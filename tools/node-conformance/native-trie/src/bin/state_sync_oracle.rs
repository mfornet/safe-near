//! Fixtures for the state sync code of the Lean node, from nearcore's own `near-store` and `zstd`
//! at the pinned revision.
//!
//! `cargo run --release --bin state-sync-oracle -- OUT_DIR` writes
//!
//! * `zstd.jsonl`: `{name, level, style, rawLength, rawSha256, raw?, frame}` for inputs of many shapes
//!   compressed with the `zstd` crate (nearcore compresses state parts with `zstd::encode_all`);
//! * `parts.jsonl`: `{case, entries, root, memoryUsage, numParts}` rows, then for each part count
//!   `{case, total, idx, nodes, additions}` (the part `get_trie_nodes_for_part_with_flat_storage`
//!   returns, and the `(hash, rc)` pairs `Trie::apply_state_part` adds) and
//!   `{case, total, idx, mutation, nodes, valid}` (a changed part and `Trie::validate_state_part`'s verdict).
//!
//! Nothing here is random: every byte comes from `mix`.

use near_crypto as _;
use near_primitives::hash::{hash, CryptoHash};
use near_primitives::shard_layout::ShardUId;
use near_primitives::state::{FlatStateValue, PartialState};
use near_primitives::state_part::PartId;
use near_store::adapter::StoreUpdateAdapter;
use near_store::flat::FlatStateChanges;
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use near_store::Trie;
use std::fmt::Write as _;
use std::io::Write as _;
use std::sync::Arc;

fn mix(x: u64) -> u64 {
    let z = x.wrapping_add(0x9E3779B97F4A7C15).wrapping_mul(0xBF58476D1CE4E5B9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

fn hex(b: &[u8]) -> String {
    let mut s = String::with_capacity(b.len() * 2);
    for x in b {
        write!(s, "{x:02x}").unwrap();
    }
    s
}

fn bytes(seed: u64, n: usize) -> Vec<u8> {
    (0..n).map(|i| mix(seed.wrapping_mul(0x1000193).wrapping_add(i as u64)) as u8).collect()
}

fn skewed(seed: u64, n: usize, alphabet: u64) -> Vec<u8> {
    (0..n).map(|i| (mix(seed.wrapping_add(i as u64)) % alphabet) as u8 + b'a').collect()
}

fn text(seed: u64, n: usize) -> Vec<u8> {
    const WORDS: [&str; 24] = [
        "account", "contract", "receipt", "trie", "node", "state", "shard", "block", "chunk", "epoch",
        "near", "gas", "balance", "storage", "function", "call", "promise", "yield", "key", "value",
        "validator", "approval", "hash", "proof",
    ];
    let mut out = Vec::new();
    let mut i = 0u64;
    while out.len() < n {
        let w = WORDS[(mix(seed + i) % WORDS.len() as u64) as usize];
        out.extend_from_slice(w.as_bytes());
        out.push(if mix(seed + i + 77) % 9 == 0 { b'\n' } else { b' ' });
        i += 1;
    }
    out.truncate(n);
    out
}

fn zstd_fixtures(out: &std::path::Path) {
    let mut cases: Vec<(String, Vec<u8>)> = vec![
        ("empty".into(), vec![]),
        ("one byte".into(), vec![42]),
        ("zeros 10k".into(), vec![0; 10_000]),
        ("zeros 300k".into(), vec![0; 300_000]),
        ("pattern".into(), (0..20_000).map(|i| (i % 251) as u8).collect()),
        ("random 5k".into(), bytes(1, 5_000)),
        ("random 200".into(), bytes(2, 200)),
        ("text 3k".into(), text(3, 3_000)),
        ("text 40k".into(), text(4, 40_000)),
        ("text 300k".into(), text(5, 300_000)),
        ("skewed 2 symbols".into(), skewed(6, 20_000, 2)),
        ("skewed 5 symbols".into(), skewed(7, 20_000, 5)),
        ("skewed 20 symbols".into(), skewed(8, 60_000, 20)),
        ("skewed 90 symbols".into(), skewed(9, 60_000, 90)),
    ];
    // hashes between repeated records: what trie nodes look like
    let mut nodes = Vec::new();
    for i in 0..400u64 {
        nodes.extend_from_slice(&[1, 0, 0, 0]);
        nodes.extend_from_slice(hash(&i.to_le_bytes()).as_ref());
        nodes.extend_from_slice(&[0u8; 8]);
        nodes.extend_from_slice(b"user");
        nodes.extend_from_slice(i.to_string().as_bytes());
        nodes.extend_from_slice(b".near");
    }
    cases.push(("trie-like".into(), nodes));
    // matches at the repeat offsets and long distances
    let mut rep = Vec::new();
    let a = bytes(10, 300);
    let b = bytes(11, 50);
    for i in 0..200u64 {
        rep.extend_from_slice(&a);
        rep.extend_from_slice(&bytes(100 + i, (mix(i) % 9) as usize));
        rep.extend_from_slice(&b);
        rep.extend_from_slice(&a[..(mix(i + 5) % 200) as usize]);
    }
    cases.push(("repeat offsets".into(), rep));
    let mut mixed = Vec::new();
    for i in 0..16u64 {
        mixed.extend_from_slice(&bytes(200 + i, 1000));
        mixed.extend_from_slice(&text(300 + i, 3000));
        mixed.extend_from_slice(&vec![i as u8; 500]);
    }
    cases.push(("mixed 70k".into(), mixed));
    let mut f = std::fs::File::create(out.join("zstd.jsonl")).unwrap();
    let levels = [-7, -3, -1, 1, 3, 5, 9, 12, 19, 22];
    let mut count = 0;
    for (n, (name, raw)) in cases.iter().enumerate() {
        // nearcore's level, and one other that changes with the case
        let other = levels[(n * 3 + 1) % levels.len()];
        let mut wanted = vec![1, other, levels[(n * 5 + 2) % levels.len()]];
        wanted.dedup();
        for level in wanted.iter() {
            for style in ["stream", "bulk", "checksum"] {
                if style != "stream" && (raw.len() > 30_000 || *level == 1) {
                    continue;
                }
                let frame = match style {
                    "stream" => zstd::encode_all(&raw[..], *level).unwrap(),
                    "bulk" => zstd::bulk::compress(raw, *level).unwrap(),
                    _ => {
                        let mut enc = zstd::stream::Encoder::new(Vec::new(), *level).unwrap();
                        enc.include_checksum(true).unwrap();
                        enc.write_all(raw).unwrap();
                        enc.finish().unwrap()
                    }
                };
                let sha: CryptoHash = hash(raw);
                let raw_field = if raw.len() <= 2048 { format!(",\"raw\":\"{}\"", hex(raw)) } else { String::new() };
                writeln!(
                    f,
                    "{{\"name\":\"{name}\",\"level\":{level},\"style\":\"{style}\",\"rawLength\":{},\"rawSha256\":\"{}\"{raw_field},\"frame\":\"{}\"}}",
                    raw.len(),
                    hex(sha.as_ref()),
                    hex(&frame)
                )
                .unwrap();
                count += 1;
            }
        }
    }
    // two frames in a row and a skippable frame between them
    let a = zstd::encode_all(&text(1, 500)[..], 1).unwrap();
    let b = zstd::encode_all(&text(2, 700)[..], 1).unwrap();
    let mut both = a.clone();
    both.extend_from_slice(&[0x50, 0x2A, 0x4D, 0x18, 3, 0, 0, 0, 9, 9, 9]);
    both.extend_from_slice(&b);
    let mut raw = text(1, 500);
    raw.extend(text(2, 700));
    writeln!(
        f,
        "{{\"name\":\"two frames and a skippable one\",\"level\":1,\"style\":\"concat\",\"rawLength\":{},\"rawSha256\":\"{}\",\"frame\":\"{}\"}}",
        raw.len(),
        hex(hash(&raw).as_ref()),
        hex(&both)
    )
    .unwrap();
    eprintln!("zstd.jsonl: {} frames", count + 1);
}

type Change = (Vec<u8>, Option<Vec<u8>>);

fn account(i: u64) -> Vec<u8> {
    format!("user{}.near", i % 97).into_bytes()
}

fn key(i: u64) -> Vec<u8> {
    let mut k = Vec::new();
    match i % 7 {
        0 => {
            k.push(0);
            k.extend(account(i));
        }
        1 => {
            k.push(2);
            k.extend(account(i));
            k.push(2);
            k.extend(bytes(i, 33));
        }
        _ => {
            k.push(9);
            k.extend(account(i));
            k.push(0x2c);
            k.extend(format!("key-{i}").into_bytes());
        }
    }
    k
}

fn cases() -> Vec<(String, Vec<(Vec<u8>, Vec<u8>)>)> {
    let mut out: Vec<(String, Vec<(Vec<u8>, Vec<u8>)>)> = Vec::new();
    out.push(("empty".into(), vec![]));
    out.push(("one entry".into(), vec![(b"a".to_vec(), vec![1, 2, 3])]));
    out.push((
        "seven entries".into(),
        (0..7).map(|i| (key(i), bytes(i, 10 + (i as usize) * 17))).collect(),
    ));
    out.push(("sixty entries".into(), (0..60).map(|i| (key(i), bytes(i, 20 + (mix(i) % 150) as usize))).collect()));
    out.push((
        "one hundred and sixty entries".into(),
        (0..160).map(|i| (key(i * 3 + 1), bytes(1000 + i, 5 + (mix(i) % 120) as usize))).collect(),
    ));
    // keys that are prefixes of each other: branches with values
    out.push((
        "prefixes".into(),
        (1..40usize).map(|n| (vec![0xffu8; n], bytes(n as u64, 30))).chain((0..30u8).map(|b| (vec![0xff, b], vec![b; 25]))).collect(),
    ));
    // big values next to small ones
    out.push((
        "big values".into(),
        vec![
            (b"a".to_vec(), bytes(1, 6000)),
            (b"aa".to_vec(), bytes(2, 9000)),
            (b"ab".to_vec(), bytes(3, 3000)),
            (b"b".to_vec(), bytes(4, 4001)),
            (b"ba".to_vec(), bytes(5, 12)),
            (b"c".to_vec(), bytes(6, 100)),
            (b"cb".to_vec(), bytes(7, 5000)),
            (b"\xfe".to_vec(), bytes(8, 7)),
        ],
    ));
    // dense: every two-nibble key
    out.push(("dense".into(), (0..=255u8).map(|b| (vec![b, b ^ 0x55], vec![b; 1 + (b % 5) as usize])).collect()));
    out
}

fn build(entries: &[(Vec<u8>, Vec<u8>)]) -> (near_store::ShardTries, ShardUId, CryptoHash) {
    let tries = TestTriesBuilder::new().with_flat_storage(true).build();
    let shard: ShardUId = near_primitives::shard_layout::ShardLayout::single_shard().shard_uids().next().unwrap();
    let trie = tries.get_trie_for_shard(shard, Trie::EMPTY_ROOT);
    let changes = trie
        .update(entries.iter().cloned().map(|(k, v)| (k, Some(v))), AccessOptions::DEFAULT)
        .unwrap();
    let mut update = tries.store_update();
    let root = tries.apply_all(&changes, shard, &mut update);
    update.commit();
    let delta = FlatStateChanges::from(
        entries.iter().cloned().map(|(k, v)| (k, Some(FlatStateValue::on_disk(&v)))),
    );
    let mut update = tries.store_update();
    delta.apply_to_flat_state(&mut update.flat_store_update(), shard);
    update.commit();
    (tries, shard, root)
}

fn rc_of(a: &near_store::trie::TrieRefcountAddition) -> u32 {
    let text = format!("{a:?}");
    let at = text.find("rc: ").expect("rc in the debug output") + 4;
    text[at..].chars().take_while(|c| c.is_ascii_digit()).collect::<String>().parse().unwrap()
}

fn nodes_of(p: &PartialState) -> Vec<Arc<[u8]>> {
    let PartialState::TrieValues(v) = p;
    v.clone()
}

fn json_nodes(nodes: &[Arc<[u8]>]) -> String {
    format!("[{}]", nodes.iter().map(|n| format!("\"{}\"", hex(n))).collect::<Vec<_>>().join(","))
}

fn parts_fixtures(out: &std::path::Path) {
    let mut f = std::fs::File::create(out.join("parts.jsonl")).unwrap();
    let block_hash = CryptoHash::default();
    let mut total_parts = 0;
    let mut mutated = 0;
    for (name, entries) in cases() {
        let (tries, shard, root) = build(&entries);
        let view = tries.get_view_trie_for_shard(shard, root);
        let memory_usage = view.retrieve_root_node().unwrap().memory_usage;
        let num_parts = near_primitives::state_sync::get_num_state_parts(memory_usage);
        writeln!(
            f,
            "{{\"case\":\"{name}\",\"root\":\"{}\",\"memoryUsage\":{memory_usage},\"numParts\":{num_parts},\"entries\":[{}]}}",
            hex(root.as_ref()),
            entries.iter().map(|(k, v)| format!("[\"{}\",\"{}\"]", hex(k), hex(v))).collect::<Vec<_>>().join(",")
        )
        .unwrap();
        let chunk_trie = tries.get_trie_with_block_hash_for_shard(shard, root, &block_hash, true);
        for total in [1u64, 2, 3, 5, 8] {
            if total == 8 && entries.len() > 100 {
                continue;
            }
            for idx in 0..total {
                let part_id = PartId::new(idx, total);
                let part = match chunk_trie.get_trie_nodes_for_part_with_flat_storage(part_id, &view) {
                    Ok(p) => p,
                    Err(e) => panic!("{name} {idx}/{total}: {e:?}"),
                };
                let verdict = Trie::validate_state_part(&root, part_id, part.clone());
                assert!(verdict.is_ok(), "{name} {idx}/{total}: {verdict:?}");
                let applied = Trie::apply_state_part(&root, part_id, part.clone());
                let mut additions: Vec<(String, u32)> = applied
                    .trie_changes
                    .insertions()
                    .iter()
                    .map(|a| (hex(a.hash().as_ref()), rc_of(a)))
                    .collect();
                additions.sort();
                writeln!(
                    f,
                    "{{\"case\":\"{name}\",\"total\":{total},\"idx\":{idx},\"nodes\":{},\"additions\":[{}]}}",
                    json_nodes(&nodes_of(&part)),
                    additions.iter().map(|(h, rc)| format!("[\"{h}\",{rc}]")).collect::<Vec<_>>().join(",")
                )
                .unwrap();
                total_parts += 1;
                // changed parts and nearcore's verdict: the part of (base_idx, base_total) in the
                // fixture, changed as `op` says, offered as part `i` of `t`. Only some parts are
                // changed, to keep the file small.
                if !(idx < 2 && total != 8) {
                    continue;
                }
                let nodes = nodes_of(&part);
                let mut variants: Vec<(String, usize, usize, u64, u64, u64, u64)> = Vec::new();
                if !nodes.is_empty() {
                    let k = (mix(idx + total) as usize) % nodes.len();
                    let p = (mix(idx * 7 + total) as usize) % nodes[k].len().max(1);
                    variants.push(("remove".into(), k, 0, idx, total, idx, total));
                    variants.push(("flip".into(), k, p, idx, total, idx, total));
                    variants.push(("repeat".into(), k, 0, idx, total, idx, total));
                    variants.push(("reverse".into(), 0, 0, idx, total, idx, total));
                }
                variants.push(("add".into(), 0, 0, idx, total, idx, total));
                variants.push(("empty".into(), 0, 0, idx, total, idx, total));
                if total > 1 {
                    variants.push(("keep".into(), 0, 0, idx, total, (idx + 1) % total, total));
                    variants.push(("keep".into(), 0, 0, idx, total, idx.min(total - 2), total - 1));
                }
                for (op, k, p, bi, bt, i, t) in variants {
                    let mut ns = nodes.clone();
                    match op.as_str() {
                        "remove" => {
                            ns.remove(k);
                        }
                        "flip" => {
                            let mut b = ns[k].to_vec();
                            if !b.is_empty() {
                                b[p] ^= 1;
                            }
                            ns[k] = Arc::from(b);
                        }
                        "repeat" => ns.push(ns[k].clone()),
                        "reverse" => ns.reverse(),
                        "add" => ns.push(Arc::from(bytes(7, 40))),
                        "empty" => ns.clear(),
                        _ => {}
                    }
                    let verdict = Trie::validate_state_part(&root, PartId::new(i, t), PartialState::TrieValues(ns));
                    writeln!(
                        f,
                        "{{\"case\":\"{name}\",\"mutation\":\"{op}\",\"k\":{k},\"p\":{p},\"baseIdx\":{bi},\"baseTotal\":{bt},\"idx\":{i},\"total\":{t},\"valid\":{}}}",
                        verdict.is_ok()
                    )
                    .unwrap();
                    mutated += 1;
                }
            }
        }
    }
    eprintln!("parts.jsonl: {total_parts} parts, {mutated} changed parts");
}

fn main() {
    let out = std::path::PathBuf::from(std::env::args().nth(1).expect("usage: state-sync-oracle OUT_DIR"));
    std::fs::create_dir_all(&out).unwrap();
    zstd_fixtures(&out);
    parts_fixtures(&out);
}
