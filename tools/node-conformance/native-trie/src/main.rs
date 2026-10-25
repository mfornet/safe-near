//! Native timings of the trie operations that `node-bench --filter trie/` measures in Lean, with
//! nearcore's own `near-store` at the pinned revision: the same keys, values and batches, an
//! in-memory `TestDB` under the trie (no RocksDB), no memtrie unless asked.
//!
//! `cargo run --release --bin native-trie-bench [-- --memtrie]` prints one JSON object per line:
//! `{"name", "nanosPerIteration"}`, with names matching `node-bench`.

use near_primitives::shard_layout::ShardUId;
use near_primitives::types::StateRoot;
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use near_store::{ShardTries, Trie};
use std::hint::black_box;
use std::time::Instant;

const TOTAL: usize = 100_000;

fn mix(x: u64) -> u64 {
    let z = x.wrapping_add(0x9E3779B97F4A7C15).wrapping_mul(0xBF58476D1CE4E5B9);
    let z = (z ^ (z >> 27)).wrapping_mul(0x94D049BB133111EB);
    z ^ (z >> 31)
}

fn account(i: usize) -> Vec<u8> {
    format!("user{i}.near").into_bytes()
}

fn key_of(i: usize) -> Vec<u8> {
    let a = account(i % 1000);
    let mut k = Vec::new();
    match i % 20 {
        0 => {
            k.push(0);
            k.extend(a);
        }
        1 => {
            k.push(2);
            k.extend(a);
            k.push(2);
            k.extend((0..33usize).map(|j| (j + i % 7) as u8));
        }
        _ => {
            k.push(9);
            k.extend(a);
            k.push(0x2c);
            k.extend(format!("key-{i}").into_bytes());
        }
    }
    k
}

fn value_of(i: usize, salt: u64) -> Vec<u8> {
    let n = 8 + (mix((i as u64).wrapping_add(salt)) % 193) as usize;
    (0..n).map(|j| (j as u64).wrapping_add(i as u64).wrapping_add(salt) as u8).collect()
}

type Change = (Vec<u8>, Option<Vec<u8>>);

fn batch(n: usize, total: usize, round: usize) -> Vec<Change> {
    (0..n)
        .map(|j| {
            let r = mix((round as u64).wrapping_mul(1000003).wrapping_add(j as u64)) as usize;
            let kind = r % 10;
            if kind < 7 {
                (key_of(r / 10 % total), Some(value_of(j, round as u64 + 1)))
            } else if kind < 9 {
                (key_of(total + round * n + j), Some(value_of(j, 7)))
            } else {
                (key_of(r / 10 % total), None)
            }
        })
        .collect()
}

fn report(name: &str, keys: usize, nanos: u128) {
    println!("{{\"name\":\"{name}\",\"nanosPerIteration\":{}}}", nanos / keys.max(1) as u128);
}

fn apply(tries: &ShardTries, shard: ShardUId, changes: &near_store::trie::TrieChanges, height: u64) -> StateRoot {
    let mut update = tries.store_update();
    tries.apply_memtrie_changes(changes, shard, height);
    let root = tries.apply_all(changes, shard, &mut update);
    update.commit();
    root
}

fn main() {
    let memtrie = std::env::args().any(|a| a == "--memtrie");
    let label = if memtrie { "memtrie " } else { "" };
    let builder = TestTriesBuilder::new();
    let tries = if memtrie {
        builder.with_flat_storage(true).with_in_memory_tries(true).build()
    } else {
        builder.build()
    };
    let shard: ShardUId = near_primitives::shard_layout::ShardLayout::single_shard().shard_uids().next().unwrap();
    let entries: Vec<Change> = (0..TOTAL).map(|i| (key_of(i), Some(value_of(i, 0)))).collect();

    let start = Instant::now();
    let trie = tries.get_trie_for_shard(shard, Trie::EMPTY_ROOT);
    let built = trie.update(entries.iter().cloned(), AccessOptions::DEFAULT).unwrap();
    let t_build = start.elapsed().as_nanos();
    report(&format!("{label}trie/build root from {TOTAL} entries"), TOTAL, t_build);

    let start = Instant::now();
    let mut root = apply(&tries, shard, &built, 1);
    report(&format!("{label}trie/apply the refcounts of {TOTAL} entries to an in-memory store"), TOTAL, start.elapsed().as_nanos());

    let mut nanos = 0u128;
    let mut keys = 0;
    for round in 0..5 {
        let b = batch(1000, TOTAL, round);
        let start = Instant::now();
        let trie = tries.get_trie_for_shard(shard, root);
        let changes = trie.update(b.iter().cloned(), AccessOptions::DEFAULT).unwrap();
        nanos += start.elapsed().as_nanos();
        keys += b.len();
        root = apply(&tries, shard, &changes, 2 + round as u64);
    }
    report(&format!("{label}trie/update, batches of 1000 writes on {TOTAL} entries"), keys, nanos);

    let trie = tries.get_trie_for_shard(shard, root);
    let n = 20_000;
    let start = Instant::now();
    let mut c = 0usize;
    for i in 0..n {
        if let Some(v) = trie.get(&key_of(i * 5 % TOTAL), AccessOptions::DEFAULT).unwrap() {
            c += v.len();
        }
    }
    black_box(c);
    report(&format!("{label}trie/get"), n, start.elapsed().as_nanos());

    let start = Instant::now();
    let mut count = 0usize;
    if let Ok(iter) = trie.disk_iter() {
        for item in iter {
            black_box(item.unwrap());
            count += 1;
        }
    }
    report(&format!("{label}trie/iterate in key order"), count, start.elapsed().as_nanos());
}
