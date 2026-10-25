//! The network oracle: fixtures for the peer protocol of `near-lean/node`, written by nearcore's own
//! `network_protocol` code at the pinned revision.
//!
//! `near-network` keeps its protocol types private, so `build.py` adds this file to the crate as the
//! module `safe_near_oracle` (and one `pub mod` line to `src/lib.rs`); the binary
//! `safe-near-network-oracle` only calls `main`.  The implementation sources are untouched.
//!
//! `safe-near-network-oracle TYPES_DIR OUT_DIR` reads the M1 Borsh fixtures in `TYPES_DIR`
//! (blocks, headers, transactions, chunk parts, endorsements, witnesses, ...) for the payloads, builds
//! every `PeerMessage` variant around them and writes to `OUT_DIR`:
//!
//! * `PeerMessage.jsonl`: protobuf bytes in `proto`, with nearcore's verdict of `PeerMessage::deserialize`:
//!   accepted lines carry `canonical` (what `PeerMessage::serialize` writes for the value, when it is not the
//!   input itself) and derived values (`maxSize`, signature checks); rejected lines carry `reject`.
//! * `<Type>.jsonl` for the Borsh types of the network protocol, in the format of the M1 fixtures.
//! * `manifest.json`: counts per type.
//!
//! The output is a pure function of the code, the locked dependencies and the input fixtures.

use crate::network_protocol::proto;
use crate::network_protocol::*;
use borsh::{BorshDeserialize, BorshSerialize};
use near_async::time;
use near_crypto::{KeyType, SecretKey, Signature};
use near_primitives::block::{Approval, Block, BlockHeader};
use near_primitives::challenge::Challenge;
use near_primitives::epoch_sync::CompressedEpochSyncProof;
use near_primitives::genesis::GenesisId;
use near_primitives::hash::CryptoHash;
use near_primitives::network::{AnnounceAccount, PeerId};
use near_primitives::optimistic_block::OptimisticBlock;
use near_primitives::sharding::{PartialEncodedChunk, PartialEncodedChunkPart, ReceiptProof};
use near_primitives::spice::chunk_endorsement::SpiceChunkEndorsement;
use near_primitives::spice::partial_data::{SpiceDataIdentifier, SpicePartialData};
use near_primitives::state_sync::{
    ShardStateSyncResponse, ShardStateSyncResponseV1, StateRequestAck,
};
use near_primitives::stateless_validation::chunk_endorsement::ChunkEndorsement;
use near_primitives::stateless_validation::contract_distribution::{
    ChunkContractAccesses, ContractCodeRequest, ContractCodeResponse, PartialEncodedContractDeploys,
    SpiceChunkContractAccesses, SpiceContractCodeRequest, SpiceContractCodeResponse,
};
use near_primitives::stateless_validation::partial_witness::{
    PartialEncodedStateWitness, VersionedPartialEncodedStateWitness,
};
use near_primitives::stateless_validation::state_witness::ChunkStateWitnessAck;
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{AccountId, EpochId, ShardId};
use near_primitives::utils::compression::CompressedData;
use near_primitives::validator_signer::InMemoryValidatorSigner;
use protobuf::Message as _;
use std::collections::{BTreeMap, HashSet};
use std::io::Write as _;
use std::path::{Path, PathBuf};
use std::sync::Arc;

// ---------------------------------------------------------------------------------------------
// plumbing

/// A small deterministic generator (SplitMix64).
struct G(u64);

impl G {
    fn new(seed: &str) -> G {
        let mut s = 0xcbf29ce484222325u64;
        for b in seed.bytes() {
            s = (s ^ b as u64).wrapping_mul(0x100000001b3);
        }
        G(s)
    }
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e3779b97f4a7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d049bb133111eb);
        z ^ (z >> 31)
    }
    fn below(&mut self, n: usize) -> usize {
        if n == 0 { 0 } else { (self.next() % n as u64) as usize }
    }
    fn bytes(&mut self, n: usize) -> Vec<u8> {
        (0..n).map(|_| self.next() as u8).collect()
    }
    fn hash(&mut self) -> CryptoHash {
        CryptoHash(self.bytes(32).try_into().unwrap())
    }
}

fn hex(b: &[u8]) -> String {
    b.iter().map(|x| format!("{x:02x}")).collect()
}

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2).map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap()).collect()
}

fn le64(n: u64) -> String {
    hex(&n.to_le_bytes())
}

/// Output files and counts.
struct Out {
    dir: PathBuf,
    files: BTreeMap<String, std::fs::File>,
    counts: BTreeMap<String, (usize, usize)>,
}

type Derived = Vec<(&'static str, String)>;

impl Out {
    fn new(dir: &Path) -> Out {
        std::fs::create_dir_all(dir).unwrap();
        Out { dir: dir.to_path_buf(), files: BTreeMap::new(), counts: BTreeMap::new() }
    }

    /// One fixture line: `key` names the input (`borsh` or `proto`); `verdict` is `None` when
    /// nearcore rejects, else the canonical re-encoding and the derived values.
    fn line(&mut self, ty: &str, name: &str, key: &str, input: &[u8], verdict: Option<(Vec<u8>, Derived)>) {
        let file = self.files.entry(ty.to_string()).or_insert_with(|| {
            std::fs::File::create(self.dir.join(format!("{ty}.jsonl"))).unwrap()
        });
        let mut s = format!("{{\"type\":\"{ty}\",\"name\":\"{name}\",\"{key}\":\"{}\"", hex(input));
        let c = self.counts.entry(ty.to_string()).or_insert((0, 0));
        match verdict {
            None => {
                s.push_str(",\"reject\":true");
                c.1 += 1;
            }
            Some((canonical, derived)) => {
                if canonical != input {
                    s.push_str(&format!(",\"canonical\":\"{}\"", hex(&canonical)));
                }
                for (k, v) in derived {
                    s.push_str(&format!(",\"{k}\":\"{v}\""));
                }
                c.0 += 1;
            }
        }
        s.push_str("}\n");
        file.write_all(s.as_bytes()).unwrap();
    }

    fn finish(self) {
        let mut types = String::new();
        for (i, (k, (a, r))) in self.counts.iter().enumerate() {
            if i > 0 {
                types.push(',');
            }
            types.push_str(&format!("\"{k}\":{{\"accept\":{a},\"reject\":{r}}}"));
        }
        let m = format!(
            "{{\"nearcore_release\":\"{}\",\"protocol_version\":{},\"types\":{{{types}}}}}\n",
            env!("CARGO_PKG_VERSION"),
            near_primitives::version::PROTOCOL_VERSION
        );
        std::fs::write(self.dir.join("manifest.json"), m).unwrap();
    }
}

/// The accepted lines of an M1 fixture file: name and Borsh bytes, at most `max_len` bytes each.
fn fixture(dir: &Path, ty: &str, max_len: usize, take: usize) -> Vec<(String, Vec<u8>)> {
    let path = dir.join(format!("{ty}.jsonl"));
    let text = std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("{}: {e}", path.display()));
    let mut out = vec![];
    for l in text.lines() {
        if l.contains("\"reject\":true") || l.contains("\"canonical\"") {
            continue;
        }
        let field = |k: &str| {
            let pat = format!("\"{k}\":\"");
            let i = l.find(&pat).map(|i| i + pat.len());
            i.map(|i| l[i..i + l[i..].find('"').unwrap()].to_string())
        };
        let (Some(name), Some(b)) = (field("name"), field("borsh")) else { continue };
        if b.len() / 2 <= max_len {
            out.push((name, unhex(&b)));
        }
    }
    // a spread over the file rather than the first lines
    let n = out.len();
    if n <= take {
        return out;
    }
    (0..take).map(|i| out[i * n / take].clone()).collect()
}

fn decode_all<T: BorshDeserialize>(items: &[(String, Vec<u8>)]) -> Vec<(String, T)> {
    items.iter().filter_map(|(n, b)| T::try_from_slice(b).ok().map(|v| (n.clone(), v))).collect()
}

fn ser<T: BorshSerialize>(v: &T) -> Vec<u8> {
    borsh::to_vec(v).unwrap()
}

// ---------------------------------------------------------------------------------------------
// keys and network values

fn sk(seed: &str) -> SecretKey {
    SecretKey::from_seed(KeyType::ED25519, seed)
}

fn peer(i: u32) -> (SecretKey, PeerId) {
    let k = sk(&format!("peer{i}"));
    let id = PeerId::new(k.public_key());
    (k, id)
}

fn socket_addr(g: &mut G) -> std::net::SocketAddr {
    if g.below(3) == 0 {
        let ip: [u16; 8] = std::array::from_fn(|_| g.next() as u16);
        std::net::SocketAddr::new(std::net::IpAddr::V6(ip.into()), g.next() as u16)
    } else {
        let ip: [u8; 4] = std::array::from_fn(|_| g.next() as u8);
        std::net::SocketAddr::new(std::net::IpAddr::V4(ip.into()), g.next() as u16)
    }
}

fn account(g: &mut G) -> AccountId {
    format!("account{}.near", g.next() % 10000).parse().unwrap()
}

fn peer_info(g: &mut G, i: u32) -> PeerInfo {
    let (_, id) = peer(i);
    let r = g.below(4);
    PeerInfo {
        id,
        addr: if r == 0 { None } else { Some(socket_addr(g)) },
        account_id: if r == 3 { None } else { Some(account(g)) },
    }
}

/// A fully signed edge between two peers; `removed` makes a removal signed by the first.
fn edge(a: u32, b: u32, nonce: u64, removed: bool) -> Edge {
    let (ska, ida) = peer(a);
    let (skb, idb) = peer(b);
    let hash = Edge::build_hash(&ida, &idb, nonce);
    let e = Edge::build_with_secret_key(ida.clone(), idb, nonce, &ska, skb.sign(hash.as_ref()));
    if removed {
        // `remove_edge` bumps the nonce, so build the added edge one below
        let hash = Edge::build_hash(&ida, &peer(b).1, nonce - 1);
        let added = Edge::build_with_secret_key(
            ida.clone(),
            peer(b).1,
            nonce - 1,
            &ska,
            skb.sign(hash.as_ref()),
        );
        added.remove_edge(ida, &ska)
    } else {
        e
    }
}

fn flip_signature(s: &Signature) -> Signature {
    let mut b = ser(s);
    let n = b.len();
    b[n / 2] ^= 1;
    Signature::try_from_slice(&b).unwrap_or_else(|_| s.clone())
}

fn announce(i: u32, epoch: CryptoHash) -> AnnounceAccount {
    let signer = InMemoryValidatorSigner::from_seed(
        format!("validator{i}.near").parse().unwrap(),
        KeyType::ED25519,
        &format!("validator{i}"),
    );
    AnnounceAccount::new(&signer, peer(i).1, EpochId(epoch))
}

fn signed_account_data(g: &mut G, i: u32, version: u64, ts: i64, proxies: usize) -> SignedAccountData {
    let signer = InMemoryValidatorSigner::from_seed(
        format!("validator{i}.near").parse().unwrap(),
        KeyType::ED25519,
        &format!("validator{i}"),
    );
    let data = VersionedAccountData {
        data: AccountData {
            peer_id: peer(i).1,
            proxies: (0..proxies)
                .map(|j| PeerAddr { addr: socket_addr(g), peer_id: peer(100 + j as u32).1 })
                .collect(),
        },
        account_key: signer.public_key(),
        version,
        timestamp: time::Utc::from_unix_timestamp(ts).unwrap(),
    };
    data.sign(&signer).unwrap()
}

fn owned_account(i: u32, ts: i64) -> SignedOwnedAccount {
    let signer = InMemoryValidatorSigner::from_seed(
        format!("validator{i}.near").parse().unwrap(),
        KeyType::ED25519,
        &format!("validator{i}"),
    );
    OwnedAccount {
        account_key: signer.public_key(),
        peer_id: peer(i).1,
        timestamp: time::Utc::from_unix_timestamp(ts).unwrap(),
    }
    .sign(&signer)
}

fn handshake(g: &mut G, sender: u32, target: u32, owned: bool, shards: usize) -> Handshake {
    let (sk_s, id_s) = peer(sender);
    let (_, id_t) = peer(target);
    Handshake {
        protocol_version: 86 - g.below(3) as u32,
        oldest_supported_version: 83,
        sender_peer_id: id_s.clone(),
        target_peer_id: id_t.clone(),
        sender_listen_port: if g.below(3) == 0 { None } else { Some(g.next() as u16 | 1) },
        sender_chain_info: PeerChainInfoV2 {
            genesis_id: GenesisId { chain_id: "localnet".to_string(), hash: g.hash() },
            height: g.next() % 1000000,
            tracked_shards: (0..shards).map(|_| ShardId::new(g.next() % 8)).collect(),
            archival: g.below(2) == 0,
        },
        partial_edge_info: PartialEdgeInfo::new(&id_s, &id_t, 1700000001 + 2 * g.below(1000) as u64, &sk_s),
        owned_account: if owned { Some(owned_account(sender, 1700000000 + g.below(100000) as i64)) } else { None },
    }
}

// ---------------------------------------------------------------------------------------------
// protobuf field-level mutation

#[derive(Clone)]
struct F {
    num: u32,
    wire: u8,
    /// varint: its raw bytes; fixed: the bytes; length-delimited: the payload
    data: Vec<u8>,
}

fn read_varint(b: &[u8], p: &mut usize) -> Option<u64> {
    let mut r = 0u64;
    for i in 0..10 {
        let x = *b.get(*p)?;
        *p += 1;
        r |= ((x & 0x7f) as u64).checked_shl(7 * i)?;
        if x < 0x80 {
            return Some(r);
        }
    }
    None
}

fn put_varint(out: &mut Vec<u8>, mut v: u64) {
    while v >= 0x80 {
        out.push((v as u8 & 0x7f) | 0x80);
        v >>= 7;
    }
    out.push(v as u8);
}

/// Splits a message into its fields; `None` unless the framing is plain (no groups).
fn parse_fields(b: &[u8]) -> Option<Vec<F>> {
    let mut p = 0;
    let mut out = vec![];
    while p < b.len() {
        let tag = read_varint(b, &mut p)?;
        let (num, wire) = ((tag >> 3) as u32, (tag & 7) as u8);
        if num == 0 {
            return None;
        }
        let data = match wire {
            0 => {
                let s = p;
                read_varint(b, &mut p)?;
                b[s..p].to_vec()
            }
            1 => {
                let d = b.get(p..p + 8)?.to_vec();
                p += 8;
                d
            }
            5 => {
                let d = b.get(p..p + 4)?.to_vec();
                p += 4;
                d
            }
            2 => {
                let n = read_varint(b, &mut p)? as usize;
                let d = b.get(p..p.checked_add(n)?)?.to_vec();
                p += n;
                d
            }
            _ => return None,
        };
        out.push(F { num, wire, data });
    }
    Some(out)
}

fn emit(fields: &[F]) -> Vec<u8> {
    let mut out = vec![];
    for f in fields {
        put_varint(&mut out, ((f.num as u64) << 3) | f.wire as u64);
        if f.wire == 2 {
            put_varint(&mut out, f.data.len() as u64);
        }
        out.extend(&f.data);
    }
    out
}

/// A field of the given wire type holding something well formed.
fn junk_field(g: &mut G, num: u32, wire: u8) -> Vec<u8> {
    let mut out = vec![];
    put_varint(&mut out, ((num as u64) << 3) | wire as u64);
    match wire {
        0 => put_varint(&mut out, g.next() >> g.below(60)),
        1 => out.extend(g.bytes(8)),
        2 => {
            let n = g.below(12);
            put_varint(&mut out, n as u64);
            out.extend(g.bytes(n));
        }
        3 => {
            // a group holding one varint field, then its end marker
            out.extend([0x08, 0x01]);
            put_varint(&mut out, ((num as u64) << 3) | 4);
        }
        4 => {}
        _ => out.extend(g.bytes(4)),
    }
    out
}

/// A varint written with extra continuation bytes.
fn padded_varint(v: u64, total: usize) -> Vec<u8> {
    let mut out = vec![];
    let mut v = v;
    for i in 0..total {
        let last = i + 1 == total;
        let low = (v & 0x7f) as u8;
        v >>= 7;
        out.push(if last { low } else { low | 0x80 });
    }
    out
}

/// Mutates the message `b` at the level of its fields, down to `depth` levels of nesting.
fn mutate_fields(g: &mut G, b: &[u8], members: &[u32], depth: usize) -> Option<Vec<u8>> {
    let mut fs = parse_fields(b)?;
    let n = fs.len();
    match g.below(13) {
        0 if n > 0 => {
            let i = g.below(n);
            let f = fs[i].clone();
            fs.insert(i, f);
        }
        1 if n > 0 => {
            fs.remove(g.below(n));
        }
        2 if n > 1 => {
            let (i, j) = (g.below(n), g.below(n));
            fs.swap(i, j);
        }
        3 => {
            let wire = [0u8, 1, 2, 5][g.below(4)];
            let num = if g.below(2) == 0 { 100 + g.below(100) as u32 } else { 1 + g.below(40) as u32 };
            let raw = junk_field(g, num, wire);
            let at = g.below(n + 1);
            let mut out = emit(&fs[..at]);
            out.extend(raw);
            out.extend(emit(&fs[at..]));
            return Some(out);
        }
        4 => {
            // a group, or a stray end marker
            let wire = [3u8, 4][g.below(2)];
            let num = 1 + g.below(30) as u32;
            let raw = junk_field(g, num, wire);
            let at = g.below(n + 1);
            let mut out = emit(&fs[..at]);
            out.extend(raw);
            out.extend(emit(&fs[at..]));
            return Some(out);
        }
        5 if n > 0 => {
            // the same number with another wire type and something well formed
            let i = g.below(n);
            let wire = [0u8, 1, 2, 5][g.below(4)];
            let raw = junk_field(g, fs[i].num, wire);
            let mut out = emit(&fs[..i]);
            out.extend(raw);
            out.extend(emit(&fs[i + 1..]));
            return Some(out);
        }
        6 if n > 0 && !members.is_empty() => {
            let i = g.below(n);
            fs[i].num = members[g.below(members.len())];
        }
        7 if n > 0 => {
            // a longer encoding of the length or the value
            let i = g.below(n);
            let mut out = emit(&fs[..i]);
            let f = &fs[i];
            let tag = ((f.num as u64) << 3) | f.wire as u64;
            let extra = 1 + g.below(5);
            if g.below(3) == 0 {
                out.extend(padded_varint(tag, 1 + extra.min(4)));
            } else {
                out.extend(padded_varint(tag, if tag < 128 { 1 } else { 2 }));
            }
            match f.wire {
                2 => {
                    let base = f.data.len() as u64;
                    let width = (if base < 128 { 1 } else if base < 16384 { 2 } else { 3 }) + extra;
                    out.extend(padded_varint(base, width.min(10)));
                    out.extend(&f.data);
                }
                0 => {
                    let mut p = 0;
                    let v = read_varint(&f.data, &mut p)?;
                    let width = f.data.len() + extra;
                    out.extend(padded_varint(v, width.min(10)));
                }
                _ => out.extend(&f.data),
            }
            out.extend(emit(&fs[i + 1..]));
            return Some(out);
        }
        8 if n > 0 => {
            // a varint field with a value that does not fit 32 bits
            let i = g.below(n);
            if fs[i].wire == 0 {
                let mut d = vec![];
                put_varint(&mut d, [u32::MAX as u64 + 1, u64::MAX, 1 << 63, 0x7fff_ffff, 0x8000_0000][g.below(5)]);
                fs[i].data = d;
            } else {
                return None;
            }
        }
        _ => {
            if depth > 0 && n > 0 {
                let i = g.below(n);
                if fs[i].wire == 2 {
                    let inner = mutate_fields(g, &fs[i].data, &[], depth - 1)?;
                    fs[i].data = inner;
                } else {
                    return None;
                }
            } else {
                return None;
            }
        }
    }
    Some(emit(&fs))
}

/// Byte-level mutations.
fn mutate_bytes(g: &mut G, b: &[u8]) -> Vec<u8> {
    let mut v = b.to_vec();
    if v.is_empty() {
        return vec![g.next() as u8];
    }
    match g.below(7) {
        0 => v.truncate(g.below(v.len())),
        1 => {
            let i = g.below(v.len());
            v[i] ^= 1 << g.below(8);
        }
        2 => {
            let i = g.below(v.len());
            v[i] = [0, 0xff, 0x80, 0x7f][g.below(4)];
        }
        3 => {
            let i = g.below(v.len() + 1);
            v.insert(i, g.next() as u8);
        }
        4 => {
            let i = g.below(v.len());
            v.remove(i);
        }
        5 => v.push(g.next() as u8),
        _ => {
            let n = g.below(v.len() + 1);
            v.truncate(n);
            let n = 1 + g.below(3);
            v.extend(g.bytes(n));
        }
    }
    v
}

// ---------------------------------------------------------------------------------------------
// families

/// A Borsh type with its bases and mutations.
fn borsh_family<T: BorshSerialize + BorshDeserialize>(
    out: &mut Out,
    ty: &str,
    bases: Vec<(String, Vec<u8>)>,
    mutations: usize,
    derive: impl Fn(&T) -> Derived,
) {
    let mut g = G::new(ty);
    let mut seen = HashSet::new();
    for (name, b) in bases {
        let mut inputs = vec![(name.clone(), b.clone())];
        for k in 0..mutations {
            inputs.push((format!("{name}/m{k}"), mutate_bytes(&mut g, &b)));
        }
        for (n, bytes) in inputs {
            if !seen.insert(bytes.clone()) {
                continue;
            }
            match T::try_from_slice(&bytes) {
                Ok(v) => {
                    let canonical = ser(&v);
                    out.line(ty, &n, "borsh", &bytes, Some((canonical, derive(&v))));
                }
                Err(_) => out.line(ty, &n, "borsh", &bytes, None),
            }
        }
    }
}

fn peer_message_bytes(m: &PeerMessage) -> Vec<u8> {
    proto::PeerMessage::from(m).write_to_bytes().unwrap()
}

fn handshake_derived(h: &Handshake) -> Derived {
    let partial = Edge::partial_verify(&h.target_peer_id, &h.sender_peer_id, &h.partial_edge_info);
    let owned = match &h.owned_account {
        None => 2u8,
        Some(o) => o.payload().verify(&o.account_key).is_ok() as u8,
    };
    vec![("partialEdgeOk", hex(&[partial as u8])), ("ownedOk", hex(&[owned]))]
}

fn derived_of(m: &PeerMessage) -> Derived {
    let mut d: Derived = vec![("maxSize", le64(m.max_size() as u64))];
    match m {
        PeerMessage::Tier1Handshake(h) | PeerMessage::Tier2Handshake(h) | PeerMessage::Tier3Handshake(h) => {
            d.extend(handshake_derived(h))
        }
        PeerMessage::SyncRoutingTable(u) => {
            d.push(("edgesOk", hex(&u.edges.iter().map(|e| e.verify() as u8).collect::<Vec<_>>())))
        }
        PeerMessage::LastEdge(e) => d.push(("edgesOk", hex(&[e.verify() as u8]))),
        PeerMessage::SyncAccountsData(s) => d.push((
            "accountsOk",
            hex(&s
                .accounts_data
                .iter()
                .map(|a| a.payload().verify(&a.account_key).is_ok() as u8)
                .collect::<Vec<_>>()),
        )),
        PeerMessage::Routed(r) => {
            d.push(("routedHash", hex(&r.hash().0)));
            d.push(("routedVerify", hex(&[r.verify() as u8])));
        }
        _ => {}
    }
    d
}

/// Decodes the bytes as nearcore does; the canonical re-encoding and derived values on success.
fn peer_verdict(bytes: &[u8]) -> Option<(Vec<u8>, Derived)> {
    let m = PeerMessage::deserialize(bytes).ok()?;
    Some((peer_message_bytes(&m), derived_of(&m)))
}

fn peer_family(
    out: &mut Out,
    g: &mut G,
    bases: Vec<(String, PeerMessage)>,
    byte_mutations: usize,
    field_mutations: usize,
) {
    let mut seen = HashSet::new();
    let members: Vec<u32> = vec![
        4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37,
    ];
    for (name, m) in bases {
        let base = peer_message_bytes(&m);
        let mut inputs = vec![(name.clone(), base.clone())];
        let big = base.len() > 4000;
        for k in 0..byte_mutations.min(if big { 2 } else { 1000 }) {
            inputs.push((format!("{name}/b{k}"), mutate_bytes(g, &base)));
        }
        for k in 0..field_mutations.min(if big { 3 } else { 1000 }) {
            let mut b = base.clone();
            let mut ok = true;
            for _ in 0..1 + g.below(2) {
                match mutate_fields(g, &b, &members, 2) {
                    Some(x) => b = x,
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            if ok {
                inputs.push((format!("{name}/f{k}"), b));
            }
        }
        for (n, bytes) in inputs {
            if !seen.insert(bytes.clone()) {
                continue;
            }
            out.line("PeerMessage", &n, "proto", &bytes, peer_verdict(&bytes));
        }
    }
}

// ---------------------------------------------------------------------------------------------

pub fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 3 || args.len() > 6 {
        panic!("usage: safe-near-network-oracle TYPES_DIR OUT_DIR [BYTE_MUTATIONS FIELD_MUTATIONS [SEED]]");
    }
    let (types_dir, out_dir) = (&args[1], &args[2]);
    let byte_mutations: usize = args.get(3).map_or(6, |a| a.parse().unwrap());
    let field_mutations: usize = args.get(4).map_or(14, |a| a.parse().unwrap());
    let seed = args.get(5).cloned().unwrap_or_default();
    assert_eq!(near_primitives::version::PROTOCOL_VERSION, 86, "the oracle is for protocol 86");
    let types = Path::new(types_dir);
    let mut out = Out::new(Path::new(out_dir));
    let mut g = G::new(&format!("network-oracle{seed}"));

    // ---- payloads from the M1 fixtures
    let blocks: Vec<(String, Arc<Block>)> = decode_all::<Block>(&fixture(types, "Block", 60000, 6))
        .into_iter()
        .map(|(n, b)| (n, Arc::new(b)))
        .collect();
    let headers: Vec<(String, Arc<BlockHeader>)> =
        decode_all::<BlockHeader>(&fixture(types, "BlockHeader", 6000, 9))
            .into_iter()
            .map(|(n, b)| (n, Arc::new(b)))
            .collect();
    let txs = decode_all::<SignedTransaction>(&fixture(types, "SignedTransaction", 3000, 6));
    let challenges = decode_all::<Challenge>(&fixture(types, "Challenge", 3000, 3));
    let approvals = decode_all::<Approval>(&fixture(types, "Approval", 1000, 4));
    let endorsements = decode_all::<ChunkEndorsement>(&fixture(types, "ChunkEndorsement", 3000, 3));
    let chunks = decode_all::<PartialEncodedChunk>(&fixture(types, "PartialEncodedChunk", 20000, 3));
    let parts = decode_all::<PartialEncodedChunkPart>(&fixture(types, "PartialEncodedChunkPart", 3000, 3));
    let receipt_proofs = decode_all::<ReceiptProof>(&fixture(types, "ReceiptProof", 3000, 3));
    let acks = decode_all::<ChunkStateWitnessAck>(&fixture(types, "ChunkStateWitnessAck", 1000, 2));
    let pws = decode_all::<PartialEncodedStateWitness>(&fixture(types, "PartialEncodedStateWitness", 8000, 2));
    let vpws =
        decode_all::<VersionedPartialEncodedStateWitness>(&fixture(types, "VersionedPartialEncodedStateWitness", 8000, 2));
    let accesses = decode_all::<ChunkContractAccesses>(&fixture(types, "ChunkContractAccesses", 3000, 2));
    let code_requests = decode_all::<ContractCodeRequest>(&fixture(types, "ContractCodeRequest", 3000, 2));
    let code_responses = decode_all::<ContractCodeResponse>(&fixture(types, "ContractCodeResponse", 3000, 2));
    let deploys =
        decode_all::<PartialEncodedContractDeploys>(&fixture(types, "PartialEncodedContractDeploys", 6000, 2));
    let spice_data = decode_all::<SpicePartialData>(&fixture(types, "SpicePartialData", 6000, 2));
    let spice_endorsements = decode_all::<SpiceChunkEndorsement>(&fixture(types, "SpiceChunkEndorsement", 3000, 2));
    let spice_ids = decode_all::<SpiceDataIdentifier>(&fixture(types, "SpiceDataIdentifier", 300, 3));
    let spice_accesses =
        decode_all::<SpiceChunkContractAccesses>(&fixture(types, "SpiceChunkContractAccesses", 3000, 2));
    let spice_code_requests =
        decode_all::<SpiceContractCodeRequest>(&fixture(types, "SpiceContractCodeRequest", 3000, 2));
    let spice_code_responses =
        decode_all::<SpiceContractCodeResponse>(&fixture(types, "SpiceContractCodeResponse", 3000, 2));
    let state_acks = decode_all::<StateRequestAck>(&fixture(types, "StateRequestAck", 500, 3));
    let responses_v1 = decode_all::<ShardStateSyncResponseV1>(&fixture(types, "ShardStateSyncResponseV1", 20000, 2));
    let responses = decode_all::<ShardStateSyncResponse>(&fixture(types, "ShardStateSyncResponse", 20000, 4));
    let optimistic = decode_all::<OptimisticBlock>(&fixture(types, "OptimisticBlock", 2000, 3));
    let epoch_proofs = [g.bytes(0), g.bytes(40), g.bytes(3000)];

    let (node_sk, node_id) = peer(1);
    let target_id = peer(2).1;

    // ---- Borsh types of the network
    let mut addrs = vec![];
    for i in 0..10 {
        addrs.push((format!("addr-{i}"), ser(&socket_addr(&mut g))));
    }
    borsh_family::<std::net::SocketAddr>(&mut out, "SocketAddr", addrs, 4, |_| vec![]);

    let infos: Vec<_> = (0..8).map(|i| (format!("info-{i}"), ser(&peer_info(&mut g, i)))).collect();
    borsh_family::<PeerInfo>(&mut out, "PeerInfo", infos, 5, |_| vec![]);

    let partials: Vec<_> = (0..4)
        .map(|i| {
            let (s, a) = peer(i);
            (format!("partial-{i}"), ser(&PartialEdgeInfo::new(&a, &peer(i + 1).1, 1700000001 + i as u64 * 2, &s)))
        })
        .collect();
    borsh_family::<PartialEdgeInfo>(&mut out, "PartialEdgeInfo", partials, 4, |_| vec![]);

    let mut edges = vec![];
    for i in 0..6u32 {
        edges.push((format!("added-{i}"), edge(i, i + 7, 1700000001 + 2 * i as u64, false)));
        edges.push((format!("removed-{i}"), edge(i, i + 7, 1700000002 + 2 * i as u64, true)));
    }
    let mut bad = edge(3, 4, 1700000001, false);
    bad = Edge::new(bad.key().0.clone(), bad.key().1.clone(), bad.nonce(), flip_signature(bad.signature0()), bad.signature1().clone());
    edges.push(("bad-signature".to_string(), bad));
    edges.push(("fake".to_string(), Edge::make_fake_edge(peer(5).1, peer(6).1, 7)));
    let edge_bases = edges.iter().map(|(n, e)| (n.clone(), ser(e))).collect();
    borsh_family::<Edge>(&mut out, "Edge", edge_bases, 6, |e| {
        vec![
            ("hash", hex(&e.hash().0)),
            ("verify", hex(&[e.verify() as u8])),
            ("next", le64(e.next())),
        ]
    });

    // ---- routed bodies
    let mut bodies: Vec<(String, RoutedMessageBody)> = vec![];
    for (n, a) in &approvals {
        bodies.push((format!("approval-{n}"), RoutedMessageBody::BlockApproval(a.clone())));
    }
    for (n, t) in &txs {
        bodies.push((format!("tx-{n}"), RoutedMessageBody::ForwardTx(t.clone())));
    }
    for i in 0..3 {
        bodies.push((format!("tx-status-{i}"), RoutedMessageBody::TxStatusRequest(account(&mut g), g.hash())));
    }
    for i in 0..4 {
        bodies.push((
            format!("chunk-request-{i}"),
            RoutedMessageBody::PartialEncodedChunkRequest(PartialEncodedChunkRequestMsg {
                chunk_hash: near_primitives::sharding::ChunkHash(g.hash()),
                part_ords: (0..i).map(|_| g.next() % 100).collect(),
                tracking_shards: (0..i).map(|_| ShardId::new(g.next() % 6)).collect(),
            }),
        ));
    }
    for (i, (n, p)) in parts.iter().enumerate() {
        bodies.push((
            format!("chunk-response-{n}"),
            RoutedMessageBody::PartialEncodedChunkResponse(PartialEncodedChunkResponseMsg {
                chunk_hash: near_primitives::sharding::ChunkHash(g.hash()),
                parts: vec![p.clone()],
                receipts: receipt_proofs.iter().take(i).map(|(_, r)| r.clone()).collect(),
            }),
        ));
        bodies.push((
            format!("chunk-forward-{n}"),
            RoutedMessageBody::PartialEncodedChunkForward(PartialEncodedChunkForwardMsg {
                chunk_hash: near_primitives::sharding::ChunkHash(g.hash()),
                inner_header_hash: g.hash(),
                merkle_root: g.hash(),
                signature: sk("forward").sign(b"forward"),
                prev_block_hash: g.hash(),
                height_created: g.next() % 1000,
                shard_id: ShardId::new(g.next() % 4),
                parts: vec![p.clone()],
            }),
        ));
    }
    bodies.push(("ping".to_string(), RoutedMessageBody::Ping(Ping { nonce: 7, source: node_id.clone() })));
    bodies.push(("pong".to_string(), RoutedMessageBody::Pong(Pong { nonce: 8, source: target_id.clone() })));
    for (n, c) in &chunks {
        bodies.push((format!("chunk-{n}"), RoutedMessageBody::VersionedPartialEncodedChunk(c.clone())));
    }
    for (n, a) in &acks {
        bodies.push((format!("witness-ack-{n}"), RoutedMessageBody::ChunkStateWitnessAck(a.clone())));
    }
    for (n, w) in &pws {
        bodies.push((format!("witness-{n}"), RoutedMessageBody::PartialEncodedStateWitness(w.clone())));
        bodies.push((format!("witness-fwd-{n}"), RoutedMessageBody::PartialEncodedStateWitnessForward(w.clone())));
    }
    for (n, e) in &endorsements {
        bodies.push((format!("endorsement-{n}"), RoutedMessageBody::VersionedChunkEndorsement(e.clone())));
    }
    for i in 0..2 {
        bodies.push((
            format!("state-part-request-{i}"),
            RoutedMessageBody::StatePartRequest(StatePartRequest {
                shard_id: ShardId::new(i),
                sync_hash: g.hash(),
                part_id: g.next() % 50,
                addr: socket_addr(&mut g),
            }),
        ));
        bodies.push((
            format!("state-header-request-{i}"),
            RoutedMessageBody::StateHeaderRequest(StateHeaderRequest {
                shard_id: ShardId::new(i),
                sync_hash: g.hash(),
                addr: socket_addr(&mut g),
            }),
        ));
    }
    for (n, a) in &accesses {
        bodies.push((format!("accesses-{n}"), RoutedMessageBody::ChunkContractAccesses(a.clone())));
    }
    for (n, a) in &code_requests {
        bodies.push((format!("code-request-{n}"), RoutedMessageBody::ContractCodeRequest(a.clone())));
    }
    for (n, a) in &code_responses {
        bodies.push((format!("code-response-{n}"), RoutedMessageBody::ContractCodeResponse(a.clone())));
    }
    for (n, a) in &deploys {
        bodies.push((format!("deploys-{n}"), RoutedMessageBody::PartialEncodedContractDeploys(a.clone())));
    }
    for (n, a) in &spice_data {
        bodies.push((format!("spice-data-{n}"), RoutedMessageBody::SpicePartialData(a.clone())));
    }
    for (n, a) in &state_acks {
        bodies.push((format!("state-ack-{n}"), RoutedMessageBody::StateRequestAck(a.clone())));
    }
    for (n, a) in &spice_endorsements {
        bodies.push((format!("spice-endorsement-{n}"), RoutedMessageBody::SpiceChunkEndorsement(a.clone())));
    }
    for (n, id) in &spice_ids {
        bodies.push((
            format!("spice-request-{n}"),
            RoutedMessageBody::SpicePartialDataRequest(crate::spice::data_distribution::SpicePartialDataRequest {
                data_id: id.clone(),
                requester: account(&mut g),
            }),
        ));
    }
    for (n, a) in &spice_accesses {
        bodies.push((format!("spice-accesses-{n}"), RoutedMessageBody::SpiceChunkContractAccesses(a.clone())));
    }
    for (n, a) in &spice_code_requests {
        bodies.push((format!("spice-code-request-{n}"), RoutedMessageBody::SpiceContractCodeRequest(a.clone())));
    }
    for (n, a) in &spice_code_responses {
        bodies.push((format!("spice-code-response-{n}"), RoutedMessageBody::SpiceContractCodeResponse(a.clone())));
    }
    for (n, w) in &vpws {
        bodies.push((format!("vwitness-{n}"), RoutedMessageBody::VersionedPartialEncodedStateWitness(w.clone())));
        bodies.push((
            format!("vwitness-fwd-{n}"),
            RoutedMessageBody::VersionedPartialEncodedStateWitnessForward(w.clone()),
        ));
    }

    // RoutedBody (V1 tags), TieredMessageBody and RoutedMessageV1
    let body_bases: Vec<_> = bodies.iter().map(|(n, b)| (n.clone(), ser(b))).collect();
    borsh_family::<RoutedMessageBody>(&mut out, "RoutedBody", body_bases, 3, |b| {
        let t = TieredMessageBody::from_routed(b.clone());
        vec![("tiered", hex(&ser(&t))), ("isT1", hex(&[t.is_t1() as u8]))]
    });
    let tiered_bases: Vec<_> =
        bodies.iter().map(|(n, b)| (n.clone(), ser(&TieredMessageBody::from_routed(b.clone())))).collect();
    borsh_family::<TieredMessageBody>(&mut out, "TieredBody", tiered_bases, 3, |t| {
        vec![("routed", hex(&ser(&RoutedMessageBody::from(t.clone()))))]
    });
    let routed_v1: Vec<_> = bodies
        .iter()
        .enumerate()
        .map(|(i, (n, b))| {
            let target = if i % 3 == 0 { PeerIdOrHash::Hash(g.hash()) } else { PeerIdOrHash::PeerId(target_id.clone()) };
            let m = RawRoutedMessage { target, body: TieredMessageBody::from_routed(b.clone()) }.sign(
                &node_sk,
                1 + (i % 100) as u8,
                Some(time::Utc::from_unix_timestamp(1700000000 + i as i64).unwrap()),
            );
            (n.clone(), ser(&m.msg_v1()))
        })
        .collect();
    borsh_family::<RoutedMessageV1>(&mut out, "RoutedMessageV1", routed_v1, 2, |m| {
        vec![("hash", hex(&m.hash().0)), ("verify", hex(&[m.verify() as u8]))]
    });

    // the request and response messages
    let req_bases: Vec<_> = bodies
        .iter()
        .filter_map(|(n, b)| match b {
            RoutedMessageBody::PartialEncodedChunkRequest(m) => Some((n.clone(), ser(m))),
            _ => None,
        })
        .collect();
    borsh_family::<PartialEncodedChunkRequestMsg>(&mut out, "PartialEncodedChunkRequestMsg", req_bases, 6, |_| vec![]);
    let resp_bases: Vec<_> = bodies
        .iter()
        .filter_map(|(n, b)| match b {
            RoutedMessageBody::PartialEncodedChunkResponse(m) => Some((n.clone(), ser(m))),
            _ => None,
        })
        .collect();
    borsh_family::<PartialEncodedChunkResponseMsg>(&mut out, "PartialEncodedChunkResponseMsg", resp_bases, 4, |_| vec![]);
    let fwd_bases: Vec<_> = bodies
        .iter()
        .filter_map(|(n, b)| match b {
            RoutedMessageBody::PartialEncodedChunkForward(m) => Some((n.clone(), ser(m))),
            _ => None,
        })
        .collect();
    borsh_family::<PartialEncodedChunkForwardMsg>(&mut out, "PartialEncodedChunkForwardMsg", fwd_bases, 4, |m| {
        vec![("validHash", hex(&[m.is_valid_hash() as u8]))]
    });
    let sh: Vec<_> = (0..4)
        .map(|i| {
            (
                format!("state-header-{i}"),
                ser(&StateHeaderRequest { shard_id: ShardId::new(i), sync_hash: g.hash(), addr: socket_addr(&mut g) }),
            )
        })
        .collect();
    borsh_family::<StateHeaderRequest>(&mut out, "StateHeaderRequest", sh, 4, |_| vec![]);
    let sp: Vec<_> = (0..4)
        .map(|i| {
            (
                format!("state-part-{i}"),
                ser(&StatePartRequest {
                    shard_id: ShardId::new(i),
                    sync_hash: g.hash(),
                    part_id: g.next() % 40,
                    addr: socket_addr(&mut g),
                }),
            )
        })
        .collect();
    borsh_family::<StatePartRequest>(&mut out, "StatePartRequest", sp, 4, |_| vec![]);
    let spr: Vec<_> = bodies
        .iter()
        .filter_map(|(n, b)| match b {
            RoutedMessageBody::SpicePartialDataRequest(m) => Some((n.clone(), ser(m))),
            _ => None,
        })
        .collect();
    borsh_family::<crate::spice::data_distribution::SpicePartialDataRequest>(
        &mut out,
        "SpicePartialDataRequest",
        spr,
        4,
        |_| vec![],
    );
    let mut infos_state: Vec<(String, StateResponseInfo)> = vec![];
    for (n, r) in &responses_v1 {
        infos_state.push((
            format!("v1-{n}"),
            StateResponseInfo::V1(Box::new(StateResponseInfoV1 {
                shard_id: ShardId::new(1),
                sync_hash: g.hash(),
                state_response: r.clone(),
            })),
        ));
    }
    for (n, r) in &responses {
        infos_state.push((
            format!("v2-{n}"),
            StateResponseInfo::V2(Box::new(StateResponseInfoV2 {
                shard_id: ShardId::new(2),
                sync_hash: g.hash(),
                state_response: r.clone(),
            })),
        ));
    }
    let info_bases: Vec<_> = infos_state.iter().map(|(n, i)| (n.clone(), ser(i))).collect();
    borsh_family::<StateResponseInfo>(&mut out, "StateResponseInfo", info_bases, 3, |_| vec![]);

    // ---- PeerMessage
    let mut msgs: Vec<(String, PeerMessage)> = vec![];
    for (i, (shards, owned)) in [(0, false), (3, false), (0, true), (128, true), (5, true)].into_iter().enumerate() {
        let h = handshake(&mut g, 1, 2, owned, shards);
        msgs.push((format!("tier2-handshake-{i}"), PeerMessage::Tier2Handshake(h.clone())));
        msgs.push((format!("tier1-handshake-{i}"), PeerMessage::Tier1Handshake(h.clone())));
        msgs.push((format!("tier3-handshake-{i}"), PeerMessage::Tier3Handshake(h)));
    }
    // a handshake with a bad edge signature, and a bad owned-account signature
    {
        let mut h = handshake(&mut g, 3, 4, true, 1);
        h.partial_edge_info.signature = flip_signature(&h.partial_edge_info.signature);
        msgs.push(("handshake-bad-edge".to_string(), PeerMessage::Tier2Handshake(h)));
        let mut h = handshake(&mut g, 3, 4, true, 1);
        let o = h.owned_account.take().unwrap();
        h.owned_account = Some(
            OwnedAccount { account_key: o.account_key.clone(), peer_id: peer(9).1, timestamp: o.timestamp }
                .sign(&InMemoryValidatorSigner::from_seed(
                    "validator3.near".parse().unwrap(),
                    KeyType::ED25519,
                    "validator3",
                )),
        );
        msgs.push(("handshake-other-owner".to_string(), PeerMessage::Tier2Handshake(h)));
    }
    for i in 0..3 {
        let info = peer_info(&mut g, i);
        msgs.push((
            format!("failure-version-{i}"),
            PeerMessage::HandshakeFailure(
                info.clone(),
                HandshakeFailureReason::ProtocolVersionMismatch { version: 80 + i, oldest_supported_version: 70 },
            ),
        ));
        msgs.push((
            format!("failure-genesis-{i}"),
            PeerMessage::HandshakeFailure(
                info.clone(),
                HandshakeFailureReason::GenesisMismatch(GenesisId { chain_id: format!("chain{i}"), hash: g.hash() }),
            ),
        ));
        msgs.push((
            format!("failure-target-{i}"),
            PeerMessage::HandshakeFailure(info, HandshakeFailureReason::InvalidTarget),
        ));
    }
    for (i, (n, e)) in edges.iter().enumerate() {
        msgs.push((format!("last-edge-{n}"), PeerMessage::LastEdge(e.clone())));
        if i % 3 == 0 {
            msgs.push((
                format!("routing-update-{n}"),
                PeerMessage::SyncRoutingTable(RoutingTableUpdate::new(
                    edges.iter().take(i % 5).map(|(_, e)| e.clone()).collect(),
                    (0..(i % 3) as u32).map(|k| announce(k, g.hash())).collect(),
                )),
            ));
        }
    }
    msgs.push(("routing-empty".to_string(), PeerMessage::SyncRoutingTable(RoutingTableUpdate::new(vec![], vec![]))));
    for i in 0..3u32 {
        let (s, a) = peer(i);
        msgs.push((
            format!("update-nonce-{i}"),
            PeerMessage::RequestUpdateNonce(PartialEdgeInfo::new(&a, &peer(9).1, 1700000001 + 2 * i as u64, &s)),
        ));
    }
    for (i, (inc, req, n)) in [(true, false, 0), (false, true, 0), (false, false, 2), (true, false, 3)].into_iter().enumerate() {
        let data = (0..n).map(|k| Arc::new(signed_account_data(&mut g, k + 1, 1 + k as u64, 1700000000 + k as i64, k as usize))).collect();
        msgs.push((
            format!("accounts-data-{i}"),
            PeerMessage::SyncAccountsData(SyncAccountsData { accounts_data: data, incremental: inc, requesting_full_sync: req }),
        ));
    }
    for (i, (a, b)) in [(None, None), (Some(5), None), (None, Some(7)), (Some(0), Some(u32::MAX)), (Some(100), Some(10))]
        .into_iter()
        .enumerate()
    {
        msgs.push((format!("peers-request-{i}"), PeerMessage::PeersRequest(PeersRequest { max_peers: a, max_direct_peers: b })));
    }
    for i in 0..4 {
        msgs.push((
            format!("peers-response-{i}"),
            PeerMessage::PeersResponse(PeersResponse {
                peers: (0..i).map(|k| peer_info(&mut g, 20 + k)).collect(),
                direct_peers: (0..(3 - i).max(0)).map(|k| peer_info(&mut g, 30 + k)).collect(),
            }),
        ));
    }
    for i in 0..4 {
        msgs.push((
            format!("headers-request-{i}"),
            PeerMessage::BlockHeadersRequest((0..i * 3).map(|_| g.hash()).collect()),
        ));
    }
    msgs.push(("headers-0".to_string(), PeerMessage::BlockHeaders(vec![])));
    for (i, chunk) in headers.chunks(3).enumerate() {
        msgs.push((
            format!("headers-{}", i + 1),
            PeerMessage::BlockHeaders(chunk.iter().map(|(_, h)| h.clone()).collect()),
        ));
    }
    for i in 0..3 {
        msgs.push((format!("block-request-{i}"), PeerMessage::BlockRequest(g.hash())));
    }
    for (n, b) in &blocks {
        msgs.push((format!("block-{n}"), PeerMessage::Block(b.clone())));
    }
    for (n, o) in &optimistic {
        msgs.push((format!("optimistic-{n}"), PeerMessage::OptimisticBlock(o.clone())));
    }
    for (n, t) in &txs {
        msgs.push((format!("transaction-{n}"), PeerMessage::Transaction(t.clone())));
    }
    for (n, c) in &challenges {
        msgs.push((format!("challenge-{n}"), PeerMessage::Challenge(Box::new(c.clone()))));
    }
    for (i, (n, b)) in bodies.iter().enumerate() {
        let target = if i % 4 == 0 { PeerIdOrHash::Hash(g.hash()) } else { PeerIdOrHash::PeerId(target_id.clone()) };
        let now = if i % 5 == 0 { None } else { Some(time::Utc::from_unix_timestamp(1700000000 + i as i64).unwrap()) };
        let m = RawRoutedMessage { target, body: TieredMessageBody::from_routed(b.clone()) }
            .sign(&node_sk, 1 + (i % 100) as u8, now);
        msgs.push((format!("routed-{n}"), PeerMessage::Routed(Box::new(m))));
    }
    for r in [false, true] {
        msgs.push((format!("disconnect-{r}"), PeerMessage::Disconnect(Disconnect { remove_from_connection_store: r })));
    }
    for i in 0..3u32 {
        let hosts = (0..i)
            .map(|k| {
                let (s, p) = peer(40 + k);
                Arc::new(SnapshotHostInfo::new(p, g.hash(), 10 + k as u64, (0..k as u64 * 3).map(ShardId::new).collect(), &s))
            })
            .collect();
        msgs.push((format!("snapshot-hosts-{i}"), PeerMessage::SyncSnapshotHosts(SyncSnapshotHosts { hosts })));
    }
    for i in 0..3 {
        msgs.push((format!("state-request-header-{i}"), PeerMessage::StateRequestHeader(ShardId::new(i), g.hash())));
        msgs.push((
            format!("state-request-part-{i}"),
            PeerMessage::StateRequestPart(ShardId::new(i), g.hash(), g.next() % 100),
        ));
    }
    for (n, i) in &infos_state {
        msgs.push((format!("state-response-{n}"), PeerMessage::VersionedStateResponse(i.clone())));
    }
    msgs.push(("epoch-sync-request".to_string(), PeerMessage::EpochSyncRequest));
    for (i, p) in epoch_proofs.iter().enumerate() {
        msgs.push((
            format!("epoch-sync-response-{i}"),
            PeerMessage::EpochSyncResponse(CompressedEpochSyncProof::from_boxed_slice(p.clone().into_boxed_slice())),
        ));
    }

    // hand-built proto messages: the V3 routed message, trace contexts, and shapes `serialize` never writes
    let mut extra: Vec<(String, Vec<u8>)> = vec![];
    for (i, (n, b)) in bodies.iter().enumerate().step_by(3) {
        let target = if i % 2 == 0 { PeerIdOrHash::Hash(g.hash()) } else { PeerIdOrHash::PeerId(target_id.clone()) };
        let tiered = TieredMessageBody::from_routed(b.clone());
        let signed = RawRoutedMessage { target: target.clone(), body: tiered.clone() }.sign(&node_sk, 5, None);
        let mut v3 = proto::RoutedMessageV3::new();
        v3.target = protobuf::MessageField::some((&target).into());
        v3.author = protobuf::MessageField::some((&node_id).into());
        v3.ttl = 1 + (i % 200) as u32;
        v3.borsh_body = ser(&tiered);
        if i % 4 != 3 {
            v3.signature = protobuf::MessageField::some(signed.signature().unwrap().into());
        }
        if i % 2 == 0 {
            v3.created_at = Some(1700000000 + i as i64);
        }
        v3.num_hops = (i % 7) as u32;
        let mut pm = proto::PeerMessage::new();
        pm.message_type = Some(proto::peer_message::Message_type::RoutedV3(v3));
        extra.push((format!("routed-v3-{n}"), pm.write_to_bytes().unwrap()));
    }
    {
        // a trace context beside the message (as nearcore writes it when a span is sampled)
        let base = peer_message_bytes(&PeerMessage::PeersRequest(PeersRequest { max_peers: Some(3), max_direct_peers: None }));
        let mut tc = proto::TraceContext::new();
        tc.trace_id = vec![1; 16];
        tc.span_id = vec![2; 8];
        tc.sampling_priority = protobuf::EnumOrUnknown::from_i32(3);
        let mut pm = proto::PeerMessage::parse_from_bytes(&base).unwrap();
        pm.trace_context = protobuf::MessageField::some(tc.clone());
        extra.push(("trace-context".to_string(), pm.write_to_bytes().unwrap()));
        tc.sampling_priority = protobuf::EnumOrUnknown::from_i32(99);
        pm.trace_context = protobuf::MessageField::some(tc);
        extra.push(("trace-context-unknown-priority".to_string(), pm.write_to_bytes().unwrap()));
    }
    {
        // update-nonce response, which parses as a routing table update
        let e = edge(1, 2, 1700000001, false);
        let mut r = proto::UpdateNonceResponse::new();
        r.edge = protobuf::MessageField::some((&e).into());
        let mut pm = proto::PeerMessage::new();
        pm.message_type = Some(proto::peer_message::Message_type::UpdateNonceResponse(r));
        extra.push(("update-nonce-response".to_string(), pm.write_to_bytes().unwrap()));
    }
    {
        // empty and nearly empty messages
        extra.push(("empty".to_string(), vec![]));
        for tag in [4u8, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 25, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37] {
            let mut b = vec![];
            put_varint(&mut b, ((tag as u64) << 3) | 2);
            b.push(0);
            extra.push((format!("member-{tag}-empty"), b));
        }
    }
    {
        // limits of the timestamp, ports, shard lists and nanos
        let h = handshake(&mut g, 1, 2, false, 0);
        let base = peer_message_bytes(&PeerMessage::Tier2Handshake(h));
        let pm = proto::PeerMessage::parse_from_bytes(&base).unwrap();
        let proto::peer_message::Message_type::Tier2Handshake(hs) = pm.message_type.clone().unwrap() else { unreachable!() };
        for (k, port) in [0u32, 1, 65535, 65536, 70000, u32::MAX].into_iter().enumerate() {
            let mut hs = hs.clone();
            hs.sender_listen_port = port;
            let mut pm = proto::PeerMessage::new();
            pm.message_type = Some(proto::peer_message::Message_type::Tier2Handshake(hs));
            extra.push((format!("handshake-port-{k}"), pm.write_to_bytes().unwrap()));
        }
        for (k, n) in [127usize, 128, 129, 200].into_iter().enumerate() {
            let mut hs = hs.clone();
            hs.sender_chain_info.as_mut().unwrap().tracked_shards = (0..n as u64).collect();
            let mut pm = proto::PeerMessage::new();
            pm.message_type = Some(proto::peer_message::Message_type::Tier2Handshake(hs));
            extra.push((format!("handshake-shards-{k}"), pm.write_to_bytes().unwrap()));
        }
        let signed = signed_account_data(&mut g, 1, 1, 0, 1);
        let owned = owned_account(1, 0);
        for (k, (secs, nanos)) in [
            (0i64, 0i32),
            (253402300799, 999999999),
            (253402300799, 1000000000),
            (253402300800, 0),
            (253402300800, -1),
            (-377705116800, 0),
            (-377705116801, 0),
            (-377705116801, 1000000000),
            (1700000000, i32::MAX),
            (1700000000, i32::MIN),
            (i64::MAX, 0),
            (i64::MIN, 0),
        ]
        .into_iter()
        .enumerate()
        {
            let signed_proto = proto::AccountKeySignedPayload::from(&signed);
            let mut payload = proto::AccountKeyPayload::parse_from_bytes(&signed_proto.payload).unwrap();
            if let Some(proto::account_key_payload::Payload_type::AccountData(a)) = payload.payload_type.as_mut() {
                let t = a.timestamp.as_mut().unwrap();
                t.seconds = secs;
                t.nanos = nanos;
            }
            let bytes = payload.write_to_bytes().unwrap();
            let mut sp = proto::AccountKeySignedPayload::new();
            sp.payload = bytes;
            sp.signature = signed_proto.signature.clone();
            let mut sd = proto::SyncAccountsData::new();
            sd.accounts_data = vec![sp];
            let mut pm = proto::PeerMessage::new();
            pm.message_type = Some(proto::peer_message::Message_type::SyncAccountsData(sd));
            extra.push((format!("account-data-time-{k}"), pm.write_to_bytes().unwrap()));
            let owned_proto = proto::AccountKeySignedPayload::from(&owned);
            let mut payload = proto::AccountKeyPayload::parse_from_bytes(&owned_proto.payload).unwrap();
            if let Some(proto::account_key_payload::Payload_type::OwnedAccount(a)) = payload.payload_type.as_mut() {
                let t = a.timestamp.as_mut().unwrap();
                t.seconds = secs;
                t.nanos = nanos;
            }
            let mut hs = hs.clone();
            let mut sp = proto::AccountKeySignedPayload::new();
            sp.payload = payload.write_to_bytes().unwrap();
            sp.signature = owned_proto.signature.clone();
            hs.owned_account = protobuf::MessageField::some(sp);
            let mut pm = proto::PeerMessage::new();
            pm.message_type = Some(proto::peer_message::Message_type::Tier2Handshake(hs));
            extra.push((format!("owned-account-time-{k}"), pm.write_to_bytes().unwrap()));
        }
        // routed messages with an out of range creation time
        let m = RawRoutedMessage { target: PeerIdOrHash::PeerId(target_id.clone()), body: TieredMessageBody::from_routed(RoutedMessageBody::Ping(Ping { nonce: 1, source: node_id.clone() })) }
            .sign(&node_sk, 5, None);
        for (k, (secs, nanos)) in [(1700000000i64, 0i32), (253402300800, 0), (-377705116801, 0), (i64::MAX, 0), (5, -7)]
            .into_iter()
            .enumerate()
        {
            let mut r = proto::RoutedMessage::new();
            r.borsh = ser(&m.clone().msg_v1());
            let mut t = protobuf::well_known_types::timestamp::Timestamp::new();
            t.seconds = secs;
            t.nanos = nanos;
            r.created_at = protobuf::MessageField::some(t);
            r.num_hops = 3;
            let mut pm = proto::PeerMessage::new();
            pm.message_type = Some(proto::peer_message::Message_type::Routed(r));
            extra.push((format!("routed-time-{k}"), pm.write_to_bytes().unwrap()));
        }
    }

    let extra_msgs: Vec<(String, Vec<u8>)> = extra;
    peer_family(&mut out, &mut g, msgs, byte_mutations, field_mutations);
    // the hand-built messages and their mutations
    {
        let mut seen = HashSet::new();
        let members: Vec<u32> = vec![4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 25, 26, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37];
        for (name, base) in extra_msgs {
            let mut inputs = vec![(name.clone(), base.clone())];
            if base.len() < 4000 {
                for k in 0..byte_mutations.min(field_mutations).max(4) / 2 {
                    inputs.push((format!("{name}/b{k}"), mutate_bytes(&mut g, &base)));
                    if let Some(b) = mutate_fields(&mut g, &base, &members, 2) {
                        inputs.push((format!("{name}/f{k}"), b));
                    }
                }
            }
            for (n, bytes) in inputs {
                if seen.insert(bytes.clone()) {
                    out.line("PeerMessage", &n, "proto", &bytes, peer_verdict(&bytes));
                }
            }
        }
    }
    out.finish();
}
