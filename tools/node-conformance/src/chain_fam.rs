//! The M1b fixture families: validators, congestion, merkle trees, approvals, chunks, block
//! headers, blocks, challenges and spice types.
#![allow(deprecated)]

use crate::chain::*;
use crate::fam::{hex, Fam, Manifest};
use crate::rng::G;
use crate::values::*;
use crate::SEED;
use near_primitives::bandwidth_scheduler::*;
use near_primitives::block::{Block, BlockV1, BlockV2, BlockV3, BlockV4, Chunks, Tip};
use near_primitives::block_body::*;
use near_primitives::block_header::*;
use near_primitives::challenge::*;
use near_primitives::congestion_info::{CongestionInfo, CongestionInfoV1};
use near_primitives::hash::{hash, CryptoHash};
use near_primitives::merkle::{compute_root_from_path, merklize, MerklePath, PartialMerkleTree};
use near_primitives::optimistic_block::{OptimisticBlock, OptimisticBlockInner};
use near_primitives::sharding::shard_chunk_header_inner::*;
use near_primitives::sharding::*;
use near_primitives::spice::chunk_endorsement::*;
use near_primitives::stateless_validation::chunk_endorsements_bitmap::ChunkEndorsementsBitmap;
use near_primitives::state::PartialState;
use near_primitives::trie_split::TrieSplit;
use near_primitives::types::chunk_extra::ChunkExtra;
use near_primitives::types::validator_stake::ValidatorStake;
use near_primitives::types::{
    ChunkExecutionResult, ChunkExecutionResultHash, EpochId, SpiceChunkEndorsementStats,
    SpiceChunkId, SpiceUncertifiedChunkInfo, ValidatorStakeV1,
};
use near_primitives_core::borsh;
use std::path::PathBuf;

fn h(c: &CryptoHash) -> String {
    hex(&c.0)
}

fn paths_hex(paths: &[MerklePath]) -> String {
    hex(&borsh::to_vec(&paths.to_vec()).unwrap())
}

/// A distinct label for each independent stream of edge-case values.
fn eg(label: &str) -> G {
    G::new(SEED, label)
}

pub fn chain(m: &mut Manifest, dir: &PathBuf) {
    validators(m, dir);
    congestion(m, dir);
    merkle(m, dir);
    approvals(m, dir);
    chunks(m, dir);
    headers(m, dir);
    spice(m, dir);
    challenges(m, dir);
    blocks(m, dir);
}

fn validators(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<EpochId>::new("EpochId", SEED);
    f.edge("zero", EpochId::default());
    f.rand(10, epoch_id);
    f.finish(m, dir);

    let mut f = Fam::<ValidatorStakeV1>::new("ValidatorStakeV1", SEED);
    f.rand(30, stake_v1);
    f.finish(m, dir);

    let mut f = Fam::<ValidatorStake>::new("ValidatorStake", SEED);
    f.edge("zero", ValidatorStake::test("a.near".parse().unwrap()));
    f.rand(30, stake);
    f.raw("tag1", {
        let mut b = vec![1u8];
        b.extend(borsh::to_vec(&stake_v1(&mut eg("vs-tag1"))).unwrap());
        b
    });
    f.finish(m, dir);

    // `compute_bp_hash_from_validator_stakes`, with and without the versioned format.
    let mut f = Fam::<Vec<ValidatorStake>>::new("ValidatorStakes", SEED);
    f.hash(|v: &Vec<ValidatorStake>| {
        vec![
            ("hash", h(&compute_bp_hash_from_validator_stakes(v, true))),
            ("hashV1", h(&compute_bp_hash_from_validator_stakes(v, false))),
        ]
    });
    f.edge("empty", vec![]);
    f.rand(30, |g| g.vec(8, stake));
    f.finish(m, dir);

    let mut f = Fam::<SlashedValidator>::new("SlashedValidator", SEED);
    f.rand(10, slashed);
    f.finish(m, dir);

    let mut f = Fam::<SpiceChunkEndorsementStats>::new("SpiceChunkEndorsementStats", SEED);
    f.edge("max", SpiceChunkEndorsementStats { produced: u32::MAX, expected: u32::MAX });
    f.rand(10, |g| SpiceChunkEndorsementStats { produced: g.u32(), expected: g.u32() });
    f.finish(m, dir);

    let mut f = Fam::<TrieSplit>::new("TrieSplit", SEED);
    f.edge("dummy", TrieSplit::dummy());
    f.rand(10, trie_split);
    f.finish(m, dir);

    let mut f = Fam::<ChunkEndorsementsBitmap>::new("ChunkEndorsementsBitmap", SEED);
    f.edge("genesis", ChunkEndorsementsBitmap::genesis());
    f.edge("from-endorsements", ChunkEndorsementsBitmap::from_endorsements(vec![
        vec![true, false, true],
        vec![],
        vec![true; 130],
    ]));
    f.rand(20, endorsements_bitmap);
    f.finish(m, dir);
}

fn congestion(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<CongestionInfoV1>::new("CongestionInfoV1", SEED);
    f.edge("default", CongestionInfoV1::default());
    f.edge("max", CongestionInfoV1 {
        delayed_receipts_gas: u128::MAX,
        buffered_receipts_gas: u128::MAX,
        receipt_bytes: u64::MAX,
        allowed_shard: u16::MAX,
    });
    f.rand(20, |g| match congestion_info(g) {
        CongestionInfo::V1(v) => v,
    });
    f.finish(m, dir);

    let mut f = Fam::<CongestionInfo>::new("CongestionInfo", SEED);
    f.edge("default", CongestionInfo::default());
    f.rand(20, congestion_info);
    f.raw("tag1", {
        let mut b = vec![1u8];
        b.extend([0; 42]);
        b
    });
    f.finish(m, dir);

    let mut f = Fam::<BandwidthRequestBitmap>::new("BandwidthRequestBitmap", SEED);
    f.edge("zero", BandwidthRequestBitmap::new());
    f.edge("ones", BandwidthRequestBitmap { data: [255; 5] });
    f.rand(10, |g| BandwidthRequestBitmap { data: arr::<5>(g) });
    f.finish(m, dir);

    let mut f = Fam::<BandwidthRequest>::new("BandwidthRequest", SEED);
    f.rand(20, bandwidth_request);
    f.finish(m, dir);

    let mut f = Fam::<BandwidthRequestsV1>::new("BandwidthRequestsV1", SEED);
    f.edge("empty", BandwidthRequestsV1::default());
    f.rand(20, |g| BandwidthRequestsV1 { requests: g.vec(6, bandwidth_request) });
    f.finish(m, dir);

    let mut f = Fam::<BandwidthRequests>::new("BandwidthRequests", SEED);
    f.edge("empty", BandwidthRequests::empty());
    f.rand(20, bandwidth_requests);
    f.raw("tag1", vec![1, 0, 0, 0, 0]);
    f.finish(m, dir);

    let mut f = Fam::<LinkAllowance>::new("LinkAllowance", SEED);
    f.rand(10, |g| LinkAllowance { sender: shard(g), receiver: shard(g), allowance: g.u64() });
    f.finish(m, dir);

    let state_v1 = |g: &mut G| BandwidthSchedulerStateV1 {
        link_allowances: g.vec(6, |g| LinkAllowance {
            sender: shard(g),
            receiver: shard(g),
            allowance: g.u64(),
        }),
        sanity_check_hash: g.hash(),
    };
    let mut f = Fam::<BandwidthSchedulerStateV1>::new("BandwidthSchedulerStateV1", SEED);
    f.rand(15, state_v1);
    f.finish(m, dir);

    let mut f = Fam::<BandwidthSchedulerState>::new("BandwidthSchedulerState", SEED);
    f.rand(15, |g| BandwidthSchedulerState::V1(state_v1(g)));
    f.raw("tag1", vec![1; 40]);
    f.finish(m, dir);

    let mut f = Fam::<BandwidthSchedulerParams>::new("BandwidthSchedulerParams", SEED);
    f.rand(10, |g| BandwidthSchedulerParams {
        base_bandwidth: g.u64(),
        max_shard_bandwidth: g.u64(),
        max_single_grant: g.u64(),
        max_receipt_size: g.u64(),
        max_allowance: g.u64(),
    });
    f.finish(m, dir);

    let mut f = Fam::<ChunkExtra>::new("ChunkExtra", SEED);
    for i in 0..N_CHUNK_EXTRA {
        f.edge(&format!("variant-{i}"), chunk_extra(&mut eg("extra-edge"), i));
    }
    f.rand(40, |g| {
        let i = g.below(N_CHUNK_EXTRA);
        chunk_extra(g, i)
    });
    f.finish(m, dir);
}

fn merkle(m: &mut Manifest, dir: &PathBuf) {
    // `merklize`: the root and every proof. Leaves are the hashes of the items.
    let mut f = Fam::<Vec<CryptoHash>>::new("HashList", SEED);
    f.hash(|v: &Vec<CryptoHash>| {
        let (root, paths) = merklize(v);
        vec![("hash", h(&root)), ("paths", paths_hex(&paths))]
    });
    for n in [0usize, 1, 2, 3, 4, 5, 7, 8, 9, 16, 17, 33] {
        f.edge(&format!("len-{n}"), (0..n).map(|i| CryptoHash::hash_bytes(&[i as u8])).collect());
    }
    f.rand_with(25, 6, |g| {
        let n = g.below(40);
        (0..n).map(|_| g.hash()).collect()
    });
    f.finish(m, dir);

    let mut f = Fam::<Vec<Vec<u8>>>::new("BytesList", SEED);
    f.hash(|v: &Vec<Vec<u8>>| {
        let (root, paths) = merklize(v);
        vec![("hash", h(&root)), ("paths", paths_hex(&paths))]
    });
    f.edge("empty", vec![]);
    f.edge("one-empty", vec![vec![]]);
    f.rand(30, |g| {
        let n = g.below(20);
        (0..n).map(|_| g.bytes(40)).collect()
    });
    f.finish(m, dir);

    let mut f = Fam::<PartialMerkleTree>::new("PartialMerkleTree", SEED);
    f.hash(|t: &PartialMerkleTree| {
        let mut v = vec![
            ("hash", h(&t.root())),
            ("wellFormed", hex(&[t.is_well_formed() as u8])),
        ];
        if t.is_well_formed() {
            let mut next = t.clone();
            next.insert(CryptoHash::hash_bytes(&[7]));
            v.push(("inserted", hex(&borsh::to_vec(&next).unwrap())));
        }
        v
    });
    f.edge("empty", PartialMerkleTree::default());
    for n in [1usize, 2, 3, 7, 8, 64, 100, 1000] {
        let mut t = PartialMerkleTree::default();
        for i in 0..n {
            t.insert(CryptoHash::hash_bytes(&(i as u32).to_le_bytes()));
        }
        f.edge(&format!("size-{n}"), t);
    }
    f.rand(30, partial_merkle_tree);
    // An ill-formed tree (a path of the wrong length) still decodes.
    let mut b = 1u32.to_le_bytes().to_vec();
    b.extend([9; 32]);
    b.extend(3u64.to_le_bytes());
    f.raw("ill-formed", b);
    f.finish(m, dir);
}

fn approvals(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<ApprovalInner>::new("ApprovalInner", SEED);
    f.edge("endorsement", ApprovalInner::Endorsement(CryptoHash([7; 32])));
    f.edge("skip", ApprovalInner::Skip(u64::MAX));
    f.rand(10, approval_inner);
    f.raw("tag2", vec![2; 33]);
    f.finish(m, dir);

    let sig_data = |a: &Approval| vec![("sigData", hex(&Approval::get_data_for_sig(&a.inner, a.target_height)))];
    let mut f = Fam::<Approval>::new("Approval", SEED);
    f.hash(sig_data);
    f.edge("endorsement", Approval::new_for_fixture(ApprovalInner::Endorsement(CryptoHash([1; 32])), 11));
    f.edge("skip", Approval::new_for_fixture(ApprovalInner::Skip(5), 9));
    f.rand(60, approval);
    f.finish(m, dir);

    let mut f = Fam::<ApprovalMessage>::new("ApprovalMessage", SEED);
    f.hash(|a: &ApprovalMessage| {
        vec![("sigData", hex(&Approval::get_data_for_sig(&a.approval.inner, a.approval.target_height)))]
    });
    f.rand(30, |g| ApprovalMessage::new(approval(g), g.account()));
    f.finish(m, dir);
}

trait Fixture {
    fn new_for_fixture(inner: ApprovalInner, target_height: u64) -> Approval;
}

impl Fixture for Approval {
    fn new_for_fixture(inner: ApprovalInner, target_height: u64) -> Approval {
        let mut g = eg("approval-edge");
        let signature = sign_msg(&mut g, &Approval::get_data_for_sig(&inner, target_height));
        Approval { inner, target_height, signature, account_id: "validator.near".parse().unwrap() }
    }
}

/// The merkle root and proofs of the parts, when every part is present (nearcore panics
/// otherwise).
fn body_fields(b: &EncodedShardChunkBody) -> Vec<(&'static str, String)> {
    if b.parts.iter().all(|p| p.is_some()) {
        let (root, paths) = b.get_merkle_hash_and_paths();
        vec![("root", h(&root)), ("paths", paths_hex(&paths))]
    } else {
        vec![]
    }
}

fn chunk_hash_fields(hash_: &ChunkHash, inner_hash: CryptoHash) -> Vec<(&'static str, String)> {
    vec![("hash", h(&hash_.0)), ("innerHash", h(&inner_hash))]
}

fn chunks(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<ChunkHash>::new("ChunkHash", SEED);
    f.rand(10, |g| ChunkHash(g.hash()));
    f.finish(m, dir);

    let mut f = Fam::<ChunkHashHeight>::new("ChunkHashHeight", SEED);
    f.hash(|c: &ChunkHashHeight| vec![("hash", h(&CryptoHash::hash_borsh(c)))]);
    f.rand(10, |g| ChunkHashHeight(ChunkHash(g.hash()), g.u64()));
    f.finish(m, dir);

    macro_rules! inner_family {
        ($name:literal, $ty:ty, $mk:expr) => {{
            let mut f = Fam::<$ty>::new($name, SEED);
            f.rand(25, $mk);
            f.finish(m, dir);
        }};
    }
    inner_family!("ShardChunkHeaderInnerV1", ShardChunkHeaderInnerV1, inner_v1);
    inner_family!("ShardChunkHeaderInnerV2", ShardChunkHeaderInnerV2, inner_v2);
    inner_family!("ShardChunkHeaderInnerV3", ShardChunkHeaderInnerV3, inner_v3);
    inner_family!("ShardChunkHeaderInnerV4", ShardChunkHeaderInnerV4, inner_v4);
    inner_family!("ShardChunkHeaderInnerV5", ShardChunkHeaderInnerV5, inner_v5);
    inner_family!("ShardChunkHeaderInnerV6", ShardChunkHeaderInnerV6SpiceTxOnly, inner_v6);

    let mut f = Fam::<ShardChunkHeaderInner>::new("ShardChunkHeaderInner", SEED);
    f.hash(|i: &ShardChunkHeaderInner| vec![("hash", h(&hash(&borsh::to_vec(i).unwrap())))]);
    for i in 0..N_INNER {
        f.edge(&format!("variant-{i}"), inner(&mut eg("inner-edge"), i));
    }
    f.rand_with(40, 6, |g| {
        let i = g.below(N_INNER);
        inner(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<ShardChunkHeaderV1>::new("ShardChunkHeaderV1", SEED);
    f.hash(|c: &ShardChunkHeaderV1| chunk_hash_fields(&c.hash, hash(&borsh::to_vec(&c.inner).unwrap())));
    f.edge("max-height", {
        let mut c = chunk_header_v1(&mut eg("chv1"));
        c.height_included = u64::MAX;
        c
    });
    f.rand_with(25, 6, chunk_header_v1);
    f.finish(m, dir);

    let mut f = Fam::<ShardChunkHeaderV2>::new("ShardChunkHeaderV2", SEED);
    f.hash(|c: &ShardChunkHeaderV2| chunk_hash_fields(&c.hash, hash(&borsh::to_vec(&c.inner).unwrap())));
    f.rand_with(25, 6, chunk_header_v2);
    f.finish(m, dir);

    let mut f = Fam::<ShardChunkHeaderV3>::new("ShardChunkHeaderV3", SEED);
    f.hash(|c: &ShardChunkHeaderV3| chunk_hash_fields(&c.hash, hash(&borsh::to_vec(&c.inner).unwrap())));
    for i in 0..N_INNER {
        f.edge(&format!("inner-{i}"), chunk_header_v3(&mut eg("chv3"), i));
    }
    f.rand_with(40, 6, |g| {
        let i = g.below(N_INNER);
        chunk_header_v3(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<ShardChunkHeader>::new("ShardChunkHeader", SEED);
    f.hash(|c: &ShardChunkHeader| {
        assert_eq!(c.compute_hash(), *c.chunk_hash());
        chunk_hash_fields(c.chunk_hash(), c.inner_header_hash())
    });
    for i in 0..N_CHUNK_HEADER {
        f.edge(&format!("header-{i}"), chunk_header(&mut eg("ch-edge"), i));
    }
    for i in 0..N_INNER {
        f.edge(&format!("v3-inner-{i}"), ShardChunkHeader::V3(chunk_header_v3(&mut eg("ch-edge3"), i)));
    }
    f.rand_with(100, 6, |g| {
        let i = g.below(N_CHUNK_HEADER);
        chunk_header(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<ShardProof>::new("ShardProof", SEED);
    f.rand(15, shard_proof);
    f.finish(m, dir);

    // `hash` is the hash of the `ReceiptList`. `verify_against_receipt_root` passes it to
    // `verify_path`, which hashes it once more; `root` is the root the proof reaches from that
    // leaf, so `verify_against_receipt_root(root)` holds.
    let mut f = Fam::<ReceiptProof>::new("ReceiptProof", SEED);
    f.hash(|p: &ReceiptProof| {
        let leaf = CryptoHash::hash_borsh(ReceiptList(p.1.to_shard_id, &p.0));
        let root = compute_root_from_path(&p.1.proof, CryptoHash::hash_borsh(leaf));
        assert!(p.verify_against_receipt_root(root));
        vec![("hash", h(&leaf)), ("root", h(&root))]
    });
    f.edge("empty", ReceiptProof(vec![], ShardProof {
        from_shard_id: 0.into(),
        to_shard_id: 1.into(),
        proof: vec![],
    }));
    f.rand(40, receipt_proof);
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedChunkPart>::new("PartialEncodedChunkPart", SEED);
    f.rand(20, part);
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedChunkV1>::new("PartialEncodedChunkV1", SEED);
    f.hash(|c: &PartialEncodedChunkV1| vec![("hash", h(&c.header.hash.0))]);
    f.rand(25, partial_chunk_v1);
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedChunkV2>::new("PartialEncodedChunkV2", SEED);
    f.hash(|c: &PartialEncodedChunkV2| vec![("hash", h(&c.header.chunk_hash().0))]);
    f.rand(25, partial_chunk_v2);
    f.finish(m, dir);

    let mut f = Fam::<PartialEncodedChunk>::new("PartialEncodedChunk", SEED);
    f.hash(|c: &PartialEncodedChunk| vec![("hash", h(&c.chunk_hash().0))]);
    f.edge("v1-empty", PartialEncodedChunk::V1(PartialEncodedChunkV1 {
        header: chunk_header_v1(&mut eg("pec")),
        parts: vec![],
        prev_outgoing_receipts: vec![],
    }));
    f.edge("v2-empty", PartialEncodedChunk::V2(PartialEncodedChunkV2 {
        header: modern_chunk_header(&mut eg("pec")),
        parts: vec![],
        prev_outgoing_receipts: vec![],
    }));
    f.rand_with(40, 4, |g| {
        if g.bool() {
            PartialEncodedChunk::V1(partial_chunk_v1(g))
        } else {
            PartialEncodedChunk::V2(partial_chunk_v2(g))
        }
    });
    f.finish(m, dir);

    let mut f = Fam::<ShardChunkV1>::new("ShardChunkV1", SEED);
    f.hash(|c: &ShardChunkV1| vec![("hash", h(&c.header.hash.0))]);
    f.rand(25, shard_chunk_v1);
    f.finish(m, dir);

    let mut f = Fam::<ShardChunkV2>::new("ShardChunkV2", SEED);
    f.hash(|c: &ShardChunkV2| vec![("hash", h(&c.header.chunk_hash().0))]);
    f.rand(25, shard_chunk_v2);
    f.finish(m, dir);

    let mut f = Fam::<ShardChunk>::new("ShardChunk", SEED);
    f.hash(|c: &ShardChunk| vec![("hash", h(&c.compute_header_hash().0))]);
    f.edge("v1-empty", ShardChunk::V1(ShardChunkV1 {
        chunk_hash: ChunkHash::default(),
        header: chunk_header_v1(&mut eg("sc")),
        transactions: vec![],
        prev_outgoing_receipts: vec![],
    }));
    f.edge("v2-empty", ShardChunk::new(modern_chunk_header(&mut eg("sc")), vec![], vec![]));
    f.rand_with(40, 4, shard_chunk);
    f.finish(m, dir);

    let mut f = Fam::<EncodedShardChunkBody>::new("EncodedShardChunkBody", SEED);
    f.hash(body_fields);
    f.edge("empty", EncodedShardChunkBody::default());
    f.rand(30, chunk_body);
    f.finish(m, dir);

    let mut f = Fam::<EncodedShardChunkV1>::new("EncodedShardChunkV1", SEED);
    f.hash(|c: &EncodedShardChunkV1| vec![("hash", h(&c.header.hash.0))]);
    f.rand(20, encoded_chunk_v1);
    f.finish(m, dir);

    let mut f = Fam::<EncodedShardChunkV2>::new("EncodedShardChunkV2", SEED);
    f.hash(|c: &EncodedShardChunkV2| vec![("hash", h(&c.header.chunk_hash().0))]);
    f.rand(20, encoded_chunk_v2);
    f.finish(m, dir);

    let mut f = Fam::<EncodedShardChunk>::new("EncodedShardChunk", SEED);
    f.hash(|c: &EncodedShardChunk| {
        let mut v = vec![("hash", h(&c.chunk_hash().0))];
        v.extend(body_fields(c.content()));
        v
    });
    f.rand_with(40, 4, |g| {
        if g.bool() {
            EncodedShardChunk::V1(encoded_chunk_v1(g))
        } else {
            EncodedShardChunk::V2(encoded_chunk_v2(g))
        }
    });
    f.finish(m, dir);

    let mut f = Fam::<TransactionReceipt>::new("TransactionReceipt", SEED);
    f.edge("empty", TransactionReceipt(vec![], vec![]));
    f.rand(30, |g| TransactionReceipt(g.vec(3, signed_transaction), g.vec(3, receipt)));
    f.finish(m, dir);

    let mut f = Fam::<StateSyncInfoV0>::new("StateSyncInfoV0", SEED);
    f.rand(10, |g| match state_sync_info(g, 0) {
        StateSyncInfo::V0(v) => v,
        _ => unreachable!(),
    });
    f.finish(m, dir);

    let mut f = Fam::<StateSyncInfoV1>::new("StateSyncInfoV1", SEED);
    f.rand(10, |g| match state_sync_info(g, 1) {
        StateSyncInfo::V1(v) => v,
        _ => unreachable!(),
    });
    f.finish(m, dir);

    let mut f = Fam::<StateSyncInfo>::new("StateSyncInfo", SEED);
    f.rand(20, |g| {
        let i = g.below(2);
        state_sync_info(g, i)
    });
    f.raw("tag2", vec![2; 40]);
    f.finish(m, dir);

    let mut f = Fam::<PartialState>::new("PartialState", SEED);
    f.edge("empty", PartialState::default());
    f.rand(20, partial_state);
    f.raw("tag1", vec![1, 0, 0, 0, 0]);
    f.finish(m, dir);
}

fn block_header_hashes(b: &BlockHeader) -> Vec<(&'static str, String)> {
    let inner = BlockHeader::compute_inner_hash(&b.inner_lite_bytes(), &b.inner_rest_bytes());
    vec![("hash", h(b.hash())), ("innerHash", h(&inner))]
}

fn headers(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<BlockHeaderInnerLite>::new("BlockHeaderInnerLite", SEED);
    f.edge("genesis", BlockHeaderInnerLite::default());
    f.rand(30, |g| {
        let height = g.u64();
        inner_lite(g, height)
    });
    f.finish(m, dir);

    macro_rules! inner_rest_family {
        ($name:literal, $variant:ident, $inner:ident) => {{
            let mut f = Fam::<$inner>::new($name, SEED);
            f.rand_with(20, 4, |g| match header_parts(g, inner_index::<$inner>()) {
                BlockHeader::$variant(x) => x.inner_rest,
                _ => unreachable!(),
            });
            f.finish(m, dir);
        }};
    }
    inner_rest_family!("BlockHeaderInnerRest", BlockHeaderV1, BlockHeaderInnerRest);
    inner_rest_family!("BlockHeaderInnerRestV2", BlockHeaderV2, BlockHeaderInnerRestV2);
    inner_rest_family!("BlockHeaderInnerRestV3", BlockHeaderV3, BlockHeaderInnerRestV3);
    inner_rest_family!("BlockHeaderInnerRestV4", BlockHeaderV4, BlockHeaderInnerRestV4);
    inner_rest_family!("BlockHeaderInnerRestV5", BlockHeaderV5, BlockHeaderInnerRestV5);
    inner_rest_family!("BlockHeaderInnerRestV6", BlockHeaderV6, BlockHeaderInnerRestV6);
    inner_rest_family!("BlockHeaderInnerRestV7", BlockHeaderV7, BlockHeaderInnerRestV7);

    macro_rules! header_family {
        ($name:literal, $variant:ident, $ty:ident, $i:expr) => {{
            let mut f = Fam::<$ty>::new($name, SEED);
            f.hash(|b: &$ty| {
                let inner = BlockHeader::compute_inner_hash(
                    &borsh::to_vec(&b.inner_lite).unwrap(),
                    &borsh::to_vec(&b.inner_rest).unwrap(),
                );
                vec![("hash", h(&b.hash)), ("innerHash", h(&inner))]
            });
            f.rand_with(20, 4, |g| match header_parts(g, $i) {
                BlockHeader::$variant(x) => x,
                _ => unreachable!(),
            });
            f.finish(m, dir);
        }};
    }
    header_family!("BlockHeaderV1", BlockHeaderV1, BlockHeaderV1, 0);
    header_family!("BlockHeaderV2", BlockHeaderV2, BlockHeaderV2, 1);
    header_family!("BlockHeaderV3", BlockHeaderV3, BlockHeaderV3, 2);
    header_family!("BlockHeaderV4", BlockHeaderV4, BlockHeaderV4, 3);
    header_family!("BlockHeaderV5", BlockHeaderV5, BlockHeaderV5, 4);
    header_family!("BlockHeaderV6", BlockHeaderV6, BlockHeaderV6, 5);
    header_family!("BlockHeaderV7", BlockHeaderV7, BlockHeaderV7, 6);

    let mut f = Fam::<BlockHeader>::new("BlockHeader", SEED);
    f.hash(block_header_hashes);
    for i in 0..N_BLOCK_HEADER {
        let mut g = eg("header-edge");
        let r = rand_roots(&mut g);
        f.edge(&format!("variant-{i}"), block_header(&mut g, i, &r));
    }
    // Genesis: no previous block, no approvals, no chunks.
    for i in 4..N_BLOCK_HEADER {
        let mut g = eg("header-genesis");
        let r = Roots {
            height: 0,
            state: g.hash(),
            outcome: CryptoHash::default(),
            receipts: g.hash(),
            headers: g.hash(),
            tx: g.hash(),
            mask: vec![true; 4],
            body_hash: g.hash(),
        };
        f.edge(&format!("genesis-{i}"), block_header(&mut g, i, &r));
    }
    f.rand_with(100, 6, |g| {
        let i = g.below(N_BLOCK_HEADER);
        header_parts(g, i)
    });
    f.finish(m, dir);
}

fn inner_index<T>() -> usize {
    let name = std::any::type_name::<T>();
    match name.rsplit("::").next().unwrap() {
        "BlockHeaderInnerRest" => 0,
        s => s.trim_start_matches("BlockHeaderInnerRestV").parse::<usize>().unwrap() - 1,
    }
}

fn spice(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<SpiceChunkId>::new("SpiceChunkId", SEED);
    f.rand(10, spice_chunk_id);
    f.finish(m, dir);

    let mut f = Fam::<ChunkExecutionResult>::new("ChunkExecutionResult", SEED);
    f.hash(|r: &ChunkExecutionResult| vec![("hash", h(&r.compute_hash().0))]);
    f.rand(40, execution_result);
    f.finish(m, dir);

    let mut f = Fam::<ChunkExecutionResultHash>::new("ChunkExecutionResultHash", SEED);
    f.rand(5, |g| ChunkExecutionResultHash(g.hash()));
    f.finish(m, dir);

    let mut f = Fam::<SpiceEndorsementSignedData>::new("SpiceEndorsementSignedData", SEED);
    f.hash(|d: &SpiceEndorsementSignedData| vec![("sigData", hex(&spice_signing_data(d)))]);
    f.rand(20, spice_signed_data);
    f.finish(m, dir);

    let mut f = Fam::<SpiceEndorsementCoreStatement>::new("SpiceEndorsementCoreStatement", SEED);
    f.rand(30, endorsement_core_statement);
    f.finish(m, dir);

    let mut f = Fam::<SpiceCoreStatement>::new("SpiceCoreStatement", SEED);
    f.rand(40, core_statement);
    f.raw("tag2", vec![2; 100]);
    f.finish(m, dir);

    let mut f = Fam::<SpiceCoreStatements>::new("SpiceCoreStatements", SEED);
    f.edge("empty", SpiceCoreStatements::new(vec![]));
    f.rand(20, |g| SpiceCoreStatements::new(g.vec(4, core_statement)));
    f.finish(m, dir);

    let mut f = Fam::<SpiceStoredVerifiedEndorsement>::new("SpiceStoredVerifiedEndorsement", SEED);
    f.rand(15, stored_endorsement);
    f.finish(m, dir);

    let mut f = Fam::<SpiceChunkEndorsement>::new("SpiceChunkEndorsement", SEED);
    f.rand(30, spice_chunk_endorsement);
    f.raw("tag1", vec![1; 200]);
    f.finish(m, dir);

    let mut f = Fam::<SpiceUncertifiedChunkInfo>::new("SpiceUncertifiedChunkInfo", SEED);
    f.rand(20, uncertified_chunk);
    f.finish(m, dir);
}

fn challenges(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<BlockDoubleSign>::new("BlockDoubleSign", SEED);
    f.rand(10, |g| match challenge_body(g, 0) {
        ChallengeBody::BlockDoubleSign(b) => b,
        _ => unreachable!(),
    });
    f.finish(m, dir);

    let mut f = Fam::<MaybeEncodedShardChunk>::new("MaybeEncodedShardChunk", SEED);
    f.rand_with(30, 4, maybe_encoded);
    f.raw("tag2", vec![2; 100]);
    f.finish(m, dir);

    let mut f = Fam::<ChunkProofs>::new("ChunkProofs", SEED);
    f.rand_with(20, 3, |g| match challenge_body(g, 1) {
        ChallengeBody::ChunkProofs(c) => c,
        _ => unreachable!(),
    });
    f.finish(m, dir);

    let mut f = Fam::<ChunkState>::new("ChunkState", SEED);
    f.rand_with(20, 3, |g| match challenge_body(g, 2) {
        ChallengeBody::ChunkState(c) => c,
        _ => unreachable!(),
    });
    f.finish(m, dir);

    let mut f = Fam::<ChallengeBody>::new("ChallengeBody", SEED);
    for i in 0..N_CHALLENGE {
        f.edge(&format!("variant-{i}"), challenge_body(&mut eg("cb-edge"), i));
    }
    f.rand_with(30, 4, |g| {
        let i = g.below(N_CHALLENGE);
        challenge_body(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<Challenge>::new("Challenge", SEED);
    f.hash(|c: &Challenge| vec![("hash", h(&c.hash))]);
    f.rand_with(30, 3, challenge);
    f.finish(m, dir);
}

fn block_checks(b: &Block) -> Vec<(&'static str, String)> {
    let chunks: Chunks = b.chunks();
    let mut v = vec![("hash", h(b.hash()))];
    if let Some(body) = b.compute_block_body_hash() {
        v.push(("bodyHash", h(&body)));
    }
    let (headers_root, paths) = chunks.compute_chunk_headers_root();
    v.push(("stateRoot", h(&chunks.compute_state_root())));
    v.push(("receiptsRoot", h(&chunks.compute_chunk_prev_outgoing_receipts_root())));
    v.push(("chunkHeadersRoot", h(&headers_root)));
    v.push(("chunkHeadersPaths", paths_hex(&paths)));
    v.push(("txRoot", h(&chunks.compute_chunk_tx_root())));
    v.push(("outcomeRoot", h(&chunks.compute_outcome_root())));
    // 0 for a valid block, then the `BlockValidityError` variants in order.
    let code = match b.check_validity() {
        Ok(()) => 0u8,
        Err(near_primitives::block::BlockValidityError::InvalidStateRoot) => 1,
        Err(near_primitives::block::BlockValidityError::InvalidReceiptRoot) => 2,
        Err(near_primitives::block::BlockValidityError::InvalidChunkHeaderRoot) => 3,
        Err(near_primitives::block::BlockValidityError::InvalidTransactionRoot) => 4,
        Err(near_primitives::block::BlockValidityError::InvalidChunkMask) => 5,
    };
    v.push(("validity", hex(&[code])));
    v
}

fn blocks(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<BlockBodyV1>::new("BlockBodyV1", SEED);
    f.hash(|b: &BlockBodyV1| vec![("hash", h(&b.compute_hash()))]);
    f.rand_with(25, 4, |g| {
        let n = g.below(4);
        let chunks = (0..n).map(|_| modern_chunk_header(g)).collect();
        body_v1(g, chunks)
    });
    f.finish(m, dir);

    let mut f = Fam::<BlockBodyV2>::new("BlockBodyV2", SEED);
    f.rand_with(25, 4, |g| {
        let n = g.below(4);
        let chunks = (0..n).map(|_| modern_chunk_header(g)).collect();
        body_v2(g, chunks)
    });
    f.finish(m, dir);

    let mut f = Fam::<SpiceBlockBodyV3>::new("SpiceBlockBodyV3", SEED);
    f.rand_with(25, 4, |g| {
        let n = g.below(4);
        let chunks = (0..n).map(|_| ShardChunkHeader::V3(chunk_header_v3(g, 5))).collect();
        spice_body(g, chunks)
    });
    f.finish(m, dir);

    let mut f = Fam::<BlockBody>::new("BlockBody", SEED);
    f.hash(|b: &BlockBody| vec![("hash", h(&b.compute_hash()))]);
    for i in 0..N_BODY {
        f.edge(&format!("empty-{i}"), body(&mut eg("body-edge"), i, vec![]));
    }
    f.rand_with(40, 4, |g| {
        let i = g.below(N_BODY);
        let n = g.below(5);
        let chunks = (0..n).map(|_| modern_chunk_header(g)).collect();
        body(g, i, chunks)
    });
    f.finish(m, dir);

    macro_rules! block_family {
        ($name:literal, $ty:ident, $variant:ident, $v:expr, $n:expr) => {{
            let mut f = Fam::<$ty>::new($name, SEED);
            f.hash(|b: &$ty| block_checks(&Block::$variant(b.clone())));
            f.rand_with($n, 2, |g| {
                let hv = g.below(N_BLOCK_HEADER);
                let bv = g.below(N_BODY);
                let valid = g.below(4) != 0;
                match block(g, $v, hv, bv, valid) {
                    Block::$variant(b) => b,
                    _ => unreachable!(),
                }
            });
            f.finish(m, dir);
        }};
    }
    block_family!("BlockV1", BlockV1, BlockV1, 0, 20);
    block_family!("BlockV2", BlockV2, BlockV2, 1, 20);
    block_family!("BlockV3", BlockV3, BlockV3, 2, 20);
    block_family!("BlockV4", BlockV4, BlockV4, 3, 20);

    let mut f = Fam::<Block>::new("Block", SEED);
    f.hash(block_checks);
    // An empty block of every version, and every header version.
    for v in 0..N_BLOCK {
        let mut g = eg("block-edge");
        f.edge(&format!("v{}-header-v{}", v + 1, 1 + v % N_BLOCK_HEADER), block(&mut g, v, v, 1, true));
    }
    for hv in 0..N_BLOCK_HEADER {
        let mut g = eg("block-hv");
        f.edge(&format!("v4-header-v{}", hv + 1), block(&mut g, 3, hv, 1, true));
    }
    f.edge("spice", block(&mut eg("block-spice"), 3, 6, 2, true));
    f.rand_with(70, 3, |g| {
        let v = g.below(N_BLOCK);
        let hv = g.below(N_BLOCK_HEADER);
        let bv = g.below(N_BODY);
        let valid = g.below(4) != 0;
        block(g, v, hv, bv, valid)
    });
    f.finish(m, dir);

    let mut f = Fam::<Tip>::new("Tip", SEED);
    f.rand(10, tip);
    f.finish(m, dir);

    let mut f = Fam::<OptimisticBlockInner>::new("OptimisticBlockInner", SEED);
    f.rand(10, |g| optimistic_block(g).inner);
    f.finish(m, dir);

    let mut f = Fam::<OptimisticBlock>::new("OptimisticBlock", SEED);
    f.hash(|b: &OptimisticBlock| vec![("hash", h(&b.hash))]);
    f.rand(30, optimistic_block);
    f.finish(m, dir);
}
