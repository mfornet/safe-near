//! The M1c state sync and network families: shard state sync headers and responses (all
//! versions), state parts, request keys and acknowledgements, the dump progress, the peer id and
//! the account announcement.
#![allow(deprecated)]

use crate::chain::*;
use crate::fam::{hex, Fam, Manifest};
use crate::rng::G;
use crate::stateless_fam::{h, signer};
use crate::values::*;
use crate::SEED;
use borsh::BorshSerialize;
use near_primitives::genesis::GenesisId;
use near_primitives::network::{AnnounceAccount, PeerId};
use near_primitives::state::PartialState;
use near_primitives::state_part::StatePart;
use near_primitives::state_sync::*;
use near_primitives::types::StateRootNode;
use std::path::PathBuf;
use std::sync::Arc;

fn ser<T: BorshSerialize>(v: &T) -> Vec<u8> {
    borsh::to_vec(v).unwrap()
}

fn eg(label: &str) -> G {
    G::new(SEED, label)
}

fn state_root_node(g: &mut G) -> StateRootNode {
    StateRootNode { data: Arc::from(g.bytes(60)), memory_usage: g.u64() }
}

fn proof_response(g: &mut G) -> ReceiptProofResponse {
    ReceiptProofResponse(g.hash(), Arc::new(g.vec(2, receipt_proof)))
}

fn root_proofs(g: &mut G) -> Vec<Vec<RootProof>> {
    g.vec(2, |g| g.vec(2, |g| RootProof(g.hash(), merkle_path(g))))
}

fn header_v1(g: &mut G) -> ShardStateSyncResponseHeaderV1 {
    ShardStateSyncResponseHeaderV1 {
        chunk: shard_chunk_v1(g),
        chunk_proof: merkle_path(g),
        prev_chunk_header: g.opt(chunk_header_v1),
        prev_chunk_proof: g.opt(merkle_path),
        incoming_receipts_proofs: g.vec(2, proof_response),
        root_proofs: root_proofs(g),
        state_root_node: state_root_node(g),
    }
}

fn header_v2(g: &mut G) -> ShardStateSyncResponseHeaderV2 {
    ShardStateSyncResponseHeaderV2 {
        chunk: shard_chunk(g),
        chunk_proof: merkle_path(g),
        prev_chunk_header: g.opt(|g| {
            let i = g.below(N_CHUNK_HEADER);
            chunk_header(g, i)
        }),
        prev_chunk_proof: g.opt(merkle_path),
        incoming_receipts_proofs: g.vec(2, proof_response),
        root_proofs: root_proofs(g),
        state_root_node: state_root_node(g),
    }
}

/// `get_num_state_parts`, which overflows for a huge memory usage (nearcore is built with overflow
/// checks, this crate without).
fn num_parts(memory_usage: u64) -> String {
    if memory_usage.checked_add(STATE_PART_MEMORY_LIMIT.as_u64() - 1).is_none() {
        return String::new();
    }
    hex(&get_num_state_parts(memory_usage).to_le_bytes())
}

fn header_fields(hd: &ShardStateSyncResponseHeader) -> Vec<(&'static str, String)> {
    vec![
        ("numParts", num_parts(hd.state_root_node().memory_usage)),
        ("heightIncluded", hex(&hd.chunk_height_included().to_le_bytes())),
        ("prevStateRoot", h(&hd.chunk_prev_state_root())),
    ]
}

/// A state part: V0 holds the Borsh of a partial state (or other bytes), V1 its zstd frame.
fn state_part(g: &mut G, i: usize) -> StatePart {
    match i % 3 {
        0 => {
            let mut b = vec![0u8];
            b.extend(ser(&partial_state(g).clone_bytes()));
            StatePart::from_bytes(b).unwrap()
        }
        1 => StatePart::from_bytes({
            let mut b = vec![0u8];
            b.extend(ser(&g.bytes(50)));
            b
        })
        .unwrap(),
        _ => StatePart::from_partial_state(partial_state(g), 1),
    }
}

trait CloneBytes {
    fn clone_bytes(&self) -> Vec<u8>;
}

impl CloneBytes for PartialState {
    fn clone_bytes(&self) -> Vec<u8> {
        ser(self)
    }
}

fn part_fields(p: &StatePart) -> Vec<(&'static str, String)> {
    // Only an uncompressed part is checked: the Lean side has no zstd.
    let partial = match p {
        StatePart::V0(_) => p.to_partial_state().map(|s| hex(&ser(&s))).unwrap_or_default(),
        StatePart::V1(_) => String::new(),
    };
    vec![("payloadLength", hex(&(p.payload_length() as u64).to_le_bytes())), ("partialState", partial)]
}

fn part_of(g: &mut G) -> (u64, StatePart) {
    let i = g.below(3);
    (g.u64(), state_part(g, i))
}

fn raw_part(g: &mut G) -> (u64, Vec<u8>) {
    (g.u64(), g.bytes(80))
}

fn cached_parts(g: &mut G) -> CachedParts {
    match g.below(3) {
        0 => CachedParts::AllParts,
        1 => CachedParts::NoParts,
        _ => {
            let capacity = g.below(100) as u64;
            CachedParts::BitArray(BitArray::new(capacity))
        }
    }
}

fn response_fields(r: &ShardStateSyncResponse) -> Vec<(&'static str, String)> {
    vec![
        ("partId", hex(&ser(&r.part_id()))),
        ("payloadLength", hex(&ser(&r.payload_length().map(|n| n as u64)))),
    ]
}

fn announce(g: &mut G) -> AnnounceAccount {
    let s = signer(g);
    let a = AnnounceAccount::new(&s, PeerId::new(g.pk()), epoch_id(g));
    assert!(a.signature.verify(a.hash().as_ref(), &s.public_key()));
    a
}

pub fn sync(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<StateRootNode>::new("StateRootNode", SEED);
    f.hash(|n: &StateRootNode| vec![("numParts", num_parts(n.memory_usage))]);
    f.edge("empty", StateRootNode::empty());
    for mu in [1u64, 30 << 20, (30 << 20) + 1, 100 * (30 << 20), u64::MAX] {
        f.edge(&format!("usage-{mu}"), StateRootNode { data: Arc::from(vec![1, 2, 3]), memory_usage: mu });
    }
    f.rand(15, state_root_node);
    f.finish(m, dir);

    let mut f = Fam::<ReceiptProofResponse>::new("ReceiptProofResponse", SEED);
    f.rand(10, proof_response);
    f.finish(m, dir);

    let mut f = Fam::<RootProof>::new("RootProof", SEED);
    f.rand(10, |g| RootProof(g.hash(), merkle_path(g)));
    f.finish(m, dir);

    let mut f = Fam::<StateHeaderKey>::new("StateHeaderKey", SEED);
    f.rand(10, |g| StateHeaderKey(shard(g), g.hash()));
    f.finish(m, dir);

    let mut f = Fam::<StatePartKey>::new("StatePartKey", SEED);
    f.rand(10, |g| StatePartKey(g.hash(), shard(g), g.u64()));
    f.finish(m, dir);

    let mut f = Fam::<PartIdOrHeader>::new("PartIdOrHeader", SEED);
    f.edge("header", PartIdOrHeader::Header);
    f.edge("part", PartIdOrHeader::Part { part_id: u64::MAX });
    f.rand(8, |g| if g.bool() { PartIdOrHeader::Header } else { PartIdOrHeader::Part { part_id: g.u64() } });
    f.raw("tag2", vec![2]);
    f.finish(m, dir);

    let mut f = Fam::<StateRequestAckBody>::new("StateRequestAckBody", SEED);
    f.edge("will-respond", StateRequestAckBody::WillRespond);
    f.edge("busy", StateRequestAckBody::Busy);
    f.edge("error", StateRequestAckBody::Error);
    f.raw("tag3", vec![3]);
    f.finish(m, dir);

    let mut f = Fam::<StateRequestAck>::new("StateRequestAck", SEED);
    f.rand(15, |g| StateRequestAck {
        shard_id: shard(g),
        sync_hash: g.hash(),
        part_id_or_header: if g.bool() { PartIdOrHeader::Header } else { PartIdOrHeader::Part { part_id: g.u64() } },
        body: match g.below(3) {
            0 => StateRequestAckBody::WillRespond,
            1 => StateRequestAckBody::Busy,
            _ => StateRequestAckBody::Error,
        },
    });
    f.finish(m, dir);

    let mut f = Fam::<ShardStateSyncResponseHeaderV1>::new("ShardStateSyncResponseHeaderV1", SEED);
    f.mutate_up_to(20000);
    f.rand_with(10, 3, header_v1);
    f.finish(m, dir);

    let mut f = Fam::<ShardStateSyncResponseHeaderV2>::new("ShardStateSyncResponseHeaderV2", SEED);
    f.mutate_up_to(20000);
    f.rand_with(14, 3, header_v2);
    f.finish(m, dir);

    let mut f = Fam::<ShardStateSyncResponseHeader>::new("ShardStateSyncResponseHeader", SEED);
    f.hash(header_fields);
    f.mutate_up_to(20000);
    f.rand_with(20, 4, |g| {
        if g.bool() {
            ShardStateSyncResponseHeader::V1(header_v1(g))
        } else {
            ShardStateSyncResponseHeader::V2(header_v2(g))
        }
    });
    f.finish(m, dir);

    let mut f = Fam::<BitArray>::new("BitArray", SEED);
    f.edge("empty", BitArray::new(0));
    f.rand(8, |g| BitArray::new(g.below(200) as u64));
    f.finish(m, dir);

    let mut f = Fam::<CachedParts>::new("CachedParts", SEED);
    f.edge("all", CachedParts::AllParts);
    f.edge("none", CachedParts::NoParts);
    f.rand(10, cached_parts);
    f.finish(m, dir);

    let mut f = Fam::<StatePart>::new("StatePart", SEED);
    f.hash(part_fields);
    for i in 0..3 {
        f.edge(&format!("kind-{i}"), state_part(&mut eg(&format!("part-edge-{i}")), i));
    }
    f.rand(20, |g| {
        let i = g.below(3);
        state_part(g, i)
    });
    // The entry count of an uncompressed part must be at most 2 * 30 MiB / 50.
    let part = |count: u32, tail: &[u8]| {
        let mut payload = vec![0u8];
        payload.extend(count.to_le_bytes());
        payload.extend(tail);
        let mut b = vec![0u8];
        b.extend(ser(&payload));
        b
    };
    f.raw("limit-exceeded", part(1_258_292, &[]));
    f.raw("limit-reached-truncated", part(1_258_291, &[]));
    f.raw("empty-values", part(2, &[0, 0, 0, 0, 0, 0, 0, 0]));
    f.raw("short-header", { let mut b = vec![0u8]; b.extend(ser(&vec![0u8, 1, 0])); b });
    f.raw("bad-variant", { let mut b = vec![0u8]; b.extend(ser(&vec![1u8, 0, 0, 0, 0])); b });
    f.finish(m, dir);

    let mut f = Fam::<ShardStateSyncResponseV1>::new("ShardStateSyncResponseV1", SEED);
    f.mutate_up_to(20000);
    f.rand_with(12, 2, |g| ShardStateSyncResponseV1 { header: g.opt(header_v1), part: g.opt(raw_part) });
    f.finish(m, dir);
    let mut f = Fam::<ShardStateSyncResponseV2>::new("ShardStateSyncResponseV2", SEED);
    f.mutate_up_to(20000);
    f.rand_with(12, 2, |g| ShardStateSyncResponseV2 { header: g.opt(header_v2), part: g.opt(raw_part) });
    f.finish(m, dir);
    let mut f = Fam::<ShardStateSyncResponseV3>::new("ShardStateSyncResponseV3", SEED);
    f.mutate_up_to(20000);
    f.rand_with(12, 2, |g| ShardStateSyncResponseV3 {
        header: g.opt(header_v2),
        part: g.opt(raw_part),
        cached_parts: g.opt(cached_parts),
        can_generate: g.bool(),
    });
    f.finish(m, dir);
    let mut f = Fam::<ShardStateSyncResponseV4>::new("ShardStateSyncResponseV4", SEED);
    f.mutate_up_to(20000);
    f.rand_with(12, 2, |g| ShardStateSyncResponseV4 { header: g.opt(header_v2), part: g.opt(part_of) });
    f.finish(m, dir);

    let mut f = Fam::<ShardStateSyncResponse>::new("ShardStateSyncResponse", SEED);
    f.hash(response_fields);
    f.mutate_up_to(20000);
    f.edge("header-only", ShardStateSyncResponse::new_from_header(Some(header_v2(&mut eg("resp-h")))));
    f.edge("part-only", ShardStateSyncResponse::new_from_part(Some(part_of(&mut eg("resp-p")))));
    f.edge("empty", ShardStateSyncResponse::new_from_header(None));
    f.rand_with(40, 6, |g| match g.below(4) {
        0 => ShardStateSyncResponse::V1(ShardStateSyncResponseV1 { header: g.opt(header_v1), part: g.opt(raw_part) }),
        1 => ShardStateSyncResponse::V2(ShardStateSyncResponseV2 { header: g.opt(header_v2), part: g.opt(raw_part) }),
        2 => ShardStateSyncResponse::V3(ShardStateSyncResponseV3 {
            header: g.opt(header_v2),
            part: g.opt(raw_part),
            cached_parts: g.opt(cached_parts),
            can_generate: g.bool(),
        }),
        _ => ShardStateSyncResponse::V4(ShardStateSyncResponseV4 { header: g.opt(header_v2), part: g.opt(part_of) }),
    });
    f.finish(m, dir);

    let mut f = Fam::<StateSyncDumpProgress>::new("StateSyncDumpProgress", SEED);
    f.rand(20, |g| match g.below(3) {
        0 => StateSyncDumpProgress::AllDumped { epoch_id: epoch_id(g), epoch_height: g.u64() },
        1 => StateSyncDumpProgress::Skipped { epoch_id: epoch_id(g), epoch_height: g.u64() },
        _ => StateSyncDumpProgress::InProgress { epoch_id: epoch_id(g), epoch_height: g.u64(), sync_hash: g.hash() },
    });
    f.raw("tag3", vec![3; 41]);
    f.finish(m, dir);

    let mut f = Fam::<PeerId>::new("PeerId", SEED);
    f.rand(15, |g| PeerId::new(g.pk()));
    f.finish(m, dir);

    let mut f = Fam::<AnnounceAccount>::new("AnnounceAccount", SEED);
    f.hash(|a: &AnnounceAccount| vec![("hash", h(&a.hash()))]);
    f.rand(20, announce);
    f.finish(m, dir);

    let mut f = Fam::<GenesisId>::new("GenesisId", SEED);
    f.edge("default", GenesisId::default());
    f.rand(10, |g| GenesisId { chain_id: g.string(20), hash: g.hash() });
    f.finish(m, dir);
}
