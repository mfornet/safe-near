//! Constructors for the block, header, approval and chunk types (milestone M1b). Same conventions
//! as `values`: `x(g, i)` builds variant `i` of an enum, and `N_X` is the number of variants.
//! Hashes and signatures that nearcore derives are computed with the crates, so the generated
//! headers and blocks carry real hashes and real signatures of them.
#![allow(deprecated)]

use crate::rng::G;
use crate::values::*;
use borsh::BorshDeserialize;
use near_crypto::vrf::{Proof, Value};
use near_crypto::{KeyType, Signature};
use near_primitives::bandwidth_scheduler::*;
use near_primitives::block::{Block, BlockV1, BlockV2, BlockV3, BlockV4, Chunks, Tip};
use near_primitives::block_body::*;
use near_primitives::block_header::*;
use near_primitives::challenge::*;
use near_primitives::congestion_info::{CongestionInfo, CongestionInfoV1};
use near_primitives::hash::CryptoHash;
use near_primitives::merkle::PartialMerkleTree;
use near_primitives::optimistic_block::OptimisticBlock;
use near_primitives::sharding::shard_chunk_header_inner::*;
use near_primitives::sharding::*;
use near_primitives::spice::chunk_endorsement::*;
use near_primitives::stateless_validation::chunk_endorsements_bitmap::ChunkEndorsementsBitmap;
use near_primitives::state::PartialState;
use near_primitives::trie_split::TrieSplit;
use near_primitives::types::chunk_extra::{ChunkExtra, ChunkExtraV2};
use near_primitives::types::validator_stake::ValidatorStake;
use near_primitives::types::{
    ChunkExecutionResult, ChunkExecutionResultHash, ChunkExtraV1, EpochId, ShardId,
    SpiceChunkEndorsementStats, SpiceChunkId, ValidatorStakeV1,
};
use rand::RngCore;
use std::sync::Arc;

pub const N_BLOCK_HEADER: usize = 7;
pub const N_BLOCK: usize = 4;
pub const N_BODY: usize = 3;
pub const N_CHUNK_HEADER: usize = 3;
pub const N_INNER: usize = 6;
pub const N_CHUNK_EXTRA: usize = 5;
pub const N_CHALLENGE: usize = 3;

pub fn arr<const N: usize>(g: &mut G) -> [u8; N] {
    let mut b = [0u8; N];
    g.0.fill_bytes(&mut b);
    b
}

pub fn shard(g: &mut G) -> ShardId {
    ShardId::new(if g.below(4) == 0 { g.u64() } else { g.below(8) as u64 })
}

/// A signature of `msg` by a fresh key, mostly ED25519. SECP256K1 signs only 32-byte messages.
pub fn sign_msg(g: &mut G, msg: &[u8]) -> Signature {
    let ty = if g.below(12) == 0 && msg.len() == 32 { g.key_type() } else { KeyType::ED25519 };
    let sk = g.secret(ty);
    g.sign(&sk, msg)
}

pub fn stake_v1(g: &mut G) -> ValidatorStakeV1 {
    ValidatorStakeV1 { account_id: g.account(), public_key: g.pk(), stake: g.balance() }
}

pub fn stake(g: &mut G) -> ValidatorStake {
    ValidatorStake::new_v1(g.account(), g.pk(), g.balance())
}

pub fn trie_split(g: &mut G) -> TrieSplit {
    TrieSplit::new(g.account(), g.u64(), g.u64())
}

pub fn epoch_id(g: &mut G) -> EpochId {
    EpochId(g.hash())
}

pub fn congestion_info(g: &mut G) -> CongestionInfo {
    CongestionInfo::V1(CongestionInfoV1 {
        delayed_receipts_gas: g.balance().as_yoctonear(),
        buffered_receipts_gas: g.balance().as_yoctonear(),
        receipt_bytes: g.u64(),
        allowed_shard: g.u16(),
    })
}

pub fn bandwidth_request(g: &mut G) -> BandwidthRequest {
    BandwidthRequest {
        to_shard: g.u16(),
        requested_values_bitmap: BandwidthRequestBitmap { data: arr::<5>(g) },
    }
}

pub fn bandwidth_requests(g: &mut G) -> BandwidthRequests {
    BandwidthRequests::V1(BandwidthRequestsV1 { requests: g.vec(5, bandwidth_request) })
}

pub fn chunk_extra(g: &mut G, i: usize) -> ChunkExtra {
    let i = i % N_CHUNK_EXTRA;
    match i {
        0 => ChunkExtra::V1(ChunkExtraV1 {
            state_root: g.hash(),
            outcome_root: g.hash(),
            validator_proposals: g.vec(3, stake_v1),
            gas_used: g.gas(),
            gas_limit: g.gas(),
            balance_burnt: g.balance(),
        }),
        1 => ChunkExtra::V2(chunk_extra_v2(g)),
        // The congestion info of V3 and later is private: build them from their bytes.
        _ => {
            let mut b = vec![i as u8];
            b.extend(borsh::to_vec(&chunk_extra_v2(g)).unwrap());
            b.extend(borsh::to_vec(&congestion_info(g)).unwrap());
            if i >= 3 {
                b.extend(borsh::to_vec(&bandwidth_requests(g)).unwrap());
            }
            if i == 4 {
                b.extend(borsh::to_vec(&g.opt(trie_split)).unwrap());
            }
            ChunkExtra::try_from_slice(&b).unwrap()
        }
    }
}

fn chunk_extra_v2(g: &mut G) -> ChunkExtraV2 {
    ChunkExtraV2 {
        state_root: g.hash(),
        outcome_root: g.hash(),
        validator_proposals: g.vec(3, stake),
        gas_used: g.gas(),
        gas_limit: g.gas(),
        balance_burnt: g.balance(),
    }
}

pub fn execution_result(g: &mut G) -> ChunkExecutionResult {
    let i = g.below(N_CHUNK_EXTRA);
    ChunkExecutionResult { chunk_extra: chunk_extra(g, i), outgoing_receipts_root: g.hash() }
}

pub fn spice_chunk_id(g: &mut G) -> SpiceChunkId {
    SpiceChunkId { block_hash: g.hash(), shard_id: shard(g) }
}

/// `SpiceEndorsementSignedData::serialize_data_for_signing` (private in the crate; the
/// assertions in `endorsement_core_statement` check it against `verified_signed_data`).
pub fn spice_signing_data(d: &SpiceEndorsementSignedData) -> Vec<u8> {
    borsh::to_vec(&(d, "SpiceChunkEndorsement")).unwrap()
}

pub fn spice_signed_data(g: &mut G) -> SpiceEndorsementSignedData {
    SpiceEndorsementSignedData {
        execution_result_hash: ChunkExecutionResultHash(g.hash()),
        chunk_id: spice_chunk_id(g),
    }
}

pub fn endorsement_core_statement(g: &mut G) -> SpiceEndorsementCoreStatement {
    let sk = g.secret(KeyType::ED25519);
    let data = spice_signed_data(g);
    let signature = sk.sign(&spice_signing_data(&data));
    let s = testonly_create_endorsement_core_statement(g.account(), signature, data);
    assert!(s.verified_signed_data(&sk.public_key()).is_some(), "spice signing data differs");
    s
}

pub fn core_statement(g: &mut G) -> SpiceCoreStatement {
    if g.bool() {
        SpiceCoreStatement::Endorsement(endorsement_core_statement(g))
    } else {
        SpiceCoreStatement::ChunkExecutionResult {
            chunk_id: spice_chunk_id(g),
            execution_result: execution_result(g),
        }
    }
}

pub fn spice_chunk_endorsement(g: &mut G) -> SpiceChunkEndorsement {
    let sk = g.secret(KeyType::ED25519);
    let (chunk_id, execution_result) = (spice_chunk_id(g), execution_result(g));
    let data = SpiceEndorsementSignedData {
        execution_result_hash: execution_result.compute_hash(),
        chunk_id: chunk_id.clone(),
    };
    let signature = sk.sign(&spice_signing_data(&data));
    let e = testonly_create_chunk_endorsement(chunk_id, g.account(), signature, execution_result);
    assert!(e.clone().into_verified(&sk.public_key()).is_some(), "spice signing data differs");
    e
}

pub fn stored_endorsement(g: &mut G) -> SpiceStoredVerifiedEndorsement {
    SpiceStoredVerifiedEndorsement {
        execution_result_hash: ChunkExecutionResultHash(g.hash()),
        signature: g.sig(),
    }
}

pub fn uncertified_chunk(g: &mut G) -> near_primitives::types::SpiceUncertifiedChunkInfo {
    near_primitives::types::SpiceUncertifiedChunkInfo {
        chunk_id: spice_chunk_id(g),
        missing_endorsements: g.vec(3, |g| g.account()),
        present_endorsements: g.vec(3, |g| (g.account(), stored_endorsement(g))),
    }
}

// ----- chunk headers -----

pub fn inner_v1(g: &mut G) -> ShardChunkHeaderInnerV1 {
    ShardChunkHeaderInnerV1 {
        prev_block_hash: g.hash(),
        prev_state_root: g.hash(),
        prev_outcome_root: g.hash(),
        encoded_merkle_root: g.hash(),
        encoded_length: g.u64(),
        height_created: g.u64(),
        shard_id: shard(g),
        prev_gas_used: g.gas(),
        gas_limit: g.gas(),
        prev_balance_burnt: g.balance(),
        prev_outgoing_receipts_root: g.hash(),
        tx_root: g.hash(),
        prev_validator_proposals: g.vec(3, stake_v1),
    }
}

pub fn inner_v2(g: &mut G) -> ShardChunkHeaderInnerV2 {
    ShardChunkHeaderInnerV2 {
        prev_block_hash: g.hash(),
        prev_state_root: g.hash(),
        prev_outcome_root: g.hash(),
        encoded_merkle_root: g.hash(),
        encoded_length: g.u64(),
        height_created: g.u64(),
        shard_id: shard(g),
        prev_gas_used: g.gas(),
        gas_limit: g.gas(),
        prev_balance_burnt: g.balance(),
        prev_outgoing_receipts_root: g.hash(),
        tx_root: g.hash(),
        prev_validator_proposals: g.vec(3, stake),
    }
}

pub fn inner_v3(g: &mut G) -> ShardChunkHeaderInnerV3 {
    let b = inner_v2(g);
    ShardChunkHeaderInnerV3 {
        prev_block_hash: b.prev_block_hash,
        prev_state_root: b.prev_state_root,
        prev_outcome_root: b.prev_outcome_root,
        encoded_merkle_root: b.encoded_merkle_root,
        encoded_length: b.encoded_length,
        height_created: b.height_created,
        shard_id: b.shard_id,
        prev_gas_used: b.prev_gas_used,
        gas_limit: b.gas_limit,
        prev_balance_burnt: b.prev_balance_burnt,
        prev_outgoing_receipts_root: b.prev_outgoing_receipts_root,
        tx_root: b.tx_root,
        prev_validator_proposals: b.prev_validator_proposals,
        congestion_info: congestion_info(g),
    }
}

pub fn inner_v4(g: &mut G) -> ShardChunkHeaderInnerV4 {
    let b = inner_v3(g);
    ShardChunkHeaderInnerV4 {
        prev_block_hash: b.prev_block_hash,
        prev_state_root: b.prev_state_root,
        prev_outcome_root: b.prev_outcome_root,
        encoded_merkle_root: b.encoded_merkle_root,
        encoded_length: b.encoded_length,
        height_created: b.height_created,
        shard_id: b.shard_id,
        prev_gas_used: b.prev_gas_used,
        gas_limit: b.gas_limit,
        prev_balance_burnt: b.prev_balance_burnt,
        prev_outgoing_receipts_root: b.prev_outgoing_receipts_root,
        tx_root: b.tx_root,
        prev_validator_proposals: b.prev_validator_proposals,
        congestion_info: b.congestion_info,
        bandwidth_requests: bandwidth_requests(g),
    }
}

pub fn inner_v5(g: &mut G) -> ShardChunkHeaderInnerV5 {
    let b = inner_v4(g);
    ShardChunkHeaderInnerV5 {
        prev_block_hash: b.prev_block_hash,
        prev_state_root: b.prev_state_root,
        prev_outcome_root: b.prev_outcome_root,
        encoded_merkle_root: b.encoded_merkle_root,
        encoded_length: b.encoded_length,
        height_created: b.height_created,
        shard_id: b.shard_id,
        prev_gas_used: b.prev_gas_used,
        gas_limit: b.gas_limit,
        prev_balance_burnt: b.prev_balance_burnt,
        prev_outgoing_receipts_root: b.prev_outgoing_receipts_root,
        tx_root: b.tx_root,
        prev_validator_proposals: b.prev_validator_proposals,
        congestion_info: b.congestion_info,
        bandwidth_requests: b.bandwidth_requests,
        proposed_split: g.opt(trie_split),
    }
}

pub fn inner_v6(g: &mut G) -> ShardChunkHeaderInnerV6SpiceTxOnly {
    ShardChunkHeaderInnerV6SpiceTxOnly {
        prev_block_hash: g.hash(),
        encoded_merkle_root: g.hash(),
        encoded_length: g.u64(),
        height_created: g.u64(),
        shard_id: shard(g),
        prev_outgoing_receipts_root: g.hash(),
        tx_root: g.hash(),
    }
}

pub fn inner(g: &mut G, i: usize) -> ShardChunkHeaderInner {
    match i % N_INNER {
        0 => ShardChunkHeaderInner::V1(inner_v1(g)),
        1 => ShardChunkHeaderInner::V2(inner_v2(g)),
        2 => ShardChunkHeaderInner::V3(inner_v3(g)),
        3 => ShardChunkHeaderInner::V4(inner_v4(g)),
        4 => ShardChunkHeaderInner::V5(inner_v5(g)),
        _ => ShardChunkHeaderInner::V6(inner_v6(g)),
    }
}

/// The chunk hash is signed by the chunk producer.
pub fn chunk_header_v1(g: &mut G) -> ShardChunkHeaderV1 {
    let mut h = ShardChunkHeaderV1 {
        inner: inner_v1(g),
        height_included: g.u64(),
        signature: Signature::empty(KeyType::ED25519),
        hash: ChunkHash::default(),
    };
    h.init();
    h.signature = sign_msg(g, h.hash.as_ref());
    h
}

pub fn chunk_header_v2(g: &mut G) -> ShardChunkHeaderV2 {
    let mut h = ShardChunkHeaderV2 {
        inner: inner_v1(g),
        height_included: g.u64(),
        signature: Signature::empty(KeyType::ED25519),
        hash: ChunkHash::default(),
    };
    h.init();
    h.signature = sign_msg(g, h.hash.as_ref());
    h
}

pub fn chunk_header_v3(g: &mut G, inner_version: usize) -> ShardChunkHeaderV3 {
    let mut h = ShardChunkHeaderV3 {
        inner: inner(g, inner_version),
        height_included: g.u64(),
        signature: Signature::empty(KeyType::ED25519),
        hash: ChunkHash::default(),
    };
    h.init();
    h.signature = sign_msg(g, h.hash.as_ref());
    h
}

/// A header of version `i` (the inner version is random for V3).
pub fn chunk_header(g: &mut G, i: usize) -> ShardChunkHeader {
    match i % N_CHUNK_HEADER {
        0 => ShardChunkHeader::V1(chunk_header_v1(g)),
        1 => ShardChunkHeader::V2(chunk_header_v2(g)),
        _ => {
            let k = g.below(N_INNER);
            ShardChunkHeader::V3(chunk_header_v3(g, k))
        }
    }
}

pub fn modern_chunk_header(g: &mut G) -> ShardChunkHeader {
    let k = 3 + g.below(3);
    ShardChunkHeader::V3(chunk_header_v3(g, k))
}

pub fn shard_proof(g: &mut G) -> ShardProof {
    ShardProof { from_shard_id: shard(g), to_shard_id: shard(g), proof: merkle_path(g) }
}

pub fn receipt_proof(g: &mut G) -> ReceiptProof {
    ReceiptProof(g.vec(2, receipt), shard_proof(g))
}

pub fn part(g: &mut G) -> PartialEncodedChunkPart {
    PartialEncodedChunkPart {
        part_ord: g.u64(),
        part: g.bytes(64).into_boxed_slice(),
        merkle_proof: merkle_path(g),
    }
}

pub fn partial_chunk_v1(g: &mut G) -> PartialEncodedChunkV1 {
    PartialEncodedChunkV1 {
        header: chunk_header_v1(g),
        parts: g.vec(3, part),
        prev_outgoing_receipts: g.vec(2, receipt_proof),
    }
}

pub fn partial_chunk_v2(g: &mut G) -> PartialEncodedChunkV2 {
    let i = g.below(N_CHUNK_HEADER);
    PartialEncodedChunkV2 {
        header: chunk_header(g, i),
        parts: g.vec(3, part),
        prev_outgoing_receipts: g.vec(2, receipt_proof),
    }
}

pub fn shard_chunk_v1(g: &mut G) -> ShardChunkV1 {
    let header = chunk_header_v1(g);
    // The stored `chunk_hash` is a separate field: mostly consistent, sometimes not.
    let chunk_hash = if g.below(4) == 0 { ChunkHash(g.hash()) } else { header.hash.clone() };
    ShardChunkV1 {
        chunk_hash,
        header,
        transactions: g.vec(2, signed_transaction),
        prev_outgoing_receipts: g.vec(2, receipt),
    }
}

pub fn shard_chunk_v2(g: &mut G) -> ShardChunkV2 {
    let i = g.below(N_CHUNK_HEADER);
    let header = chunk_header(g, i);
    let chunk_hash =
        if g.below(4) == 0 { ChunkHash(g.hash()) } else { header.chunk_hash().clone() };
    ShardChunkV2 {
        chunk_hash,
        header,
        transactions: g.vec(2, signed_transaction),
        prev_outgoing_receipts: g.vec(2, receipt),
    }
}

pub fn chunk_body(g: &mut G) -> EncodedShardChunkBody {
    // Half the bodies have every part present, so that their merkle root is defined.
    let all = g.bool();
    EncodedShardChunkBody {
        parts: g.vec(6, |g| {
            if all || g.bool() { Some(g.bytes(48).into_boxed_slice()) } else { None }
        }),
    }
}

pub fn encoded_chunk_v1(g: &mut G) -> EncodedShardChunkV1 {
    EncodedShardChunkV1 { header: chunk_header_v1(g), content: chunk_body(g) }
}

pub fn encoded_chunk_v2(g: &mut G) -> EncodedShardChunkV2 {
    let i = g.below(N_CHUNK_HEADER);
    EncodedShardChunkV2 { header: chunk_header(g, i), content: chunk_body(g) }
}

pub fn partial_state(g: &mut G) -> PartialState {
    PartialState::TrieValues(g.vec(4, |g| Arc::from(g.bytes(40))))
}

pub fn state_sync_info(g: &mut G, i: usize) -> StateSyncInfo {
    let shards = g.vec(4, |g| shard(g));
    if i % 2 == 0 {
        StateSyncInfo::V0(StateSyncInfoV0 { sync_hash: g.hash(), shards })
    } else {
        StateSyncInfo::V1(StateSyncInfoV1 {
            epoch_first_block: g.hash(),
            sync_hash: g.opt(|g| g.hash()),
            shards,
        })
    }
}

// ----- challenges -----

pub fn maybe_encoded(g: &mut G) -> MaybeEncodedShardChunk {
    if g.bool() {
        let i = g.below(2);
        MaybeEncodedShardChunk::Encoded(if i == 0 {
            EncodedShardChunk::V1(encoded_chunk_v1(g))
        } else {
            EncodedShardChunk::V2(encoded_chunk_v2(g))
        })
    } else {
        MaybeEncodedShardChunk::Decoded(shard_chunk(g))
    }
}

pub fn shard_chunk(g: &mut G) -> ShardChunk {
    if g.bool() { ShardChunk::V1(shard_chunk_v1(g)) } else { ShardChunk::V2(shard_chunk_v2(g)) }
}

pub fn challenge_body(g: &mut G, i: usize) -> ChallengeBody {
    match i % N_CHALLENGE {
        0 => ChallengeBody::BlockDoubleSign(BlockDoubleSign {
            left_block_header: g.bytes(100),
            right_block_header: g.bytes(100),
        }),
        1 => ChallengeBody::ChunkProofs(ChunkProofs {
            block_header: g.bytes(100),
            merkle_proof: merkle_path(g),
            chunk: Box::new(maybe_encoded(g)),
        }),
        _ => ChallengeBody::ChunkState(ChunkState {
            prev_block_header: g.bytes(100),
            block_height: g.u64(),
            prev_merkle_proof: merkle_path(g),
            prev_chunk: shard_chunk(g),
            merkle_proof: merkle_path(g),
            chunk_header: {
                let i = g.below(N_CHUNK_HEADER);
                chunk_header(g, i)
            },
            partial_state: partial_state(g),
        }),
    }
}

pub fn challenge(g: &mut G) -> Challenge {
    let i = g.below(N_CHALLENGE);
    let mut c = Challenge {
        body: challenge_body(g, i),
        account_id: g.account(),
        signature: g.sig(),
        hash: CryptoHash::default(),
    };
    c.init();
    c
}

// ----- approvals -----

pub fn approval_inner(g: &mut G) -> ApprovalInner {
    if g.bool() { ApprovalInner::Endorsement(g.hash()) } else { ApprovalInner::Skip(g.u64()) }
}

/// An approval signed over `get_data_for_sig`.
pub fn approval(g: &mut G) -> Approval {
    let inner = approval_inner(g);
    let target_height = g.u64();
    let signature = sign_msg(g, &Approval::get_data_for_sig(&inner, target_height));
    Approval { inner, target_height, signature, account_id: g.account() }
}

// ----- block headers -----

pub fn inner_lite(g: &mut G, height: u64) -> BlockHeaderInnerLite {
    BlockHeaderInnerLite {
        height,
        epoch_id: epoch_id(g),
        next_epoch_id: epoch_id(g),
        prev_state_root: g.hash(),
        prev_outcome_root: g.hash(),
        timestamp: g.u64(),
        next_bp_hash: g.hash(),
        block_merkle_root: g.hash(),
    }
}

pub fn approvals(g: &mut G) -> Vec<Option<Box<Signature>>> {
    let ty_all_ed = |g: &mut G| Box::new(g.sig_of(KeyType::ED25519));
    g.vec(10, |g| g.opt(ty_all_ed))
}

pub fn endorsements_bitmap(g: &mut G) -> ChunkEndorsementsBitmap {
    ChunkEndorsementsBitmap::from_bytes(g.vec(4, |g| g.bytes(8)))
}

pub fn endorsement_stats(g: &mut G) -> Vec<SpiceChunkEndorsementStats> {
    g.vec(5, |g| SpiceChunkEndorsementStats { produced: g.u32(), expected: g.u32() })
}

pub fn shard_split(g: &mut G) -> Option<(ShardId, near_primitives::types::AccountId)> {
    g.opt(|g| (shard(g), g.account()))
}

/// The values of a header that depend on the block's chunks.
#[derive(Clone)]
pub struct Roots {
    pub height: u64,
    pub state: CryptoHash,
    pub outcome: CryptoHash,
    pub receipts: CryptoHash,
    pub headers: CryptoHash,
    pub tx: CryptoHash,
    pub mask: Vec<bool>,
    pub body_hash: CryptoHash,
}

pub fn rand_roots(g: &mut G) -> Roots {
    Roots {
        height: g.u64(),
        state: g.hash(),
        outcome: g.hash(),
        receipts: g.hash(),
        headers: g.hash(),
        tx: g.hash(),
        mask: g.vec(5, |g| g.bool()),
        body_hash: g.hash(),
    }
}

/// A header of version `i` whose chunk-dependent fields come from `r`, with a real hash and a
/// real signature of it.
pub fn block_header(g: &mut G, i: usize, r: &Roots) -> BlockHeader {
    let prev_hash = g.hash();
    let lite = BlockHeaderInnerLite { prev_state_root: r.state, prev_outcome_root: r.outcome,
        ..inner_lite(g, r.height) };
    let empty = Signature::empty(KeyType::ED25519);
    let hash = CryptoHash::default();
    macro_rules! header {
        ($variant:ident, $ty:ident, $rest:expr) => {{
            let mut h = $ty { prev_hash, inner_lite: lite, inner_rest: $rest, signature: empty, hash };
            h.init();
            h.signature = sign_msg(g, h.hash.as_ref());
            BlockHeader::$variant(h)
        }};
    }
    match i % N_BLOCK_HEADER {
        0 => header!(BlockHeaderV1, BlockHeaderV1, BlockHeaderInnerRest {
            prev_chunk_outgoing_receipts_root: r.receipts,
            chunk_headers_root: r.headers,
            chunk_tx_root: r.tx,
            chunks_included: r.mask.iter().filter(|b| **b).count() as u64,
            challenges_root: g.hash(),
            random_value: g.hash(),
            prev_validator_proposals: g.vec(3, stake_v1),
            chunk_mask: r.mask.clone(),
            next_gas_price: g.balance(),
            total_supply: g.balance(),
            challenges_result: g.vec(2, slashed),
            last_final_block: g.hash(),
            last_ds_final_block: g.hash(),
            approvals: approvals(g),
            latest_protocol_version: g.u32(),
        }),
        1 => header!(BlockHeaderV2, BlockHeaderV2, BlockHeaderInnerRestV2 {
            prev_chunk_outgoing_receipts_root: r.receipts,
            chunk_headers_root: r.headers,
            chunk_tx_root: r.tx,
            challenges_root: g.hash(),
            random_value: g.hash(),
            prev_validator_proposals: g.vec(3, stake_v1),
            chunk_mask: r.mask.clone(),
            next_gas_price: g.balance(),
            total_supply: g.balance(),
            challenges_result: g.vec(2, slashed),
            last_final_block: g.hash(),
            last_ds_final_block: g.hash(),
            approvals: approvals(g),
            latest_protocol_version: g.u32(),
        }),
        2 => header!(BlockHeaderV3, BlockHeaderV3, BlockHeaderInnerRestV3 {
            prev_chunk_outgoing_receipts_root: r.receipts,
            chunk_headers_root: r.headers,
            chunk_tx_root: r.tx,
            challenges_root: g.hash(),
            random_value: g.hash(),
            prev_validator_proposals: g.vec(3, stake),
            chunk_mask: r.mask.clone(),
            next_gas_price: g.balance(),
            total_supply: g.balance(),
            challenges_result: g.vec(2, slashed),
            last_final_block: g.hash(),
            last_ds_final_block: g.hash(),
            block_ordinal: g.u64(),
            prev_height: g.u64(),
            epoch_sync_data_hash: g.opt(|g| g.hash()),
            approvals: approvals(g),
            latest_protocol_version: g.u32(),
        }),
        3 => header!(BlockHeaderV4, BlockHeaderV4, BlockHeaderInnerRestV4 {
            block_body_hash: r.body_hash,
            prev_chunk_outgoing_receipts_root: r.receipts,
            chunk_headers_root: r.headers,
            chunk_tx_root: r.tx,
            challenges_root: g.hash(),
            random_value: g.hash(),
            prev_validator_proposals: g.vec(3, stake),
            chunk_mask: r.mask.clone(),
            next_gas_price: g.balance(),
            total_supply: g.balance(),
            challenges_result: g.vec(2, slashed),
            last_final_block: g.hash(),
            last_ds_final_block: g.hash(),
            block_ordinal: g.u64(),
            prev_height: g.u64(),
            epoch_sync_data_hash: g.opt(|g| g.hash()),
            approvals: approvals(g),
            latest_protocol_version: g.u32(),
        }),
        4 => header!(BlockHeaderV5, BlockHeaderV5, BlockHeaderInnerRestV5 {
            block_body_hash: r.body_hash,
            prev_chunk_outgoing_receipts_root: r.receipts,
            chunk_headers_root: r.headers,
            chunk_tx_root: r.tx,
            challenges_root: g.hash(),
            random_value: g.hash(),
            prev_validator_proposals: g.vec(3, stake),
            chunk_mask: r.mask.clone(),
            next_gas_price: g.balance(),
            total_supply: g.balance(),
            challenges_result: g.vec(2, slashed),
            last_final_block: g.hash(),
            last_ds_final_block: g.hash(),
            block_ordinal: g.u64(),
            prev_height: g.u64(),
            epoch_sync_data_hash: g.opt(|g| g.hash()),
            approvals: approvals(g),
            latest_protocol_version: g.u32(),
            chunk_endorsements: endorsements_bitmap(g),
        }),
        5 => header!(BlockHeaderV6, BlockHeaderV6, BlockHeaderInnerRestV6 {
            block_body_hash: r.body_hash,
            prev_chunk_outgoing_receipts_root: r.receipts,
            chunk_headers_root: r.headers,
            chunk_tx_root: r.tx,
            random_value: g.hash(),
            prev_validator_proposals: g.vec(3, stake),
            chunk_mask: r.mask.clone(),
            next_gas_price: g.balance(),
            total_supply: g.balance(),
            last_final_block: g.hash(),
            last_ds_final_block: g.hash(),
            block_ordinal: g.u64(),
            prev_height: g.u64(),
            epoch_sync_data_hash: g.opt(|g| g.hash()),
            approvals: approvals(g),
            latest_protocol_version: g.u32(),
            chunk_endorsements: endorsements_bitmap(g),
            shard_split: shard_split(g),
        }),
        _ => header!(BlockHeaderV7, BlockHeaderV7, BlockHeaderInnerRestV7 {
            block_body_hash: r.body_hash,
            prev_chunk_outgoing_receipts_root: r.receipts,
            chunk_headers_root: r.headers,
            chunk_tx_root: r.tx,
            random_value: g.hash(),
            prev_validator_proposals: g.vec(3, stake),
            chunk_mask: r.mask.clone(),
            next_gas_price: g.balance(),
            total_supply: g.balance(),
            last_final_block: g.hash(),
            last_ds_final_block: g.hash(),
            block_ordinal: g.u64(),
            prev_height: g.u64(),
            epoch_sync_data_hash: g.opt(|g| g.hash()),
            approvals: approvals(g),
            latest_protocol_version: g.u32(),
            chunk_endorsements: endorsements_bitmap(g),
            shard_split: shard_split(g),
            prev_last_certified_block_epoch_id: epoch_id(g),
            spice_chunk_endorsement_stats: endorsement_stats(g),
        }),
    }
}

pub fn slashed(g: &mut G) -> near_primitives::challenge::SlashedValidator {
    near_primitives::challenge::SlashedValidator { account_id: g.account(), is_double_sign: g.bool() }
}

/// The inner parts of header version `i`, for the families of their own.
pub fn header_parts(g: &mut G, i: usize) -> BlockHeader {
    let r = rand_roots(g);
    block_header(g, i, &r)
}

// ----- blocks -----

fn vrf(g: &mut G) -> (Value, Proof) {
    (Value(arr::<32>(g)), Proof(arr::<64>(g)))
}

pub fn body_v1(g: &mut G, chunks: Vec<ShardChunkHeader>) -> BlockBodyV1 {
    let (vrf_value, vrf_proof) = vrf(g);
    BlockBodyV1 {
        chunks,
        challenges: if g.below(5) == 0 { g.vec(1, challenge) } else { vec![] },
        vrf_value,
        vrf_proof,
    }
}

pub fn body_v2(g: &mut G, chunks: Vec<ShardChunkHeader>) -> BlockBodyV2 {
    let (vrf_value, vrf_proof) = vrf(g);
    let shards = chunks.len();
    BlockBodyV2 {
        chunks,
        challenges: if g.below(5) == 0 { g.vec(1, challenge) } else { vec![] },
        vrf_value,
        vrf_proof,
        chunk_endorsements: (0..shards)
            .map(|_| g.vec(5, |g| g.opt(|g| Box::new(g.sig_of(KeyType::ED25519)))))
            .collect(),
    }
}

pub fn spice_body(g: &mut G, chunks: Vec<ShardChunkHeader>) -> SpiceBlockBodyV3 {
    let (vrf_value, vrf_proof) = vrf(g);
    SpiceBlockBodyV3 {
        chunks,
        vrf_value,
        vrf_proof,
        core_statements: SpiceCoreStatements::new(g.vec(3, core_statement)),
    }
}

/// `BlockBody` of version `i`, with the given chunks.
pub fn body(g: &mut G, i: usize, chunks: Vec<ShardChunkHeader>) -> BlockBody {
    match i % N_BODY {
        0 => BlockBody::V1(body_v1(g, chunks)),
        1 => BlockBody::V2(body_v2(g, chunks)),
        _ => BlockBody::V3(spice_body(g, chunks)),
    }
}

/// A chunk header for a block at `height`: new in this block two thirds of the time.
fn block_chunk(g: &mut G, height: u64, version: usize, inner_version: usize) -> ShardChunkHeader {
    let mut h = match version {
        0 => ShardChunkHeader::V1(chunk_header_v1(g)),
        1 => ShardChunkHeader::V2(chunk_header_v2(g)),
        _ => ShardChunkHeader::V3(chunk_header_v3(g, inner_version)),
    };
    *h.height_included_mut() = if g.below(3) == 0 { height.saturating_sub(1 + g.below(3) as u64) } else { height };
    h
}

/// A block of version `v` whose header (of version `hv`) commits to its chunks. With `valid`
/// false, one committed value is replaced by a random one. The body of a V4 block is of version
/// `body_version`; V3 blocks have a V1 body.
pub fn block(g: &mut G, v: usize, hv: usize, body_version: usize, valid: bool) -> Block {
    let v = v % N_BLOCK;
    let height = if g.below(3) == 0 { g.u64() } else { 1_000_000 + g.below(1000) as u64 };
    let shards = g.below(5);
    let spice = v == 3 && body_version % N_BODY == 2;
    // Chunk header version: V1 for V1 blocks, V2/V3 for the others; spice chunks are V3 + V6.
    let chunk_version = |g: &mut G| match v {
        0 => 0,
        1 | 2 => g.below(N_CHUNK_HEADER),
        _ => 2,
    };
    let mut chunks = vec![];
    for _ in 0..shards {
        let cv = chunk_version(g);
        let iv = if spice { 5 } else { g.below(N_INNER) };
        chunks.push(block_chunk(g, height, cv, iv));
    }
    // The body, then the roots over the chunks as `Block::chunks` sees them.
    let body_chunks = chunks.clone();
    let (mut roots, body_opt) = {
        let wrapper = Chunks::from_chunk_headers(&chunks, height);
        let mask: Vec<bool> = chunks.iter().map(|c| c.is_new_chunk(height)).collect();
        (
            Roots {
                height,
                state: if spice { CryptoHash::default() } else { wrapper.compute_state_root() },
                outcome: wrapper.compute_outcome_root(),
                receipts: wrapper.compute_chunk_prev_outgoing_receipts_root(),
                headers: wrapper.compute_chunk_headers_root().0,
                tx: wrapper.compute_chunk_tx_root(),
                mask,
                body_hash: CryptoHash::default(),
            },
            match v {
                2 => Some(BlockBody::V1(body_v1(g, body_chunks))),
                3 => Some(body(g, body_version, body_chunks)),
                _ => None,
            },
        )
    };
    if let Some(b) = &body_opt {
        roots.body_hash = b.compute_hash();
    }
    if !valid {
        match g.below(7) {
            0 => roots.state = g.hash(),
            1 => roots.outcome = g.hash(),
            2 => roots.receipts = g.hash(),
            3 => roots.headers = g.hash(),
            4 => roots.tx = g.hash(),
            5 => roots.body_hash = g.hash(),
            _ => roots.mask.push(g.bool()),
        }
    }
    let header = block_header(g, hv, &roots);
    let (vrf_value, vrf_proof) = vrf(g);
    let challenges = if g.below(6) == 0 { g.vec(1, challenge) } else { vec![] };
    match v {
        0 => Block::BlockV1(BlockV1 {
            header,
            chunks: chunks
                .into_iter()
                .map(|c| match c {
                    ShardChunkHeader::V1(h) => h,
                    _ => unreachable!(),
                })
                .collect(),
            challenges,
            vrf_value,
            vrf_proof,
        }),
        1 => Block::BlockV2(BlockV2 { header, chunks, challenges, vrf_value, vrf_proof }),
        2 => match body_opt.unwrap() {
            BlockBody::V1(body) => Block::BlockV3(BlockV3 { header, body }),
            _ => unreachable!(),
        },
        _ => Block::BlockV4(BlockV4 { header, body: body_opt.unwrap() }),
    }
}

pub fn tip(g: &mut G) -> Tip {
    Tip {
        height: g.u64(),
        last_block_hash: g.hash(),
        prev_block_hash: g.hash(),
        epoch_id: epoch_id(g),
        next_epoch_id: epoch_id(g),
    }
}

pub fn optimistic_block(g: &mut G) -> OptimisticBlock {
    // `signature_differentiator` is private: build the value from its bytes.
    let mut b = Vec::new();
    b.extend(g.hash().0);
    b.extend(g.u64().to_le_bytes());
    b.extend(g.u64().to_le_bytes());
    b.extend(g.hash().0);
    b.extend(arr::<32>(g));
    b.extend(arr::<64>(g));
    let differentiator = if g.below(4) == 0 { g.string(12) } else { "OptimisticBlock".to_string() };
    b.extend((differentiator.len() as u32).to_le_bytes());
    b.extend(differentiator.as_bytes());
    let signature = sign_msg(g, &b);
    b.extend(borsh::to_vec(&signature).unwrap());
    OptimisticBlock::try_from_slice(&b).unwrap()
}

pub fn partial_merkle_tree(g: &mut G) -> PartialMerkleTree {
    let mut t = PartialMerkleTree::default();
    for _ in 0..g.below(70) {
        t.insert(g.hash());
    }
    t
}
