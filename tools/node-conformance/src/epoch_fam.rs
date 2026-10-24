//! The M1c epoch families: shard layouts, `EpochInfo` (V1 to V5) with the stake-weighted
//! samplers and validator mandates it stores, `BlockInfo`, `EpochSummary` and the epoch sync
//! proof.
//!
//! Derived values are the functions that pick producers from an `EpochInfo`:
//! `sample_block_producer`, `sample_chunk_producer` and `sample_chunk_validators` over the fixed
//! heights below, `validator_account_id` and `get_validator_id`. A computation that panics in
//! nearcore (an index out of range, a division by zero, an overflow) is recorded as no value, so
//! lines whose bytes decode but are not a valid epoch are still checked.
#![allow(deprecated)]

use crate::chain::*;
use crate::fam::{hex, Fam, Manifest};
use crate::rng::G;
use crate::stateless_fam::h;
use crate::values::*;
use crate::SEED;
use borsh::{BorshDeserialize, BorshSerialize};
use near_primitives::epoch_block_info::*;
use near_primitives::epoch_info::{EpochInfo, EpochInfoV1, EpochInfoV2, ValidatorWeight};
use near_primitives::epoch_manager::EpochSummary;
use near_primitives::epoch_sync::*;
use near_primitives::hash::hash;
use near_primitives::rand::StakeWeightedIndex;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::types::validator_stake::ValidatorStake;
use near_primitives::types::{
    AccountId, Balance, BlockChunkValidatorStats, ChunkStats, ShardId, ValidatorKickoutReason, ValidatorStats,
};
use near_primitives::utils::compression::CompressedData;
use near_primitives::validator_mandates::{ValidatorMandates, ValidatorMandatesConfig};
use rand::{Rng, RngCore, SeedableRng};
use rand_chacha::ChaCha20Rng;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

/// Heights at which the samplers are evaluated (the Lean test has the same list).
pub fn sample_heights() -> Vec<u64> {
    let mut v: Vec<u64> = (0..16).collect();
    v.extend([
        100,
        255,
        256,
        1000,
        65535,
        65536,
        12345678,
        4294967295,
        4294967296,
        1099511627783,
        i64::MAX as u64,
        1 << 63,
        u64::MAX - 1,
        u64::MAX,
    ]);
    v.extend((16..32u64).map(|i| 37 * i * i + i));
    v
}

/// The heights at which chunk validators are sampled.
fn validator_heights() -> Vec<u64> {
    sample_heights().into_iter().step_by(7).collect()
}

fn sid(s: ShardId) -> u64 {
    s.into()
}

fn ser<T: BorshSerialize>(v: &T) -> Vec<u8> {
    borsh::to_vec(v).unwrap()
}

static QUIET: AtomicBool = AtomicBool::new(false);

/// Runs `f`, returning `None` if it panics (without a message).
fn quiet<T>(f: impl FnOnce() -> T) -> Option<T> {
    QUIET.store(true, Ordering::SeqCst);
    let r = catch_unwind(AssertUnwindSafe(f)).ok();
    QUIET.store(false, Ordering::SeqCst);
    r
}

pub fn install_quiet_hook() {
    let default = std::panic::take_hook();
    std::panic::set_hook(Box::new(move |info| {
        if !QUIET.load(Ordering::SeqCst) {
            default(info)
        }
    }));
}

fn eg(label: &str) -> G {
    G::new(SEED, label)
}

// ----- shard layouts -----

fn sorted_accounts(g: &mut G, n: usize) -> Vec<AccountId> {
    let mut v: Vec<AccountId> = (0..n).map(|_| g.account()).collect();
    v.sort();
    v
}

pub const N_LAYOUT: usize = 4;

pub fn shard_layout(g: &mut G, i: usize) -> ShardLayout {
    let n = 1 + g.below(5);
    let boundaries = sorted_accounts(g, n - 1);
    let version = g.u16() as u32;
    match i % N_LAYOUT {
        0 => ShardLayout::v0(n as u64, version),
        1 => {
            // The children of each parent partition the new shards.
            let split = g.opt(|g| {
                let parents = 1 + g.below(n);
                let mut map: Vec<Vec<ShardId>> = vec![vec![]; parents];
                for s in 0..n {
                    let p = if s < parents { s } else { g.below(parents) };
                    map[p].push(ShardId::new(s as u64));
                }
                map
            });
            ShardLayout::v1(boundaries, split, version)
        }
        2 => {
            let ids = shard_ids(g, n);
            let split = g.opt(|g| {
                let mut map: BTreeMap<ShardId, Vec<ShardId>> =
                    ids.iter().map(|&s| (s, vec![s])).collect();
                if n >= 2 && g.bool() {
                    let (a, b) = (ids[0], ids[1]);
                    map.remove(&a);
                    map.remove(&b);
                    map.insert(ShardId::new(1000), vec![a, b]);
                }
                map
            });
            ShardLayout::v2(boundaries, ids, split)
        }
        _ => {
            let mut ids = shard_ids(g, n.max(2));
            let boundaries = sorted_accounts(g, ids.len() - 1);
            let mut map: BTreeMap<ShardId, Vec<ShardId>> = BTreeMap::new();
            map.insert(ShardId::new(1000), vec![ids[0], ids[1]]);
            let mut last = ShardId::new(1000);
            if ids.len() >= 3 && g.bool() {
                // The parent of a shard that was split before.
                map.insert(ShardId::new(2000), vec![ShardId::new(1000), ids[2]]);
                last = ShardId::new(2000);
            }
            ids.sort_by_key(|s| sid(*s) ^ 0x55);
            ShardLayout::v3(boundaries, ids, map, last)
        }
    }
}

/// Distinct shard ids below 1000, in a random order.
fn shard_ids(g: &mut G, n: usize) -> Vec<ShardId> {
    let mut all: Vec<u64> = (0..n as u64 + 4).collect();
    for i in (1..all.len()).rev() {
        let j = g.below(i + 1);
        all.swap(i, j);
    }
    all.into_iter().take(n).map(ShardId::new).collect()
}

const PROBE_ACCOUNTS: [&str; 6] = ["a.near", "alice.near", "test1", "test2", "zzzzzzzz.near", "00"];

fn layout_fields(l: &ShardLayout) -> Vec<(&'static str, String)> {
    let opt_u64 = |v: Option<u64>| v;
    let indexes: Vec<Option<u64>> = (0..8u64)
        .chain([1000, 2000, u64::MAX])
        .map(|s| opt_u64(l.get_shard_index(ShardId::new(s)).ok().map(|i| i as u64)))
        .collect();
    let ids: Vec<Option<u64>> = (0..8usize)
        .map(|i| l.get_shard_id(i).ok().map(sid))
        .collect();
    let mut accounts: Vec<AccountId> = PROBE_ACCOUNTS.iter().map(|a| a.parse().unwrap()).collect();
    if !matches!(l, ShardLayout::V0(_)) {
        accounts.extend(l.boundary_accounts().iter().cloned());
    }
    let sorted = matches!(l, ShardLayout::V0(_) | ShardLayout::V1(_))
        || l.boundary_accounts().windows(2).all(|w| w[0] <= w[1]);
    let shards: Vec<Option<u64>> = accounts
        .iter()
        .map(|a| if sorted { quiet(|| sid(l.account_id_to_shard_id(a))) } else { None })
        .collect();
    vec![
        ("version", hex(&l.version().to_le_bytes())),
        ("numShards", hex(&l.num_shards().to_le_bytes())),
        ("shardIndexes", hex(&ser(&indexes))),
        ("shardIds", hex(&ser(&ids))),
        ("accountShards", hex(&ser(&shards))),
    ]
}

// ----- validators -----

fn stake_amount(g: &mut G) -> Balance {
    let scale = 10u128.pow(18 + g.below(7) as u32);
    Balance::from_yoctonear(scale * (1 + g.below(1_000_000) as u128))
}

fn kickout_reason(g: &mut G, i: usize) -> ValidatorKickoutReason {
    match i % 8 {
        0 => ValidatorKickoutReason::_UnusedSlashed,
        1 => ValidatorKickoutReason::NotEnoughBlocks { produced: g.u64(), expected: g.u64() },
        2 => ValidatorKickoutReason::NotEnoughChunks { produced: g.u64(), expected: g.u64() },
        3 => ValidatorKickoutReason::Unstaked,
        4 => ValidatorKickoutReason::NotEnoughStake { stake: g.balance(), threshold: g.balance() },
        5 => ValidatorKickoutReason::DidNotGetASeat,
        6 => ValidatorKickoutReason::NotEnoughChunkEndorsements { produced: g.u64(), expected: g.u64() },
        _ => ValidatorKickoutReason::ProtocolVersionTooOld {
            version: g.u32(),
            network_version: g.u32(),
        },
    }
}

fn validator_stats(g: &mut G) -> ValidatorStats {
    ValidatorStats { produced: g.u64(), expected: g.u64() }
}

fn chunk_stats(g: &mut G) -> ChunkStats {
    ChunkStats { production: validator_stats(g), endorsement: validator_stats(g) }
}

/// The pieces that every `EpochInfo` version shares.
struct Parts {
    height: u64,
    validators: Vec<ValidatorStake>,
    to_index: HashMap<AccountId, u64>,
    bps: Vec<u64>,
    cps: Vec<Vec<u64>>,
    stake_change: BTreeMap<AccountId, Balance>,
    reward: HashMap<AccountId, Balance>,
    kickout: HashMap<AccountId, ValidatorKickoutReason>,
    minted: Balance,
    seat: Balance,
    version: u32,
}

fn parts(g: &mut G, min_validators: usize) -> Parts {
    let n = min_validators.max(g.below(10));
    let mut seen = HashSet::new();
    let mut validators = vec![];
    while validators.len() < n {
        let a = g.account();
        if seen.insert(a.clone()) {
            validators.push(ValidatorStake::new_v1(a, g.pk(), stake_amount(g)));
        }
    }
    let ids = |g: &mut G, max: usize| -> Vec<u64> {
        if n == 0 {
            return vec![];
        }
        (0..1 + g.below(max)).map(|_| g.below(n) as u64).collect()
    };
    let bps = ids(g, 2 * n.max(1));
    let cps = (0..1 + g.below(4)).map(|_| ids(g, n.max(1))).collect();
    let to_index = validators.iter().enumerate().map(|(i, v)| (v.account_id().clone(), i as u64)).collect();
    Parts {
        height: g.u64(),
        to_index,
        bps,
        cps,
        stake_change: g.vec(4, |g| (g.account(), g.balance())).into_iter().collect(),
        reward: g.vec(4, |g| (g.account(), g.balance())).into_iter().collect(),
        kickout: g
            .vec(5, |g| {
                let i = g.below(8);
                (g.account(), kickout_reason(g, i))
            })
            .into_iter()
            .collect(),
        minted: g.balance(),
        seat: stake_amount(g),
        version: g.u32(),
        validators,
    }
}

fn hidden(g: &mut G) -> Vec<ValidatorWeight> {
    g.vec(3, |g| {
        let mut b = g.u64().to_le_bytes().to_vec();
        b.extend(g.u64().to_le_bytes());
        ValidatorWeight::try_from_slice(&b).unwrap()
    })
}

fn mandates(g: &mut G, p: &Parts) -> ValidatorMandates {
    let config = ValidatorMandatesConfig::new(1 + g.below(20), p.cps.len());
    ValidatorMandates::new(config, &p.validators)
}

pub const N_EPOCH_INFO: usize = 5;

/// `EpochInfo` version `i + 1`.
pub fn epoch_info(g: &mut G, i: usize) -> EpochInfo {
    match i % N_EPOCH_INFO {
        0 => {
            let p = parts(g, 0);
            EpochInfo::V1(EpochInfoV1 {
                epoch_height: p.height,
                validators: p.validators.iter().map(|v| v.clone().into_v1()).collect(),
                validator_to_index: p.to_index,
                block_producers_settlement: p.bps,
                chunk_producers_settlement: p.cps,
                hidden_validators_settlement: hidden(g),
                fishermen: g.vec(2, stake_v1),
                fishermen_to_index: g.vec(2, |g| (g.account(), g.u64())).into_iter().collect(),
                stake_change: p.stake_change,
                validator_reward: p.reward,
                validator_kickout: p.kickout,
                minted_amount: p.minted,
                seat_price: p.seat,
                protocol_version: p.version,
            })
        }
        1 => {
            let p = parts(g, 0);
            EpochInfo::V2(v2(g, p))
        }
        2 => {
            // V3 stores private seed and samplers: build it from its bytes.
            let p = parts(g, 0);
            let (bp, cp) = samplers(&p);
            let mut b = vec![2u8];
            b.extend(ser(&v2(g, p)));
            b.extend(crate::chain::arr::<32>(g));
            b.extend(ser(&bp));
            b.extend(ser(&cp));
            EpochInfo::try_from_slice(&b).unwrap()
        }
        3 => versioned(g, 83),
        _ => versioned(g, 86),
    }
}

fn v2(g: &mut G, p: Parts) -> EpochInfoV2 {
    EpochInfoV2 {
        epoch_height: p.height,
        validators: p.validators,
        validator_to_index: p.to_index,
        block_producers_settlement: p.bps,
        chunk_producers_settlement: p.cps,
        hidden_validators_settlement: hidden(g),
        fishermen: g.vec(2, stake),
        fishermen_to_index: g.vec(2, |g| (g.account(), g.u64())).into_iter().collect(),
        stake_change: p.stake_change,
        validator_reward: p.reward,
        validator_kickout: p.kickout,
        minted_amount: p.minted,
        seat_price: p.seat,
        protocol_version: p.version,
    }
}

fn samplers(p: &Parts) -> (StakeWeightedIndex, Vec<StakeWeightedIndex>) {
    let weights = |ids: &[u64]| StakeWeightedIndex::new(ids.iter().map(|&i| p.validators[i as usize].stake()).collect());
    (weights(&p.bps), p.cps.iter().map(|c| weights(c)).collect())
}

/// V4 below protocol 85 and V5 from it, built by `EpochInfo::new`.
fn versioned(g: &mut G, protocol_version: u32) -> EpochInfo {
    let p = parts(g, 1);
    let mandates = mandates(g, &p);
    let i = g.below(N_LAYOUT);
    let layout = shard_layout(g, i);
    let seed = crate::chain::arr::<32>(g);
    let last = g.opt(|g| g.u64());
    let mut e = EpochInfo::new(
        p.height,
        p.validators,
        p.to_index,
        p.bps,
        p.cps,
        p.stake_change,
        p.reward,
        p.kickout,
        p.minted,
        p.seat,
        protocol_version,
        seed,
        mandates,
        layout,
        last,
    );
    if let EpochInfo::V4(v4) = &mut e {
        v4._hidden_validators_settlement = hidden(g);
        v4._fishermen = g.vec(2, stake);
        v4._fishermen_to_index = g.vec(2, |g| (g.account(), g.u64())).into_iter().collect();
    }
    e
}

fn epoch_fields(e: &EpochInfo) -> Vec<(&'static str, String)> {
    let accounts: Vec<AccountId> = (0..e.validators_len() as u64).map(|i| e.validator_account_id(i).clone()).collect();
    let mut probes = accounts.clone();
    probes.extend(["nobody.near".parse().unwrap(), "a.near".parse().unwrap()]);
    let ids: Vec<Option<u64>> = probes.iter().map(|a| e.get_validator_id(a).copied()).collect();
    let heights = sample_heights();
    let bp: Vec<Option<u64>> = heights.iter().map(|&h| quiet(|| e.sample_block_producer(h))).collect();
    // V1 to V4 have no layout of their own: the shard id is the index.
    let layout = match e.shard_layout() {
        Some(l) => l.clone(),
        None => ShardLayout::v0(e.chunk_producers_settlement().len() as u64, 0),
    };
    // Not the ids of a layout that claims a huge number of shards.
    let mut shards: Vec<u64> =
        if layout.num_shards() > 1000 { vec![] } else { layout.shard_ids().map(sid).collect() };
    shards.extend([e.chunk_producers_settlement().len() as u64, 1000, u64::MAX]);
    let cp: Vec<Option<u64>> = shards
        .iter()
        .flat_map(|&s| {
            heights.iter().map(move |&h| (s, h))
        })
        .map(|(s, h)| quiet(|| e.sample_chunk_producer(&layout, ShardId::new(s), h)).flatten())
        .collect();
    vec![
        ("validatorAccounts", hex(&ser(&accounts))),
        ("validatorIds", hex(&ser(&ids))),
        ("bp", hex(&ser(&bp))),
        ("cp", hex(&ser(&cp))),
        ("cv", chunk_validators(e)),
    ]
}

/// Chunk validators at a few heights; none for a mandates config that would allocate unboundedly.
fn chunk_validators(e: &EpochInfo) -> String {
    let m = ser(&e.validator_mandates());
    let num_shards = u64::from_le_bytes(m[8..16].try_into().unwrap());
    let count = u32::from_le_bytes(m[32..36].try_into().unwrap());
    if num_shards > 4096 || count > 1_000_000 {
        return String::new();
    }
    let all: Option<Vec<_>> = validator_heights()
        .iter()
        .map(|&h| quiet(|| e.sample_chunk_validators(h)))
        .collect();
    all.map(|v| hex(&ser(&v))).unwrap_or_default()
}

// ----- constructive checks -----

/// `StakeWeightedIndex::new` over a list of stakes.
#[derive(BorshSerialize, BorshDeserialize)]
struct Stakes(Vec<u128>);

/// `ValidatorMandates::new` over a config and validators. Decoding rejects the configs that
/// nearcore rejects by assertion or that overflow the mandates count of a validator.
struct MandatesInput {
    target: u64,
    num_shards: u64,
    validators: Vec<ValidatorStake>,
}

impl BorshSerialize for MandatesInput {
    fn serialize<W: borsh::io::Write>(&self, w: &mut W) -> borsh::io::Result<()> {
        self.target.serialize(w)?;
        self.num_shards.serialize(w)?;
        self.validators.serialize(w)
    }
}

impl BorshDeserialize for MandatesInput {
    fn deserialize_reader<R: borsh::io::Read>(r: &mut R) -> borsh::io::Result<Self> {
        let target = u64::deserialize_reader(r)?;
        let num_shards = u64::deserialize_reader(r)?;
        if num_shards == 0 || num_shards > 64 || target > 1000 {
            return Err(borsh::io::Error::new(borsh::io::ErrorKind::InvalidData, "mandates config"));
        }
        Ok(MandatesInput { target, num_shards, validators: Vec::deserialize_reader(r)? })
    }
}

/// A seed and a count, for `ChaCha20Rng` and `shuffle`. The count is at least 1 and at most 4096.
struct RngCase {
    seed: [u8; 32],
    n: u32,
}

impl BorshSerialize for RngCase {
    fn serialize<W: borsh::io::Write>(&self, w: &mut W) -> borsh::io::Result<()> {
        self.seed.serialize(w)?;
        self.n.serialize(w)
    }
}

impl BorshDeserialize for RngCase {
    fn deserialize_reader<R: borsh::io::Read>(r: &mut R) -> borsh::io::Result<Self> {
        let seed = <[u8; 32]>::deserialize_reader(r)?;
        let n = u32::deserialize_reader(r)?;
        if n == 0 || n > 4096 {
            return Err(borsh::io::Error::new(borsh::io::ErrorKind::InvalidData, "count"));
        }
        Ok(RngCase { seed, n })
    }
}

fn rng_fields(c: &RngCase) -> Vec<(&'static str, String)> {
    let mut r = ChaCha20Rng::from_seed(c.seed);
    let u32s: Vec<u8> = (0..200).flat_map(|_| r.next_u32().to_le_bytes()).collect();
    let mut r = ChaCha20Rng::from_seed(c.seed);
    let u64s: Vec<u8> = (0..100).flat_map(|_| r.next_u64().to_le_bytes()).collect();
    let mut r = ChaCha20Rng::from_seed(c.seed);
    let range: Vec<u8> = (0..60).flat_map(|_| r.gen_range(0..c.n).to_le_bytes()).collect();
    let mut r = ChaCha20Rng::from_seed(c.seed);
    let mut items: Vec<u32> = (0..c.n).collect();
    rand::seq::SliceRandom::shuffle(items.as_mut_slice(), &mut r);
    // The stream position after the shuffle.
    let after = r.next_u64();
    let shuffled: Vec<u8> = items.iter().flat_map(|x| x.to_le_bytes()).chain(after.to_le_bytes()).collect();
    vec![("u32s", hex(&u32s)), ("u64s", hex(&u64s)), ("range", hex(&range)), ("shuffle", hex(&shuffled))]
}

fn sampler_samples(s: &StakeWeightedIndex) -> String {
    let out: Option<Vec<u8>> = quiet(|| {
        (0..40u32)
            .flat_map(|i| (s.sample(hash(&i.to_le_bytes()).0) as u64).to_le_bytes())
            .collect()
    });
    out.map(|b| hex(&b)).unwrap_or_default()
}

// ----- block info and epoch sync -----

pub const N_BLOCK_INFO: usize = 5;

fn epoch_id_(g: &mut G) -> near_primitives::types::EpochId {
    epoch_id(g)
}

#[allow(deprecated)]
pub fn block_info(g: &mut G, i: usize) -> BlockInfo {
    let slashed = |g: &mut G| -> HashMap<AccountId, SlashState> {
        g.vec(3, |g| {
            let s = match g.below(3) {
                0 => SlashState::DoubleSign,
                1 => SlashState::AlreadySlashed,
                _ => SlashState::Other,
            };
            (g.account(), s)
        })
        .into_iter()
        .collect()
    };
    let (hash, height, lf, lb, prev, first) = (g.hash(), g.u64(), g.u64(), g.hash(), g.hash(), g.hash());
    let (eid, mask, lpv, supply, ts) = (epoch_id_(g), g.vec(6, |g| g.bool()), g.u32(), g.balance(), g.u64());
    match i % N_BLOCK_INFO {
        0 => BlockInfo::V1(BlockInfoV1 {
            hash, height, last_finalized_height: lf, last_final_block_hash: lb, prev_hash: prev,
            epoch_first_block: first, epoch_id: eid, proposals: g.vec(3, stake_v1), chunk_mask: mask,
            latest_protocol_version: lpv, slashed: slashed(g), total_supply: supply, timestamp_nanosec: ts,
        }),
        1 => BlockInfo::V2(BlockInfoV2 {
            hash, height, last_finalized_height: lf, last_final_block_hash: lb, prev_hash: prev,
            epoch_first_block: first, epoch_id: eid, proposals: g.vec(3, stake), chunk_mask: mask,
            latest_protocol_version: lpv, slashed: slashed(g), total_supply: supply, timestamp_nanosec: ts,
        }),
        2 => BlockInfo::V3(BlockInfoV3 {
            hash, height, last_finalized_height: lf, last_final_block_hash: lb, prev_hash: prev,
            epoch_first_block: first, epoch_id: eid, proposals: g.vec(3, stake), chunk_mask: mask,
            latest_protocol_version: lpv, slashed: slashed(g), total_supply: supply, timestamp_nanosec: ts,
            chunk_endorsements: endorsements_bitmap(g),
        }),
        3 => BlockInfo::V4(BlockInfoV4 {
            hash, height, last_finalized_height: lf, last_final_block_hash: lb, prev_hash: prev,
            epoch_first_block: first, epoch_id: eid, proposals: g.vec(3, stake), chunk_mask: mask,
            latest_protocol_version: lpv, total_supply: supply, timestamp_nanosec: ts,
            chunk_endorsements: endorsements_bitmap(g),
            shard_split: g.opt(|g| (shard(g), g.account())),
        }),
        _ => BlockInfo::V5(BlockInfoV5 {
            hash, height, last_finalized_height: lf, last_final_block_hash: lb, prev_hash: prev,
            epoch_first_block: first, epoch_id: eid, proposals: g.vec(3, stake), chunk_mask: mask,
            latest_protocol_version: lpv, total_supply: supply, timestamp_nanosec: ts,
            chunk_endorsements: endorsements_bitmap(g),
            shard_split: g.opt(|g| (shard(g), g.account())),
            last_certified_block_epoch: epoch_id_(g),
            spice_chunk_endorsement_stats: endorsement_stats(g),
        }),
    }
}

fn block_info_fields(b: &BlockInfo) -> Vec<(&'static str, String)> {
    vec![
        ("hash", h(b.hash())),
        ("height", hex(&b.height().to_le_bytes())),
        ("prevHash", h(b.prev_hash())),
        ("epochId", h(&b.epoch_id().0)),
        ("isGenesis", hex(&[b.is_genesis() as u8])),
    ]
}

fn sync_epoch_data(g: &mut G) -> EpochSyncProofEpochData {
    let i = g.below(N_BLOCK_HEADER);
    EpochSyncProofEpochData {
        block_producers: g.vec(3, stake),
        use_versioned_bp_hash_format: g.bool(),
        last_final_block_header: Arc::new(header_parts(g, i)),
        this_epoch_endorsements_for_last_final_block: approvals(g),
    }
}

fn sync_last_epoch(g: &mut G) -> EpochSyncProofLastEpochData {
    let info = |g: &mut G| {
        let i = g.below(N_EPOCH_INFO);
        epoch_info(g, i)
    };
    let block = |g: &mut G| {
        let i = g.below(N_BLOCK_INFO);
        block_info(g, i)
    };
    EpochSyncProofLastEpochData {
        epoch_info: info(g),
        next_epoch_info: info(g),
        next_next_epoch_info: info(g),
        first_block_in_epoch: block(g),
        last_block_in_epoch: block(g),
        second_last_block_in_epoch: block(g),
    }
}

fn sync_current_epoch(g: &mut G) -> EpochSyncProofCurrentEpochData {
    let header = |g: &mut G| {
        let i = g.below(N_BLOCK_HEADER);
        Arc::new(header_parts(g, i))
    };
    EpochSyncProofCurrentEpochData {
        first_block_header_in_epoch: header(g),
        last_block_header_in_prev_epoch: header(g),
        second_last_block_header_in_prev_epoch: header(g),
        merkle_proof_for_first_block: merkle_path(g),
        partial_merkle_tree_for_first_block: partial_merkle_tree(g),
    }
}

fn sync_proof(g: &mut G) -> EpochSyncProof {
    EpochSyncProof::V1(EpochSyncProofV1 {
        all_epochs: g.vec(3, sync_epoch_data),
        last_epoch: sync_last_epoch(g),
        current_epoch: sync_current_epoch(g),
    })
}

pub fn epoch(m: &mut Manifest, dir: &PathBuf) {
    install_quiet_hook();

    let mut f = Fam::<near_primitives::shard_layout::ShardUId>::new("ShardUId", SEED);
    f.rand(10, |g| near_primitives::shard_layout::ShardUId { version: g.u32(), shard_id: g.u32() });
    f.finish(m, dir);

    let mut f = Fam::<ShardLayout>::new("ShardLayout", SEED);
    f.hash(layout_fields);
    f.edge("single", ShardLayout::single_shard());
    for i in 0..N_LAYOUT {
        f.edge(&format!("variant-{i}"), shard_layout(&mut eg(&format!("layout-edge-{i}")), i));
    }
    f.rand(50, |g| {
        let i = g.below(N_LAYOUT);
        shard_layout(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<ValidatorKickoutReason>::new("ValidatorKickoutReason", SEED);
    for i in 0..8 {
        f.edge(&format!("variant-{i}"), kickout_reason(&mut eg(&format!("kick-edge-{i}")), i));
    }
    f.rand(20, |g| {
        let i = g.below(8);
        kickout_reason(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<ValidatorStats>::new("ValidatorStats", SEED);
    f.rand(10, validator_stats);
    f.finish(m, dir);
    let mut f = Fam::<ChunkStats>::new("ChunkStats", SEED);
    f.rand(10, chunk_stats);
    f.finish(m, dir);
    let mut f = Fam::<BlockChunkValidatorStats>::new("BlockChunkValidatorStats", SEED);
    f.rand(10, |g| BlockChunkValidatorStats { block_stats: validator_stats(g), chunk_stats: chunk_stats(g) });
    f.finish(m, dir);
    let mut f = Fam::<SlashState>::new("SlashState", SEED);
    f.edge("double-sign", SlashState::DoubleSign);
    f.edge("already-slashed", SlashState::AlreadySlashed);
    f.edge("other", SlashState::Other);
    f.finish(m, dir);

    let mut f = Fam::<ValidatorWeight>::new("ValidatorWeight", SEED);
    f.rand(8, |g| hidden(g).into_iter().next().unwrap_or_default());
    f.finish(m, dir);

    // The alias tables built from a list of stakes (no mutations: they would overflow).
    let mut f = Fam::<Stakes>::new("StakeWeights", SEED);
    f.hash(|s: &Stakes| {
        let built = quiet(|| StakeWeightedIndex::new(s.0.iter().map(|&x| Balance::from_yoctonear(x)).collect()));
        vec![("hash", built.map(|i| hex(&ser(&i))).unwrap_or_default())]
    });
    // The example of https://www.keithschwarz.com/darts-dice-coins/ used by nearcore's tests.
    f.raw("darts-and-dice", ser(&Stakes(vec![5, 8, 4, 10, 4, 4, 5])));
    f.raw("empty", ser(&Stakes(vec![])));
    f.raw("one", ser(&Stakes(vec![7])));
    f.raw("zeros", ser(&Stakes(vec![0, 0, 3])));
    f.raw("overflow-sum", ser(&Stakes(vec![u128::MAX, 1])));
    f.raw("overflow-scale", ser(&Stakes(vec![1 << 127, 1 << 127, 0])));
    f.raw("trunc", ser(&Stakes(vec![5, 8]))[..20].to_vec());
    f.raw("trailing", {
        let mut b = ser(&Stakes(vec![5, 8]));
        b.push(0);
        b
    });
    f.rand_with(40, 0, |g| {
        let n = g.below(30);
        Stakes((0..n).map(|_| stake_amount(g).as_yoctonear()).collect())
    });
    f.rand_with(10, 0, |g| Stakes((0..1 + g.below(8)).map(|_| 1 + g.below(5) as u128).collect()));
    f.finish(m, dir);

    let mut f = Fam::<StakeWeightedIndex>::new("StakeWeightedIndex", SEED);
    f.hash(|s: &StakeWeightedIndex| vec![("samples", sampler_samples(s))]);
    f.edge("darts-and-dice", StakeWeightedIndex::new([5u128, 8, 4, 10, 4, 4, 5].iter().map(|&x| Balance::from_yoctonear(x)).collect()));
    f.edge("empty", StakeWeightedIndex::default());
    f.rand(25, |g| {
        let n = 1 + g.below(12);
        StakeWeightedIndex::new((0..n).map(|_| stake_amount(g)).collect())
    });
    f.finish(m, dir);

    let mut f = Fam::<ValidatorMandatesConfig>::new("ValidatorMandatesConfig", SEED);
    f.edge("default", ValidatorMandatesConfig::default());
    f.rand(8, |g| ValidatorMandatesConfig::new(g.below(1000), 1 + g.below(8)));
    f.finish(m, dir);

    let mut f = Fam::<ValidatorMandates>::new("ValidatorMandates", SEED);
    f.edge("default", ValidatorMandates::default());
    f.rand(15, |g| {
        let p = parts(g, 1);
        mandates(g, &p)
    });
    f.finish(m, dir);

    let mut f = Fam::<MandatesInput>::new("MandatesInput", SEED);
    f.hash(|i: &MandatesInput| {
        let built = quiet(|| {
            ValidatorMandates::new(ValidatorMandatesConfig::new(i.target as usize, i.num_shards as usize), &i.validators)
        });
        vec![("hash", built.map(|m| hex(&ser(&m))).unwrap_or_default())]
    });
    let input = |target: u64, num_shards: u64, stakes: &[u128]| {
        ser(&MandatesInput {
            target,
            num_shards,
            validators: stakes
                .iter()
                .enumerate()
                .map(|(i, &s)| ValidatorStake::new_v1(format!("account_{i}").parse().unwrap(), near_crypto::PublicKey::empty(near_crypto::KeyType::ED25519), Balance::from_yoctonear(s)))
                .collect(),
        })
    };
    // The example of nearcore's tests: 12 mandates at price 8.
    f.raw("nearcore-test", input(3, 4, &[30, 27, 9, 12, 35, 4, 6]));
    f.raw("small-total", input(1000, 1, &[100]));
    f.raw("equal", input(13, 1, &[11; 13]));
    f.raw("one-validator", input(5, 2, &[1_000_000]));
    f.raw("no-validators", input(5, 2, &[]));
    f.raw("zero-stake", input(5, 2, &[0, 0]));
    f.raw("zero-shards", input(5, 0, &[1, 2]));
    f.raw("huge-target", input(5000, 2, &[1, 2]));
    f.rand_with(40, 0, |g| {
        let p = parts(g, 1);
        MandatesInput { target: 1 + g.below(40) as u64, num_shards: 1 + g.below(4) as u64, validators: p.validators }
    });
    f.finish(m, dir);

    let mut f = Fam::<RngCase>::new("RngCase", SEED);
    f.hash(rng_fields);
    for n in [1u32, 2, 3, 5, 7, 16, 100, 255, 256, 257, 1000, 3000] {
        f.raw(&format!("n-{n}"), ser(&RngCase { seed: [n as u8; 32], n }));
    }
    f.raw("zero-count", ser(&RngCase { seed: [1; 32], n: 0 }));
    f.raw("huge-count", ser(&RngCase { seed: [1; 32], n: 4097 }));
    f.rand_with(14, 0, |g| RngCase { seed: crate::chain::arr::<32>(g), n: 1 + g.below(150) as u32 });
    f.finish(m, dir);

    let mut f = Fam::<EpochInfo>::new("EpochInfo", SEED);
    f.hash(epoch_fields);
    f.mutate_up_to(3000);
    for i in 0..N_EPOCH_INFO {
        f.edge(&format!("variant-{i}"), epoch_info(&mut eg(&format!("epoch-edge-{i}")), i));
    }
    f.rand_with(60, 12, |g| {
        let i = g.below(N_EPOCH_INFO);
        epoch_info(g, i)
    });
    f.raw("tag5", {
        let mut b = ser(&epoch_info(&mut eg("epoch-tag5"), 3));
        b[0] = 5;
        b
    });
    f.finish(m, dir);

    let mut f = Fam::<BlockInfo>::new("BlockInfo", SEED);
    f.hash(block_info_fields);
    for i in 0..N_BLOCK_INFO {
        f.edge(&format!("variant-{i}"), block_info(&mut eg(&format!("bi-edge-{i}")), i));
    }
    f.rand(60, |g| {
        let i = g.below(N_BLOCK_INFO);
        block_info(g, i)
    });
    f.finish(m, dir);

    let mut f = Fam::<EpochSummary>::new("EpochSummary", SEED);
    f.rand(20, |g| EpochSummary {
        prev_epoch_last_block_hash: g.hash(),
        all_proposals: g.vec(3, stake),
        validator_kickout: g
            .vec(4, |g| {
                let i = g.below(8);
                (g.account(), kickout_reason(g, i))
            })
            .into_iter()
            .collect(),
        validator_block_chunk_stats: g
            .vec(4, |g| (g.account(), BlockChunkValidatorStats { block_stats: validator_stats(g), chunk_stats: chunk_stats(g) }))
            .into_iter()
            .collect(),
        next_next_epoch_version: g.u32(),
    });
    f.finish(m, dir);

    let mut f = Fam::<EpochSyncProofEpochData>::new("EpochSyncProofEpochData", SEED);
    f.rand_with(15, 3, sync_epoch_data);
    f.finish(m, dir);

    let mut f = Fam::<EpochSyncProofLastEpochData>::new("EpochSyncProofLastEpochData", SEED);
    f.hash(|d: &EpochSyncProofLastEpochData| vec![("hash", h(&d.compute_epoch_sync_data_hash()))]);
    f.mutate_up_to(12000);
    f.rand_with(10, 2, sync_last_epoch);
    f.finish(m, dir);

    let mut f = Fam::<EpochSyncProofCurrentEpochData>::new("EpochSyncProofCurrentEpochData", SEED);
    f.rand_with(10, 3, sync_current_epoch);
    f.finish(m, dir);

    let mut f = Fam::<EpochSyncProof>::new("EpochSyncProof", SEED);
    f.mutate_up_to(30000);
    f.rand_with(8, 2, sync_proof);
    f.finish(m, dir);

    let mut f = Fam::<CompressedEpochSyncProof>::new("CompressedEpochSyncProof", SEED);
    f.edge("proof", CompressedEpochSyncProof::encode(&sync_proof(&mut eg("compressed"))).unwrap().0);
    f.rand(8, |g| CompressedEpochSyncProof::from(g.bytes(200).into_boxed_slice()));
    f.finish(m, dir);

}
