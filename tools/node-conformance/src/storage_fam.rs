//! The M4a storage-layer families: trie keys with their on-trie bytes, value references, flat
//! state values, the state change types and the raw trie nodes.
//!
//! `RawTrieNode` and `RawTrieNodeWithSize` live in `near-store`, which this crate does not link;
//! their definitions are copied from `core/store/src/trie/raw_node.rs` at the pinned revision
//! (Borsh layout, including the `Children` bitmap encoding). The Lean side also checks every
//! node hash against real trie roots of the M3 corpus, which nearcore produced.
use crate::fam::{hex, Fam, Manifest};
use crate::rng::G;
use crate::SEED;
use borsh::{BorshDeserialize, BorshSerialize};
use near_crypto::{KeyType, PublicKeyHandle};
use near_primitives::hash::{hash, CryptoHash, YieldId};
use near_primitives::state::{FlatStateValue, ValueRef};
use near_primitives::trie_key::{GlobalContractCodeIdentifier, TrieKey};
use near_primitives::types::{
    RawStateChange, RawStateChangesWithTrieKey, StateChangeCause, StateChangesForBlock,
    StateChangesForBlockRange, StateChangesForShard,
};
use near_primitives_core::types::ShardId;
use near_primitives::shard_layout::ShardUId;
use std::collections::HashMap;
use std::path::PathBuf;

fn handle(g: &mut G) -> PublicKeyHandle {
    let ty = g.key_type();
    PublicKeyHandle::from(&g.pk_of(ty))
}

fn identifier(g: &mut G) -> GlobalContractCodeIdentifier {
    if g.bool() {
        GlobalContractCodeIdentifier::CodeHash(g.hash())
    } else {
        GlobalContractCodeIdentifier::AccountId(g.account())
    }
}

fn shard(g: &mut G) -> ShardId {
    ShardId::new(if g.below(3) == 0 { g.u64() } else { g.below(70000) as u64 })
}

pub fn trie_key(g: &mut G, i: usize) -> TrieKey {
    match i % 24 {
        0 => TrieKey::Account { account_id: g.account() },
        1 => TrieKey::ContractCode { account_id: g.account() },
        2 => TrieKey::AccessKey { account_id: g.account(), key_handle: handle(g) },
        3 => TrieKey::ReceivedData { receiver_id: g.account(), data_id: g.hash() },
        4 => TrieKey::PostponedReceiptId { receiver_id: g.account(), data_id: g.hash() },
        5 => TrieKey::PendingDataCount { receiver_id: g.account(), receipt_id: g.hash() },
        6 => TrieKey::PostponedReceipt { receiver_id: g.account(), receipt_id: g.hash() },
        7 => TrieKey::DelayedReceiptIndices,
        8 => TrieKey::DelayedReceipt { index: g.u64() },
        9 => TrieKey::ContractData { account_id: g.account(), key: g.bytes(40) },
        10 => TrieKey::PromiseYieldIndices,
        11 => TrieKey::PromiseYieldTimeout { index: g.u64() },
        12 => TrieKey::PromiseYieldReceipt { receiver_id: g.account(), data_id: g.hash() },
        13 => TrieKey::BufferedReceiptIndices,
        14 => TrieKey::BufferedReceipt {
            receiving_shard: ShardId::new(g.below(70000).min(65535) as u64),
            index: g.u64(),
        },
        15 => TrieKey::BandwidthSchedulerState,
        16 => TrieKey::BufferedReceiptGroupsQueueData { receiving_shard: shard(g) },
        17 => TrieKey::BufferedReceiptGroupsQueueItem { receiving_shard: shard(g), index: g.u64() },
        18 => TrieKey::GlobalContractCode { identifier: identifier(g) },
        19 => TrieKey::GlobalContractNonce { identifier: identifier(g) },
        20 => TrieKey::PromiseYieldStatus { receiver_id: g.account(), data_id: g.hash() },
        21 => TrieKey::YieldIdToDataId { receiver_id: g.account(), yield_id: YieldId(g.hash()) },
        22 => TrieKey::DataIdToYieldId { receiver_id: g.account(), data_id: g.hash() },
        _ => TrieKey::GasKeyNonce {
            account_id: g.account(),
            key_handle: handle(g),
            index: g.u16(),
        },
    }
}

/// `to_vec` panics for a receiving shard that does not fit a `u16`: no value then.
fn key_hex(k: &TrieKey) -> String {
    if let TrieKey::BufferedReceipt { receiving_shard, .. } = k {
        let s: u64 = (*receiving_shard).into();
        if s > u16::MAX as u64 {
            return String::new();
        }
    }
    hex(&k.to_vec())
}

fn cause(g: &mut G, i: usize) -> StateChangeCause {
    match i % 12 {
        0 => StateChangeCause::NotWritableToDisk,
        1 => StateChangeCause::InitialState,
        2 => StateChangeCause::TransactionProcessing { tx_hash: g.hash() },
        3 => StateChangeCause::ActionReceiptProcessingStarted { receipt_hash: g.hash() },
        4 => StateChangeCause::ActionReceiptGasReward { receipt_hash: g.hash() },
        5 => StateChangeCause::ReceiptProcessing { receipt_hash: g.hash() },
        6 => StateChangeCause::PostponedReceipt { receipt_hash: g.hash() },
        7 => StateChangeCause::UpdatedDelayedReceipts,
        8 => StateChangeCause::ValidatorAccountsUpdate,
        9 => StateChangeCause::Migration,
        10 => StateChangeCause::_UnusedReshardingV2,
        _ => StateChangeCause::BandwidthSchedulerStateUpdate,
    }
}

fn raw_change(g: &mut G) -> RawStateChange {
    let i = g.below(12);
    RawStateChange { cause: cause(g, i), data: g.opt(|g| g.bytes(50)) }
}

fn changes_with_key(g: &mut G) -> RawStateChangesWithTrieKey {
    let i = g.below(24);
    RawStateChangesWithTrieKey { trie_key: trie_key(g, i), changes: g.vec(3, raw_change) }
}

fn changes_for_shard(g: &mut G) -> StateChangesForShard {
    StateChangesForShard { shard_id: shard(g), state_changes: g.vec(3, changes_with_key) }
}

fn changes_for_block(g: &mut G) -> StateChangesForBlock {
    StateChangesForBlock { block_hash: g.hash(), state_changes: g.vec(3, changes_for_shard) }
}

fn value_ref(g: &mut G) -> ValueRef {
    if g.bool() {
        ValueRef::new(&g.bytes(60))
    } else {
        ValueRef { length: g.u32(), hash: g.hash() }
    }
}

// ---- copied from core/store/src/trie/raw_node.rs ----

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Children(pub [Option<CryptoHash>; 16]);

impl BorshSerialize for Children {
    fn serialize<W: borsh::io::Write>(&self, wr: &mut W) -> borsh::io::Result<()> {
        let mut bitmap: u16 = 0;
        let mut pos: u16 = 1;
        for child in &self.0 {
            if child.is_some() {
                bitmap |= pos
            }
            pos <<= 1;
        }
        bitmap.serialize(wr)?;
        self.0.iter().filter_map(Option::as_ref).map(|child| child.serialize(wr)).collect()
    }
}

impl BorshDeserialize for Children {
    fn deserialize_reader<R: borsh::io::Read>(rd: &mut R) -> borsh::io::Result<Self> {
        let mut bitmap = u16::deserialize_reader(rd)?;
        let mut children = Self([None; 16]);
        while bitmap != 0 {
            let idx = bitmap.trailing_zeros() as usize;
            bitmap &= bitmap - 1;
            children.0[idx] = Some(CryptoHash::deserialize_reader(rd)?);
        }
        Ok(children)
    }
}

#[derive(BorshSerialize, BorshDeserialize, Clone, Debug, PartialEq, Eq)]
#[borsh(use_discriminant = true)]
#[repr(u8)]
pub enum RawTrieNode {
    Leaf(Vec<u8>, ValueRef) = 0,
    BranchNoValue(Children) = 1,
    BranchWithValue(ValueRef, Children) = 2,
    Extension(Vec<u8>, CryptoHash) = 3,
}

#[derive(BorshSerialize, BorshDeserialize, Clone, Debug, PartialEq, Eq)]
pub struct RawTrieNodeWithSize {
    pub node: RawTrieNode,
    pub memory_usage: u64,
}

// ---- end of copy ----


// ---- copied from core/store/src/flat/{types,delta}.rs ----

#[derive(BorshSerialize, BorshDeserialize, Debug, Copy, Clone, PartialEq, Eq)]
pub struct BlockInfo {
    pub hash: CryptoHash,
    pub height: u64,
    pub prev_hash: CryptoHash,
}

#[derive(BorshSerialize, BorshDeserialize, Debug, Clone, Copy)]
pub struct BlockWithChangesInfo {
    pub hash: CryptoHash,
    pub height: u64,
}

#[derive(BorshSerialize, BorshDeserialize, Debug, Clone, Copy)]
pub struct FlatStateDeltaMetadata {
    pub block: BlockInfo,
    pub prev_block_with_changes: Option<BlockWithChangesInfo>,
}

#[derive(BorshSerialize, BorshDeserialize, Debug)]
pub struct KeyForFlatStateDelta {
    pub shard_uid: ShardUId,
    pub block_hash: CryptoHash,
}

#[derive(BorshSerialize, BorshDeserialize, Clone, Default, PartialEq, Eq)]
pub struct FlatStateChanges(pub HashMap<Vec<u8>, Option<FlatStateValue>>);

#[derive(BorshSerialize, BorshDeserialize, Debug, PartialEq, Eq, Clone)]
pub struct FlatStorageReadyStatus {
    pub flat_head: BlockInfo,
}

/// The variants a node uses: the full enum also has `Creation = 2` (deprecated) and
/// `Resharding = 4`, which this copy omits.
#[derive(BorshSerialize, BorshDeserialize, Debug, PartialEq, Eq, Clone)]
#[borsh(use_discriminant = true)]
#[repr(u8)]
pub enum FlatStorageStatus {
    Disabled = 0,
    Empty = 1,
    Ready(FlatStorageReadyStatus) = 3,
}

// ---- end of copy ----

fn block_info(g: &mut G) -> BlockInfo {
    BlockInfo { hash: g.hash(), height: g.u64(), prev_hash: g.hash() }
}

fn delta_metadata(g: &mut G) -> FlatStateDeltaMetadata {
    FlatStateDeltaMetadata {
        block: block_info(g),
        prev_block_with_changes: g.opt(|g| BlockWithChangesInfo { hash: g.hash(), height: g.u64() }),
    }
}

fn flat_changes(g: &mut G) -> FlatStateChanges {
    FlatStateChanges(
        g.vec(5, |g| {
            let k = g.bytes(12);
            let v = g.opt(|g| {
                if g.bool() { FlatStateValue::Ref(value_ref(g)) } else { FlatStateValue::Inlined(g.bytes(40)) }
            });
            (k, v)
        })
        .into_iter()
        .collect(),
    )
}

fn shard_uid(g: &mut G) -> ShardUId {
    ShardUId { version: g.u32(), shard_id: g.u32() }
}

fn children(g: &mut G) -> Children {
    let mut c = Children([None; 16]);
    for slot in c.0.iter_mut() {
        if g.below(4) == 0 {
            *slot = Some(g.hash());
        }
    }
    c
}

fn raw_node(g: &mut G, i: usize) -> RawTrieNodeWithSize {
    let node = match i % 4 {
        0 => RawTrieNode::Leaf(g.bytes(12), value_ref(g)),
        1 => RawTrieNode::BranchNoValue(children(g)),
        2 => RawTrieNode::BranchWithValue(value_ref(g), children(g)),
        _ => RawTrieNode::Extension(g.bytes(12), g.hash()),
    };
    RawTrieNodeWithSize { node, memory_usage: g.u64() }
}

pub fn storage(m: &mut Manifest, dir: &PathBuf) {
    let mut f = Fam::<TrieKey>::new("TrieKey", SEED);
    f.hash(|k| vec![("key", key_hex(k))]);
    for i in 0..24 {
        let mut g = G::new(SEED, &format!("TrieKey/edge{i}"));
        f.edge(&format!("variant-{i}"), trie_key(&mut g, i));
    }
    f.edge("empty-data-key", TrieKey::ContractData { account_id: "ab".parse().unwrap(), key: vec![] });
    f.edge(
        "separator-in-data-key",
        TrieKey::ContractData { account_id: "ab".parse().unwrap(), key: b",,\x02".to_vec() },
    );
    f.edge("shard-max", TrieKey::BufferedReceipt { receiving_shard: ShardId::new(65535), index: u64::MAX });
    f.edge(
        "shard-over",
        TrieKey::BufferedReceipt { receiving_shard: ShardId::new(65536), index: 0 },
    );
    f.rand(120, |g| {
        let i = g.below(24);
        trie_key(g, i)
    });
    f.raw("tag24", vec![24, 0, 0, 0, 0]);
    f.raw("tag255", vec![255]);
    f.raw("tag8-short", vec![8, 1, 2, 3]);
    f.finish(m, dir);

    let mut f = Fam::<ValueRef>::new("ValueRef", SEED);
    f.hash(|v| vec![("hash", hex(&v.hash.0))]);
    f.edge("empty", ValueRef::new(&[]));
    f.edge("abc", ValueRef::new(b"abc"));
    f.rand(40, value_ref);
    f.finish(m, dir);

    let mut f = Fam::<FlatStateValue>::new("FlatStateValue", SEED);
    f.hash(|v| {
        let r = v.to_value_ref();
        vec![("hash", hex(&r.hash.0)), ("length", hex(&r.length.to_le_bytes()))]
    });
    f.edge("inline-empty", FlatStateValue::Inlined(vec![]));
    f.edge("ref", FlatStateValue::value_ref(b"abc"));
    f.edge("on-disk-small", FlatStateValue::on_disk(&[7; 4000]));
    f.edge("on-disk-threshold", FlatStateValue::on_disk(&vec![7; FlatStateValue::INLINE_DISK_VALUE_THRESHOLD]));
    f.edge(
        "on-disk-over-threshold",
        FlatStateValue::on_disk(&vec![7; FlatStateValue::INLINE_DISK_VALUE_THRESHOLD + 1]),
    );
    f.rand(40, |g| {
        if g.bool() {
            FlatStateValue::Ref(value_ref(g))
        } else {
            FlatStateValue::Inlined(g.bytes(60))
        }
    });
    f.raw("tag2", vec![2, 0, 0, 0, 0]);
    f.finish(m, dir);

    let mut f = Fam::<StateChangeCause>::new("StateChangeCause", SEED);
    for i in 0..12 {
        let mut g = G::new(SEED, &format!("StateChangeCause/edge{i}"));
        f.edge(&format!("variant-{i}"), cause(&mut g, i));
    }
    f.raw("tag12", vec![12]);
    f.raw("tag255", vec![255]);
    f.finish(m, dir);

    let mut f = Fam::<RawStateChange>::new("RawStateChange", SEED);
    f.edge("deletion", RawStateChange { cause: StateChangeCause::InitialState, data: None });
    f.rand(30, raw_change);
    f.finish(m, dir);

    let mut f = Fam::<RawStateChangesWithTrieKey>::new("RawStateChangesWithTrieKey", SEED);
    f.rand(60, changes_with_key);
    f.finish(m, dir);

    let mut f = Fam::<StateChangesForShard>::new("StateChangesForShard", SEED);
    f.rand(20, changes_for_shard);
    f.finish(m, dir);

    let mut f = Fam::<StateChangesForBlock>::new("StateChangesForBlock", SEED);
    f.edge("empty", StateChangesForBlock { block_hash: CryptoHash::default(), state_changes: vec![] });
    f.rand(20, changes_for_block);
    f.finish(m, dir);

    let mut f = Fam::<StateChangesForBlockRange>::new("StateChangesForBlockRange", SEED);
    f.edge("empty", StateChangesForBlockRange { blocks: vec![] });
    f.rand(10, |g| StateChangesForBlockRange { blocks: g.vec(3, changes_for_block) });
    f.finish(m, dir);

    let mut f = Fam::<RawTrieNodeWithSize>::new("RawTrieNodeWithSize", SEED);
    f.hash(|n| vec![("hash", hex(&hash(&borsh::to_vec(n).unwrap()).0))]);
    for i in 0..4 {
        let mut g = G::new(SEED, &format!("RawTrieNodeWithSize/edge{i}"));
        f.edge(&format!("variant-{i}"), raw_node(&mut g, i));
    }
    let mut full = Children([None; 16]);
    for (i, c) in full.0.iter_mut().enumerate() {
        *c = Some(CryptoHash([i as u8; 32]));
    }
    f.edge("full-branch", RawTrieNodeWithSize { node: RawTrieNode::BranchNoValue(full), memory_usage: 42 });
    f.edge(
        "empty-leaf",
        RawTrieNodeWithSize { node: RawTrieNode::Leaf(vec![], ValueRef::new(&[])), memory_usage: 1 },
    );
    f.rand(80, |g| {
        let i = g.below(4);
        raw_node(g, i)
    });
    // bitmap bits beyond the children present, and a branch without children
    let mut empty_branch = vec![1u8, 0, 0];
    empty_branch.extend(42u64.to_le_bytes());
    f.raw("branch-no-children", empty_branch);
    f.raw("tag4", vec![4; 60]);
    f.finish(m, dir);

    let mut f = Fam::<BlockInfo>::new("FlatBlockInfo", SEED);
    f.rand(20, block_info);
    f.finish(m, dir);

    let mut f = Fam::<FlatStateDeltaMetadata>::new("FlatStateDeltaMetadata", SEED);
    f.rand(30, delta_metadata);
    f.raw("tag2", {
        let mut b = vec![0u8; 72];
        b.push(2);
        b
    });
    f.finish(m, dir);

    let mut f = Fam::<FlatStateChanges>::new("FlatStateChanges", SEED);
    f.edge("empty", FlatStateChanges::default());
    f.rand(30, flat_changes);
    // unsorted entries decode and re-encode sorted
    let entry = |k: u8| {
        let mut b = vec![1, 0, 0, 0, k];
        b.push(0);
        b
    };
    let mut unsorted = 2u32.to_le_bytes().to_vec();
    unsorted.extend(entry(9));
    unsorted.extend(entry(3));
    f.raw("unsorted", unsorted);
    f.finish(m, dir);

    let mut f = Fam::<KeyForFlatStateDelta>::new("KeyForFlatStateDelta", SEED);
    f.hash(|k| {
        let mut key = k.shard_uid.to_bytes().to_vec();
        key.extend(k.block_hash.as_bytes());
        vec![("key", hex(&key))]
    });
    f.rand(20, |g| KeyForFlatStateDelta { shard_uid: shard_uid(g), block_hash: g.hash() });
    f.finish(m, dir);

    let mut f = Fam::<FlatStorageStatus>::new("FlatStorageStatus", SEED);
    f.edge("disabled", FlatStorageStatus::Disabled);
    f.edge("empty", FlatStorageStatus::Empty);
    f.rand(20, |g| FlatStorageStatus::Ready(FlatStorageReadyStatus { flat_head: block_info(g) }));
    f.raw("tag5", vec![5]);
    f.finish(m, dir);

    let mut f = Fam::<ShardUId>::new("ShardUIdKey", SEED);
    f.hash(|u| vec![("key", hex(&u.to_bytes()))]);
    f.rand(20, shard_uid);
    f.finish(m, dir);

    let _ = KeyType::ED25519;
}
