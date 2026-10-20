//! Lossless JSON/Borsh adapter around the pinned, trie-backed Runtime::apply.
//! The build overlay adds this binary target without changing runtime code.
use borsh::{BorshDeserialize, BorshSerialize, from_slice, to_vec as borsh_bytes};
use near_crypto::{InMemorySigner, KeyType, PublicKey};
use near_parameters::RuntimeConfigStore;
use near_primitives::account::{AccessKey, Account, AccountContract};
use near_primitives::action::{Action, CreateAccountAction, TransferAction};
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::BlockBandwidthRequests;
use near_primitives::congestion_info::{BlockCongestionInfo, ExtendedCongestionInfo};
use near_primitives::hash::CryptoHash;
use near_primitives::receipt::Receipt;
use near_primitives::state_record::StateRecord;
use near_primitives::test_utils::MockEpochInfoProvider;
use near_primitives::transaction::{
    NonceMode, SignedTransaction, Transaction, TransactionNonce, TransactionV1,
};
use near_primitives::trie_key::trie_key_parsers::parse_account_id_from_raw_key;
use near_primitives::trie_key::{TrieKey, col};
use near_primitives::types::{AccountId, Balance, EpochId, EpochInfoProvider, Gas, ShardId};
use near_primitives::version::{MIN_SUPPORTED_PROTOCOL_VERSION, PROTOCOL_VERSION};
use near_primitives::views::{ExecutionOutcomeView, SignedTransactionView};
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use near_store::{ShardTries, ShardUId};
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions};
use serde_json::{Map, Value, from_str, from_value, json, to_value};
use std::collections::{BTreeMap, BTreeSet};
use std::env::args;
use std::error::Error;
use std::io::{Read, stdin};
use std::result::Result as StdResult;

type Result<T> = StdResult<T, Box<dyn Error>>;
type Entry = (Vec<u8>, Vec<u8>);

fn metadata() -> Value {
    let store = RuntimeConfigStore::new(None);
    json!({"package":env!("CARGO_PKG_NAME"), "release":env!("CARGO_PKG_VERSION"),
        "sourceRevision":env!("SAFE_NEAR_REFERENCE_REVISION"),
        "adapterSha256":env!("SAFE_NEAR_ADAPTER_SHA256"),
        "minProtocolVersion":MIN_SUPPORTED_PROTOCOL_VERSION, "maxProtocolVersion":PROTOCOL_VERSION,
        "latestProtocolVmKind":format!("{:?}",store.get_config(PROTOCOL_VERSION).wasm_config.vm_kind),
        "epochFixture":"single-shard/no-validators"})
}

fn object<'a>(value: &'a Value, fields: &[&str]) -> Result<&'a Map<String, Value>> {
    let object = value.as_object().ok_or("expected a json object")?;
    for key in object.keys() {
        if !fields.contains(&key.as_str()) {
            return Err(format!("unknown field: {key}").into());
        }
    }
    Ok(object)
}

fn field<'a>(object: &'a Map<String, Value>, name: &str) -> Result<&'a Value> {
    object
        .get(name)
        .ok_or_else(|| format!("missing field: {name}").into())
}

fn integer(object: &Map<String, Value>, name: &str) -> Result<u64> {
    field(object, name)?
        .as_u64()
        .ok_or_else(|| format!("invalid u64 field: {name}").into())
}

fn decode<T: BorshDeserialize + BorshSerialize>(value: &Value) -> Result<T> {
    let bytes: Vec<u8> = from_value(value.clone())?;
    let decoded = from_slice(&bytes)?;
    if borsh_bytes(&decoded)? != bytes {
        return Err("noncanonical borsh input".into());
    }
    Ok(decoded)
}

fn hash(value: &Value) -> Result<CryptoHash> {
    let bytes: Vec<u8> = from_value(value.clone())?;
    Ok(CryptoHash(
        bytes.try_into().map_err(|_| "expected a 32-byte hash")?,
    ))
}

fn congestion_info(value: &Value) -> Result<BlockCongestionInfo> {
    let rows: Vec<(ShardId, Vec<u8>, u64)> = from_value(value.clone())?;
    let mut shards = BTreeMap::new();
    for (id, bytes, missed) in rows {
        let info = ExtendedCongestionInfo::new(from_slice(&bytes)?, missed);
        if shards.insert(id, info).is_some() {
            return Err("duplicate congestion shard id".into());
        }
    }
    Ok(BlockCongestionInfo::new(shards))
}

fn snapshot(tries: &ShardTries, shard: ShardUId, root: CryptoHash) -> Result<Value> {
    let trie = tries.get_trie_for_shard(shard, root);
    let locked = trie.lock_for_iter();
    let entries: Vec<Entry> = locked.iter()?.collect::<StdResult<_, _>>()?;
    let mut records = Vec::new();
    for (key, value) in &entries {
        // Upstream's StateRecord omits these two callback indices. Decode their
        // values with native Borsh types and require exact native key re-encoding.
        if matches!(
            key.first(),
            Some(&col::PENDING_DATA_COUNT | &col::POSTPONED_RECEIPT_ID)
        ) {
            let receiver_id =
                parse_account_id_from_raw_key(key)?.ok_or("missing queue receiver")?;
            let suffix = key
                .get(key.len().saturating_sub(32)..)
                .ok_or("short queue key")?;
            let identifier: CryptoHash = from_slice(suffix)?;
            let (typed_key, record) = if key[0] == col::PENDING_DATA_COUNT {
                let count: u32 = from_slice(value)?;
                (
                    TrieKey::PendingDataCount {
                        receiver_id: receiver_id.clone(),
                        receipt_id: identifier,
                    },
                    json!({"PendingDataCount":{"account_id":receiver_id,"receipt_id":identifier,"count":count}}),
                )
            } else {
                let receipt_id: CryptoHash = from_slice(value)?;
                (
                    TrieKey::PostponedReceiptId {
                        receiver_id: receiver_id.clone(),
                        data_id: identifier,
                    },
                    json!({"PostponedReceiptId":{"account_id":receiver_id,"data_id":identifier,"receipt_id":receipt_id}}),
                )
            };
            if typed_key.to_vec() != *key {
                return Err("noncanonical queue key".into());
            }
            records.push(json!({"key":key,"record":record}));
            continue;
        }
        // The upstream state-dump decoder prints diagnostics for newer shard
        // columns. Only use it for the columns it understands. All columns,
        // including opaque shard state, remain in the complete raw entries.
        if !matches!(
            key.first(),
            Some(
                &col::ACCOUNT
                    | &col::CONTRACT_DATA
                    | &col::CONTRACT_CODE
                    | &col::ACCESS_KEY
                    | &col::RECEIVED_DATA
                    | &col::POSTPONED_RECEIPT_ID
                    | &col::PENDING_DATA_COUNT
                    | &col::POSTPONED_RECEIPT
                    | &col::DELAYED_RECEIPT_OR_INDICES
            )
        ) {
            records.push(json!({"key":key, "opaque":true}));
            continue;
        }
        match StateRecord::from_raw_key_value_impl(key, value.clone()) {
            Ok(Some(record)) => {
                let mut row = json!({"key":key,"record":record});
                if let StateRecord::DelayedReceipt(receipt) = &record {
                    row["queueIndex"] =
                        json!(receipt.index.ok_or("missing delayed receipt index")?);
                }
                records.push(row);
            }
            Ok(None) => records.push(json!({"key":key, "opaque":true})),
            Err(error) => records.push(json!({"key": key, "decodeError": error.to_string()})),
        }
    }
    Ok(json!({"root":root, "entries":entries, "decodedRecords":records}))
}

fn select(
    pending: &[Receipt],
    positions: &Value,
) -> StdResult<(Vec<Receipt>, Vec<Receipt>), Value> {
    if positions.is_null() {
        return Ok((pending.to_vec(), Vec::new()));
    }
    let indices: Vec<usize> = from_value(positions.clone())
        .map_err(|error| json!({"invalidIndices":error.to_string()}))?;
    let mut seen = BTreeSet::new();
    let mut incoming = Vec::new();
    for position in indices {
        if position >= pending.len() || !seen.insert(position) {
            return Err(json!({"unavailableIndex":position}));
        }
        incoming.push(pending[position].clone());
    }
    let deferred = pending
        .iter()
        .enumerate()
        .filter_map(|(i, receipt)| (!seen.contains(&i)).then(|| receipt.clone()))
        .collect();
    Ok((incoming, deferred))
}

fn run(request: &Value) -> Result<Value> {
    let input = object(
        request,
        &[
            "formatVersion",
            "protocolVersion",
            "initialEntries",
            "pendingReceipts",
            "blocks",
        ],
    )?;
    if integer(input, "formatVersion")? != 1 {
        return Err("unsupported formatVersion".into());
    }
    let version = u32::try_from(integer(input, "protocolVersion")?)?;
    if !(MIN_SUPPORTED_PROTOCOL_VERSION..=PROTOCOL_VERSION).contains(&version) {
        return Err("protocol version is outside the pinned runtime's supported range".into());
    }
    let config = RuntimeConfigStore::new(None).get_config(version).clone();
    let provider = MockEpochInfoProvider::default();
    let layout = provider.shard_layout(&EpochId::default())?;
    if layout.shard_ids().count() != 1 {
        return Err("the oracle requires a single-shard epoch fixture".into());
    }
    let shard = layout.shard_uids().next().ok_or("missing shard")?;
    let tries = TestTriesBuilder::new().with_shard_layout(layout).build();
    let entries: Vec<Entry> = from_value(field(input, "initialEntries")?.clone())?;
    let mut keys = BTreeSet::new();
    if entries.iter().any(|(key, _)| !keys.insert(key.clone())) {
        return Err("duplicate initial trie key".into());
    }
    let trie = tries.get_trie_for_shard(shard, CryptoHash::default());
    let changes = trie.update(
        entries.into_iter().map(|(key, value)| (key, Some(value))),
        AccessOptions::DEFAULT,
    )?;
    let mut update = tries.store_update();
    let mut root = tries.apply_all(&changes, shard, &mut update);
    update.commit();
    let initial = snapshot(&tries, shard, root)?;
    let mut pending: Vec<Receipt> = field(input, "pendingReceipts")?
        .as_array()
        .ok_or("pendingReceipts must be an array")?
        .iter()
        .map(decode)
        .collect::<Result<_>>()?;
    let initial_pending = json!(pending);
    let blocks = field(input, "blocks")?
        .as_array()
        .ok_or("blocks must be an array")?;
    let runtime = Runtime::new();
    let mut trace = Vec::new();
    let mut stop = "blocksExhausted";
    for block in blocks {
        let header = object(
            block,
            &[
                "blockHeight",
                "blockTimestamp",
                "epochHeight",
                "gasPrice",
                "gasLimit",
                "randomSeed",
                "prevBlockHash",
                "congestionInfo",
                "bandwidthRequests",
                "transactions",
                "incomingIndices",
            ],
        )?;
        let positions = field(header, "incomingIndices")?;
        let (incoming, deferred) = match select(&pending, positions) {
            Ok(selection) => selection,
            Err(error) => {
                trace.push(json!({"scheduleError":error, "state":snapshot(&tries, shard, root)?,
                    "pendingReceipts":pending.iter().map(borsh_bytes).collect::<StdResult<Vec<_>, _>>()?}));
                stop = "invalidSchedule";
                break;
            }
        };
        let txs: Vec<SignedTransaction> = field(header, "transactions")?
            .as_array()
            .ok_or("transactions must be an array")?
            .iter()
            .map(decode)
            .collect::<Result<_>>()?;
        // The bridge consumes upstream-decoded views, never a second custom
        // Borsh parser. RPC views hash deployment bytes; retain actual typed actions.
        let transactions = txs
            .iter()
            .map(|tx| {
                let version = match &tx.transaction {
                    Transaction::V0(_) => 0,
                    Transaction::V1(_) => 1,
                };
                Ok(json!({"version":version, "borsh":borsh_bytes(tx)?,
                    "actions":to_value(tx.transaction.actions())?,
                    "view":SignedTransactionView::from(tx.clone())}))
            })
            .collect::<Result<Vec<_>>>()?;
        let resolved_inputs = json!({"transactions":transactions, "incomingReceipts":incoming});
        let gas_price_text = field(header, "gasPrice")?
            .as_str()
            .ok_or("gasPrice must be a decimal string")?;
        if gas_price_text.is_empty() || !gas_price_text.bytes().all(|byte| byte.is_ascii_digit()) {
            return Err("gasPrice must contain decimal digits only".into());
        }
        let gas_price = gas_price_text.parse()?;
        let gas_limit = if field(header, "gasLimit")?.is_null() {
            None
        } else {
            Some(Gas::from_gas(integer(header, "gasLimit")?))
        };
        let apply = ApplyState {
            apply_reason: ApplyChunkReason::UpdateTrackedShard,
            block_height: integer(header, "blockHeight")?,
            prev_block_hash: hash(field(header, "prevBlockHash")?)?,
            shard_id: shard.shard_id(),
            epoch_id: EpochId::default(),
            epoch_height: integer(header, "epochHeight")?,
            gas_price: Balance::from_yoctonear(gas_price),
            block_timestamp: integer(header, "blockTimestamp")?,
            gas_limit,
            random_seed: hash(field(header, "randomSeed")?)?,
            current_protocol_version: version,
            config: config.clone(),
            next_wasm_config: None,
            cache: None,
            trie_access_tracker_state: Default::default(),
            is_new_chunk: true,
            save_receipt_to_tx: false,
            congestion_info: congestion_info(field(header, "congestionInfo")?)?,
            bandwidth_requests: BlockBandwidthRequests {
                shards_bandwidth_requests: decode(field(header, "bandwidthRequests")?)?,
            },
            on_post_state_ready: None,
        };
        let validity = vec![true; txs.len()];
        let attempt = runtime.apply(
            tries.get_trie_for_shard(shard, root),
            &None,
            &apply,
            &incoming,
            SignedValidPeriodTransactions::new(txs, validity),
            &provider,
            Default::default(),
        );
        let result = match attempt {
            Ok(result) => result,
            Err(error) => {
                trace.push(json!({"runtimeError":format!("{error:?}"), "inputs":resolved_inputs,
                    "state":snapshot(&tries, shard, root)?,
                    "pendingReceipts":pending.iter().map(borsh_bytes).collect::<StdResult<Vec<_>, _>>()?}));
                stop = "runtimeError";
                break;
            }
        };
        let mut store_update = tries.store_update();
        root = tries.apply_all(&result.trie_changes, shard, &mut store_update);
        store_update.commit();
        if root != result.state_root {
            return Err("committed trie root differs from Runtime::apply result".into());
        }
        pending = deferred;
        pending.extend(result.outgoing_receipts.clone());
        let outcomes: Vec<_> = result
            .outcomes
            .iter()
            .map(|outcome| {
                Ok(json!({
                    "id":outcome.id,
                    "outcome":ExecutionOutcomeView::from(outcome.outcome.clone()),
                    "computeUsage":outcome.outcome.compute_usage,
                    "borsh":borsh_bytes(outcome)?
                }))
            })
            .collect::<Result<_>>()?;
        trace.push(json!({
            "inputs":resolved_inputs,
            "state":snapshot(&tries, shard, root)?,
            "outcomes":outcomes,
            "processedReceipts":result.processed_receipts.iter().map(|entry| &entry.receipt).collect::<Vec<_>>(),
            "outgoingReceipts":result.outgoing_receipts,
            "outgoingReceiptBorsh":result.outgoing_receipts.iter().map(borsh_bytes).collect::<StdResult<Vec<_>, _>>()?,
            "pendingReceipts":pending.iter().map(borsh_bytes).collect::<StdResult<Vec<_>, _>>()?,
            "stateChanges":borsh_bytes(&result.state_changes)?,
            "stats":borsh_bytes(&result.stats)?,
            "balanceStats":{
                "txBurntAmount":result.stats.balance.tx_burnt_amount,
                "slashedBurntAmount":result.stats.balance.slashed_burnt_amount,
                "otherBurntAmount":result.stats.balance.other_burnt_amount,
                "gasDeficitAmount":result.stats.balance.gas_deficit_amount,
                "subsidizedAmount":result.stats.balance.subsidized_amount,
            },
            "validatorProposals":borsh_bytes(&result.validator_proposals)?,
            "congestionInfo":borsh_bytes(&result.congestion_info)?,
            "nextCongestionInfo":match &result.congestion_info {
                Some(info) => json!([[shard.shard_id(),borsh_bytes(info)?,0]]),
                None => json!([]),
            },
            "bandwidthRequests":borsh_bytes(&result.bandwidth_requests)?,
            "delayedReceiptsCount":result.delayed_receipts_count,
            "bandwidthSchedulerStateHash":result.bandwidth_scheduler_state_hash,
        }));
    }
    Ok(json!({"formatVersion":1, "reference":metadata(),
        "protocolVersion":version, "vmKind":format!("{:?}",config.wasm_config.vm_kind),
        "epochFixture":"single-shard/no-validators", "initialState":initial,
        "initialPendingReceiptViews":initial_pending, "blocks":trace, "stop":stop,
        "unrunBlocks":blocks.len() - trace.len()}))
}

fn example() -> Result<Value> {
    let alice: AccountId = "alice.near".parse()?;
    let bob: AccountId = "bob.near".parse()?;
    let signer =
        InMemorySigner::from_seed(alice.clone(), KeyType::ED25519, "safe-near-fixture-alice");
    let one = 10u128.pow(24);
    let mut entries = Vec::new();
    for (id, amount) in [(alice.clone(), 100 * one), (bob.clone(), 10 * one)] {
        let account = Account::new(
            Balance::from_yoctonear(amount),
            Balance::ZERO,
            AccountContract::None,
            182,
        );
        entries.push((
            TrieKey::Account { account_id: id }.to_vec(),
            borsh_bytes(&account)?,
        ));
    }
    entries.push((
        TrieKey::access_key(alice.clone(), signer.public_key()).to_vec(),
        borsh_bytes(&AccessKey::full_access())?,
    ));
    let cross = SignedTransaction::from_actions(
        1,
        alice.clone(),
        bob,
        &signer,
        vec![Action::Transfer(TransferAction {
            deposit: Balance::from_yoctonear(one),
        })],
        CryptoHash::default(),
    );
    let local = SignedTransaction::from_actions(
        2,
        alice.clone(),
        alice,
        &signer,
        vec![Action::Transfer(TransferAction {
            deposit: Balance::from_yoctonear(one),
        })],
        CryptoHash::default(),
    );
    let provider = MockEpochInfoProvider::default();
    let layout = provider.shard_layout(&EpochId::default())?;
    let congestion = BlockCongestionInfo::new(
        layout
            .shard_ids()
            .map(|id| (id, ExtendedCongestionInfo::default()))
            .collect(),
    );
    let congestion_rows: Vec<_> = congestion
        .iter()
        .map(|(id, extended)| {
            Ok(json!([
                id,
                borsh_bytes(&extended.congestion_info)?,
                extended.missed_chunks_count
            ]))
        })
        .collect::<Result<_>>()?;
    let mut blocks = Vec::new();
    for (height, transactions, positions) in [
        (7, vec![borsh_bytes(&cross)?], Value::Null),
        (8, vec![], json!([])),
        (9, vec![], json!([0])),
        (10, vec![], Value::Null),
        (11, vec![borsh_bytes(&local)?], Value::Null),
        (12, vec![], Value::Null),
    ] {
        blocks.push(json!({"blockHeight":height, "blockTimestamp":height * 1_000_000_000u64,
            "epochHeight":0, "gasPrice":"100000000", "gasLimit":null,
            "randomSeed":vec![0u8;32], "prevBlockHash":vec![0u8;32],
            "congestionInfo":congestion_rows,
            "bandwidthRequests":borsh_bytes(&BlockBandwidthRequests::empty().shards_bandwidth_requests)?,
            "transactions":transactions, "incomingIndices":positions}));
    }
    Ok(
        json!({"formatVersion":1, "protocolVersion":PROTOCOL_VERSION, "initialEntries":entries,
        "pendingReceipts":[], "blocks":blocks}),
    )
}

fn decimal(value: &Value) -> Result<u128> {
    let text = value.as_str().ok_or("expected a decimal string")?;
    if text.is_empty() || !text.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err("invalid decimal string".into());
    }
    Ok(text.parse()?)
}

/// Encode a queue-free synthetic genesis through the pinned protocol types.
/// This is a projection of captured account fields, not the original shard trie.
fn encode_state(request: &Value) -> Result<Value> {
    let input = object(request, &["accounts"])?;
    let accounts = field(input, "accounts")?
        .as_array()
        .ok_or("expected accounts array")?;
    let mut entries = BTreeMap::new();
    let mut public_keys = BTreeMap::new();
    let mut code_hashes = BTreeMap::new();
    for row in accounts {
        let row = object(
            row,
            &[
                "accountId",
                "amount",
                "locked",
                "storageUsage",
                "code",
                "keys",
                "storage",
            ],
        )?;
        let id: AccountId = field(row, "accountId")?
            .as_str()
            .ok_or("invalid account id")?
            .parse()?;
        let code: Option<Vec<u8>> = from_value(field(row, "code")?.clone())?;
        let hash = code
            .as_ref()
            .map(|code| CryptoHash::hash_bytes(code))
            .unwrap_or_default();
        if code_hashes.insert(id.clone(), hash).is_some() {
            return Err("duplicate account".into());
        }
        let account = Account::new(
            Balance::from_yoctonear(decimal(field(row, "amount")?)?),
            Balance::from_yoctonear(decimal(field(row, "locked")?)?),
            if code.is_some() {
                AccountContract::Local(hash)
            } else {
                AccountContract::None
            },
            integer(row, "storageUsage")?,
        );
        entries.insert(
            TrieKey::Account {
                account_id: id.clone(),
            }
            .to_vec(),
            borsh_bytes(&account)?,
        );
        if let Some(code) = code {
            entries.insert(
                TrieKey::ContractCode {
                    account_id: id.clone(),
                }
                .to_vec(),
                code,
            );
        }
        let mut insert = |key, value| -> Result<()> {
            if entries.insert(key, value).is_some() {
                return Err("duplicate state key".into());
            }
            Ok(())
        };
        for key in field(row, "keys")?
            .as_array()
            .ok_or("expected keys array")?
        {
            let key = object(key, &["publicKey", "accessKey"])?;
            let text = field(key, "publicKey")?
                .as_str()
                .ok_or("invalid public key")?;
            let public_key: PublicKey = text.parse()?;
            if public_key.to_string() != text {
                return Err("noncanonical public key".into());
            }
            let access_key: AccessKey = from_value(field(key, "accessKey")?.clone())?;
            if to_value(&access_key)? != *field(key, "accessKey")? {
                return Err("noncanonical access key fields".into());
            }
            public_keys.insert(text.to_owned(), borsh_bytes(&public_key)?);
            insert(
                TrieKey::access_key(id.clone(), public_key).to_vec(),
                borsh_bytes(&access_key)?,
            )?;
        }
        let storage: Vec<Entry> = from_value(field(row, "storage")?.clone())?;
        for (key, value) in storage {
            insert(
                TrieKey::ContractData {
                    account_id: id.clone(),
                    key,
                }
                .to_vec(),
                value,
            )?;
        }
    }
    let entries: Vec<Entry> = entries.into_iter().collect();
    Ok(json!({"initialEntries":entries, "publicKeys":public_keys, "codeHashes":code_hashes}))
}

/// Deterministic synthetic signers make local transaction fixtures reproducible.
/// The adapter never submits anything to a network.
fn sign_transactions(request: &Value) -> Result<Value> {
    let input = object(request, &["signerId", "seed", "transactions"])?;
    let signer_id: AccountId = field(input, "signerId")?
        .as_str()
        .ok_or("invalid signer")?
        .parse()?;
    let seed = field(input, "seed")?
        .as_str()
        .ok_or("invalid synthetic seed")?;
    let signer = InMemorySigner::from_seed(signer_id.clone(), KeyType::ED25519, seed);
    let requests = field(input, "transactions")?
        .as_array()
        .ok_or("expected transactions array")?;
    let mut result = Vec::new();
    let mut action_keys = BTreeMap::new();
    for row in requests {
        let row = object(
            row,
            &[
                "version",
                "receiverId",
                "nonce",
                "nonceMode",
                "blockHash",
                "actions",
            ],
        )?;
        let receiver: AccountId = field(row, "receiverId")?
            .as_str()
            .ok_or("invalid receiver")?
            .parse()?;
        let actions: Vec<Action> = from_value(field(row, "actions")?.clone())?;
        if to_value(&actions)? != *field(row, "actions")? {
            return Err("noncanonical action fields".into());
        }
        for action in &actions {
            match action {
                Action::Stake(a) => {
                    action_keys.insert(a.public_key.to_string(), borsh_bytes(&a.public_key)?);
                }
                Action::AddKey(a) => {
                    action_keys.insert(a.public_key.to_string(), borsh_bytes(&a.public_key)?);
                }
                Action::DeleteKey(a) => {
                    action_keys.insert(a.public_key.to_string(), borsh_bytes(&a.public_key)?);
                }
                _ => {}
            }
        }
        let version = row
            .get("version")
            .map(|v| v.as_u64().ok_or("invalid transaction version"))
            .transpose()?
            .unwrap_or(0);
        let nonce_mode: NonceMode = row
            .get("nonceMode")
            .map(|v| from_value(v.clone()))
            .transpose()?
            .unwrap_or_default();
        let transaction = match version {
            0 => {
                if nonce_mode != NonceMode::Monotonic {
                    return Err("v0 transactions have no nonce mode".into());
                }
                SignedTransaction::from_actions(
                    integer(row, "nonce")?,
                    signer_id.clone(),
                    receiver,
                    &signer,
                    actions,
                    hash(field(row, "blockHash")?)?,
                )
            }
            1 => {
                let transaction = Transaction::V1(TransactionV1 {
                    signer_id: signer_id.clone(),
                    public_key: signer.public_key(),
                    nonce: TransactionNonce::from_nonce(integer(row, "nonce")?),
                    receiver_id: receiver,
                    block_hash: hash(field(row, "blockHash")?)?,
                    actions,
                    nonce_mode,
                });
                let signature = signer.sign(transaction.get_hash_and_size().0.as_ref());
                SignedTransaction::new(signature, transaction)
            }
            _ => return Err("unsupported transaction envelope tag".into()),
        };
        result.push(json!({"version":version,"borsh":borsh_bytes(&transaction)?,
            "actions":to_value(transaction.transaction.actions())?,
            "view":SignedTransactionView::from(transaction)}));
    }
    Ok(
        json!({"signerId":signer_id, "publicKey":signer.public_key(),
        "publicKeyBorsh":borsh_bytes(&signer.public_key())?,
        "accessKeyBorsh":borsh_bytes(&AccessKey::full_access())?,
        "actionPublicKeys":action_keys, "transactions":result}),
    )
}

fn financial_examples() -> Result<Value> {
    let transfer = example()?;
    let mut creation = transfer.clone();
    let alice: AccountId = "alice.near".parse()?;
    let child: AccountId = "child.alice.near".parse()?;
    let signer =
        InMemorySigner::from_seed(alice.clone(), KeyType::ED25519, "safe-near-fixture-alice");
    let tx = SignedTransaction::from_actions(
        1,
        alice,
        child,
        &signer,
        vec![
            Action::CreateAccount(CreateAccountAction {}),
            Action::Transfer(TransferAction {
                deposit: Balance::from_yoctonear(10u128.pow(24)),
            }),
        ],
        CryptoHash::default(),
    );
    let blocks = creation["blocks"]
        .as_array_mut()
        .ok_or("missing example blocks")?;
    blocks.truncate(4);
    blocks[0]["transactions"] = json!([borsh_bytes(&tx)?]);
    Ok(json!({"transfer":transfer, "createAccount":creation}))
}

fn main() -> Result<()> {
    match args().nth(1).as_deref() {
        Some("--metadata") => println!("{}", metadata()),
        Some("--example") => println!("{}", example()?),
        Some("--financial-examples") => println!("{}", financial_examples()?),
        Some(mode @ ("--encode-state" | "--sign-transactions")) => {
            let mut input = String::new();
            stdin().read_to_string(&mut input)?;
            let input = from_str(&input)?;
            println!(
                "{}",
                if mode == "--encode-state" {
                    encode_state(&input)?
                } else {
                    sign_transactions(&input)?
                }
            );
        }
        Some(_) => return Err("unknown argument".into()),
        None => {
            let mut input = String::new();
            stdin().read_to_string(&mut input)?;
            println!("{}", run(&from_str(&input)?)?);
        }
    }
    Ok(())
}
