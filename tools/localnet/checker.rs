//! Oracle self-check for corpus bundles (build-time overlay on `node-runtime`).
//!
//! Reads one raw bundle (a single JSON document, see tools/localnet/CORPUS.md) from the
//! file named by the first argument, rebuilds the shard's trie from the complete raw
//! pre-state, runs the pinned `Runtime::apply` on exactly the bundle data and prints the
//! results in the same shape as the bundle's `expected` section.  Nothing here reads a
//! database or the network; the bundle alone is the input.
use borsh::{BorshDeserialize, to_vec as borsh_bytes};
use near_parameters::RuntimeConfigStore;
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::BlockBandwidthRequests;
use near_primitives::congestion_info::{BlockCongestionInfo, CongestionInfo, ExtendedCongestionInfo};
use near_primitives::errors::EpochError;
use near_primitives::hash::CryptoHash;
use near_primitives::receipt::Receipt;
use near_primitives::shard_layout::{ShardLayout, ShardUId};
use near_primitives::transaction::SignedTransaction;
use near_primitives::types::{AccountId, Balance, EpochId, EpochInfoProvider, Gas, ShardId};
use near_primitives::state_record::StateRecord;
use near_primitives::trie_key::trie_key_parsers::parse_account_id_from_raw_key;
use near_primitives::trie_key::{TrieKey, col};
use near_primitives::views::ExecutionOutcomeView;
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions, ValidatorAccountsUpdate};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap};
use std::error::Error;
use std::sync::Arc;

type Result<T> = std::result::Result<T, Box<dyn Error>>;

fn unhex(value: &Value) -> Result<Vec<u8>> {
    let text = value.as_str().ok_or("expected a hex string")?;
    if text.len() % 2 != 0 {
        return Err("odd hex length".into());
    }
    (0..text.len() / 2)
        .map(|i| u8::from_str_radix(&text[2 * i..2 * i + 2], 16).map_err(|e| e.into()))
        .collect()
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn hash_of(value: &Value) -> Result<CryptoHash> {
    Ok(CryptoHash(unhex(value)?.try_into().map_err(|_| "expected 32 bytes")?))
}

fn hash_hex(hash: &CryptoHash) -> String {
    hex(hash.as_ref())
}

fn string<'a>(value: &'a Value, key: &str) -> Result<&'a str> {
    value[key].as_str().ok_or_else(|| format!("missing string {key}").into())
}

fn number(value: &Value, key: &str) -> Result<u64> {
    value[key].as_u64().ok_or_else(|| format!("missing integer {key}").into())
}

fn balance(value: &Value, key: &str) -> Result<Balance> {
    Ok(Balance::from_yoctonear(string(value, key)?.parse()?))
}

fn account_map(value: &Value) -> Result<HashMap<AccountId, Balance>> {
    let mut map = HashMap::new();
    for (key, amount) in value.as_object().ok_or("expected an account map")? {
        map.insert(key.parse()?, Balance::from_yoctonear(amount.as_str().ok_or("amount")?.parse()?));
    }
    Ok(map)
}

struct BundleEpoch {
    chain_id: String,
    stakes: HashMap<AccountId, Balance>,
    total: Balance,
    minimum: Balance,
    layout: ShardLayout,
}

impl EpochInfoProvider for BundleEpoch {
    fn validator_stake(
        &self,
        _epoch_id: &EpochId,
        account_id: &AccountId,
    ) -> std::result::Result<Option<Balance>, EpochError> {
        Ok(self.stakes.get(account_id).copied())
    }
    fn validator_total_stake(&self, _epoch_id: &EpochId) -> std::result::Result<Balance, EpochError> {
        Ok(self.total)
    }
    fn minimum_stake(&self, _prev_block_hash: &CryptoHash) -> std::result::Result<Balance, EpochError> {
        Ok(self.minimum)
    }
    fn chain_id(&self) -> String {
        self.chain_id.clone()
    }
    fn shard_layout(&self, _epoch_id: &EpochId) -> std::result::Result<ShardLayout, EpochError> {
        Ok(self.layout.clone())
    }
}

fn apply_bundle(bundle: &Value) -> Result<Value> {
    if bundle["formatVersion"] != json!(1) {
        return Err("unsupported bundle formatVersion".into());
    }
    let meta = &bundle["meta"];
    let context = &bundle["context"];
    let shard_uid = ShardUId::new(
        number(&meta["shardUId"], "version")? as u32,
        ShardId::new(number(&meta["shardUId"], "shardId")?),
    );
    let shard_id = ShardId::new(number(meta, "shardId")?);
    let protocol_version = number(context, "currentProtocolVersion")? as u32;
    let layout = ShardLayout::try_from_slice(&unhex(&context["shardLayout"])?)?;

    // Rebuild the shard's trie from the complete raw pre-state.
    let tries = TestTriesBuilder::new().with_shard_layout(layout.clone()).build();
    let pre = &bundle["preState"];
    let entries: Vec<(Vec<u8>, Option<Vec<u8>>)> = pre["entries"]
        .as_array()
        .ok_or("preState.entries")?
        .iter()
        .map(|row| Ok((unhex(&row[0])?, Some(unhex(&row[1])?))))
        .collect::<Result<_>>()?;
    let changes = tries
        .get_trie_for_shard(shard_uid, CryptoHash::default())
        .update(entries.iter().cloned(), AccessOptions::DEFAULT)?;
    let mut update = tries.store_update();
    let root = tries.apply_all(&changes, shard_uid, &mut update);
    update.commit();
    if hash_hex(&root) != string(pre, "root")? {
        return Err(format!("rebuilt pre-state root {} differs from the bundle", hash_hex(&root)).into());
    }

    let config = RuntimeConfigStore::for_chain_id(string(meta, "chainId")?)
        .get_config(protocol_version)
        .clone();
    let mut congestion = BTreeMap::new();
    for row in context["congestionInfo"].as_array().ok_or("congestionInfo")? {
        let info = CongestionInfo::try_from_slice(&unhex(&row[1])?)?;
        let id = ShardId::new(row[0].as_u64().ok_or("congestion shard")?);
        congestion.insert(id, ExtendedCongestionInfo::new(info, row[2].as_u64().ok_or("missed")?));
    }
    let apply_state = ApplyState {
        apply_reason: ApplyChunkReason::UpdateTrackedShard,
        block_height: number(context, "blockHeight")?,
        prev_block_hash: hash_of(&context["prevBlockHash"])?,
        shard_id,
        epoch_id: EpochId(hash_of(&context["epochId"])?),
        epoch_height: number(context, "epochHeight")?,
        gas_price: balance(context, "gasPrice")?,
        block_timestamp: number(context, "blockTimestamp")?,
        gas_limit: Some(Gas::from_gas(number(context, "gasLimit")?)),
        random_seed: hash_of(&context["randomSeed"])?,
        current_protocol_version: protocol_version,
        config: config.clone(),
        next_wasm_config: None,
        cache: None,
        is_new_chunk: context["isNewChunk"].as_bool().ok_or("isNewChunk")?,
        save_receipt_to_tx: false,
        congestion_info: BlockCongestionInfo::new(congestion),
        bandwidth_requests: BlockBandwidthRequests {
            shards_bandwidth_requests: BorshDeserialize::try_from_slice(&unhex(&context["bandwidthRequests"])?)?,
        },
        trie_access_tracker_state: Default::default(),
        on_post_state_ready: None,
    };
    let update_json = &context["validatorAccountsUpdate"];
    let validator_update = if update_json.is_null() {
        None
    } else {
        Some(ValidatorAccountsUpdate {
            stake_info: account_map(&update_json["stakeInfo"])?,
            validator_rewards: account_map(&update_json["validatorRewards"])?,
            last_proposals: account_map(&update_json["lastProposals"])?,
            protocol_treasury_account_id: match &update_json["protocolTreasuryAccountId"] {
                Value::Null => None,
                other => Some(other.as_str().ok_or("treasury")?.parse()?),
            },
        })
    };
    let epoch_json = &context["epochInfo"];
    let provider = BundleEpoch {
        chain_id: string(epoch_json, "chainId")?.to_string(),
        stakes: epoch_json["validators"]
            .as_array()
            .ok_or("validators")?
            .iter()
            .map(|row| {
                Ok((
                    row[0].as_str().ok_or("validator")?.parse()?,
                    Balance::from_yoctonear(row[1].as_str().ok_or("stake")?.parse()?),
                ))
            })
            .collect::<Result<_>>()?,
        total: balance(epoch_json, "totalStake")?,
        minimum: balance(epoch_json, "minimumStake")?,
        layout: layout.clone(),
    };

    let inputs = &bundle["inputs"];
    let mut transactions = Vec::new();
    let mut validity = Vec::new();
    for row in inputs["transactions"].as_array().ok_or("transactions")? {
        transactions.push(SignedTransaction::try_from_slice(&unhex(&row["borsh"])?)?);
        validity.push(row["valid"].as_bool().ok_or("valid")?);
    }
    let receipts: Vec<Receipt> = inputs["incomingReceipts"]
        .as_array()
        .ok_or("incomingReceipts")?
        .iter()
        .map(|row| Ok(Receipt::try_from_slice(&unhex(row)?)?))
        .collect::<Result<_>>()?;

    let proof_limit = number(context, "proofSizeSoftLimit")?;
    let trie = tries.get_trie_for_shard(shard_uid, root).recording_reads_with_proof_size_limit(proof_limit);
    let result = Runtime::new()
        .apply(
            trie,
            &validator_update,
            &apply_state,
            &receipts,
            SignedValidPeriodTransactions::new(transactions, validity),
            &provider,
            Default::default(),
        )
        .map_err(|e| format!("Runtime::apply failed: {e:?}"))?;

    let mut store_update = tries.store_update();
    let post_root = tries.apply_all(&result.trie_changes, shard_uid, &mut store_update);
    store_update.commit();
    if post_root != result.state_root {
        return Err("committed trie root differs from Runtime::apply result".into());
    }
    let post_entries: Vec<(Vec<u8>, Vec<u8>)> = tries
        .get_trie_for_shard(shard_uid, post_root)
        .lock_for_iter()
        .iter()?
        .collect::<std::result::Result<_, _>>()?;
    let pre_map: BTreeMap<Vec<u8>, Vec<u8>> =
        entries.iter().map(|(k, v)| (k.clone(), v.clone().unwrap())).collect();
    let post_map: BTreeMap<Vec<u8>, Vec<u8>> = post_entries.into_iter().collect();
    let mut diff = Vec::new();
    for (key, value) in &post_map {
        if pre_map.get(key) != Some(value) {
            diff.push(json!([hex(key), hex(value)]));
        }
    }
    for key in pre_map.keys() {
        if !post_map.contains_key(key) {
            diff.push(json!([hex(key), Value::Null]));
        }
    }

    let outcomes: Vec<Value> = result
        .outcomes
        .iter()
        .map(|o| {
            Ok(json!({
                "id": hash_hex(&o.id),
                "borsh": hex(&borsh_bytes(o)?),
                "view": serde_json::to_value(ExecutionOutcomeView::from(o.outcome.clone()))?,
                "computeUsage": o.outcome.compute_usage,
            }))
        })
        .collect::<Result<_>>()?;
    let hashes: Vec<Vec<CryptoHash>> = result.outcomes.iter().map(|o| o.to_hashes()).collect();
    let (outcome_root, _) = near_primitives::merkle::merklize(&hashes);
    let total_gas: u64 = result.outcomes.iter().map(|o| o.outcome.gas_burnt.as_gas()).sum();
    let stats = &result.stats.balance;
    let burnt = stats.tx_burnt_amount.as_yoctonear() + stats.other_burnt_amount.as_yoctonear()
        + stats.slashed_burnt_amount.as_yoctonear() - stats.subsidized_amount.as_yoctonear();
    Ok(json!({
        "postStateRoot": hash_hex(&result.state_root),
        "outcomes": outcomes,
        "outcomeRoot": hash_hex(&outcome_root),
        "outgoingReceipts": result.outgoing_receipts.iter().map(|r| Ok(hex(&borsh_bytes(r)?))).collect::<Result<Vec<_>>>()?,
        "stateChanges": hex(&borsh_bytes(&result.state_changes)?),
        "stateDiff": diff,
        "gasUsed": total_gas,
        "balanceBurnt": burnt.to_string(),
        "balanceStats": {
            "txBurnt": stats.tx_burnt_amount.as_yoctonear().to_string(),
            "slashedBurnt": stats.slashed_burnt_amount.as_yoctonear().to_string(),
            "otherBurnt": stats.other_burnt_amount.as_yoctonear().to_string(),
            "gasDeficit": stats.gas_deficit_amount.as_yoctonear().to_string(),
            "subsidized": stats.subsidized_amount.as_yoctonear().to_string(),
        },
        "validatorProposals": hex(&borsh_bytes(&result.validator_proposals)?),
        "congestionInfo": result.congestion_info.as_ref().map(|c| Ok::<_, Box<dyn Error>>(hex(&borsh_bytes(c)?))).transpose()?,
        "bandwidthRequests": hex(&borsh_bytes(&result.bandwidth_requests)?),
        "bandwidthSchedulerStateHash": hash_hex(&result.bandwidth_scheduler_state_hash),
        "delayedReceiptsCount": result.delayed_receipts_count,
        "processedYieldTimeouts": hex(&borsh_bytes(&result.processed_yield_timeouts)?),
        "contractUpdates": {"deployed": result.contract_updates.contract_deploys.len(), "called": result.contract_updates.contract_accesses.len()},
    }))
}

/// Readable projection of raw trie entries through the pinned decoders.  Columns that
/// upstream's `StateRecord` does not know are marked opaque; the raw bytes stay authoritative.
fn decode_entries(rows: &Value) -> Result<Value> {
    let mut records = Vec::new();
    for row in rows.as_array().ok_or("entries")? {
        let key = unhex(&row[0])?;
        let value = unhex(&row[1])?;
        let first = key.first().copied();
        if matches!(first, Some(col::PENDING_DATA_COUNT | col::POSTPONED_RECEIPT_ID)) {
            let receiver_id = parse_account_id_from_raw_key(&key)?.ok_or("missing queue receiver")?;
            let identifier: CryptoHash = borsh::from_slice(&key[key.len() - 32..])?;
            let (typed, record) = if first == Some(col::PENDING_DATA_COUNT) {
                let count: u32 = borsh::from_slice(&value)?;
                (TrieKey::PendingDataCount { receiver_id: receiver_id.clone(), receipt_id: identifier },
                 json!({"PendingDataCount": {"account_id": receiver_id, "receipt_id": identifier, "count": count}}))
            } else {
                let receipt_id: CryptoHash = borsh::from_slice(&value)?;
                (TrieKey::PostponedReceiptId { receiver_id: receiver_id.clone(), data_id: identifier },
                 json!({"PostponedReceiptId": {"account_id": receiver_id, "data_id": identifier, "receipt_id": receipt_id}}))
            };
            if typed.to_vec() != key {
                return Err("noncanonical queue key".into());
            }
            records.push(json!({"key": hex(&key), "record": record}));
            continue;
        }
        if !matches!(first, Some(col::ACCOUNT | col::CONTRACT_DATA | col::CONTRACT_CODE | col::ACCESS_KEY
            | col::RECEIVED_DATA | col::POSTPONED_RECEIPT | col::DELAYED_RECEIPT_OR_INDICES)) {
            records.push(json!({"key": hex(&key), "opaque": true}));
            continue;
        }
        match StateRecord::from_raw_key_value_impl(&key, value.clone()) {
            Ok(Some(record)) => {
                let mut out = json!({"key": hex(&key), "record": record});
                if let StateRecord::DelayedReceipt(receipt) = &record {
                    out["queueIndex"] = json!(receipt.index);
                }
                records.push(out);
            }
            Ok(None) => records.push(json!({"key": hex(&key), "opaque": true})),
            Err(error) => records.push(json!({"key": hex(&key), "decodeError": error.to_string()})),
        }
    }
    Ok(Value::Array(records))
}

fn main() -> Result<()> {
    let mut arguments = std::env::args().skip(1);
    let first = arguments.next().ok_or("usage: safe-near-corpus-check [--decode] BUNDLE.json")?;
    if first == "--decode" {
        let path = arguments.next().ok_or("missing bundle")?;
        let bundle: Value = serde_json::from_slice(&std::fs::read(path)?)?;
        let pre = decode_entries(&bundle["preState"]["entries"])?;
        let diff: Vec<Value> = bundle["expected"]["stateDiff"].as_array().ok_or("stateDiff")?.iter()
            .filter(|row| !row[1].is_null()).cloned().collect();
        println!("{}", serde_json::to_string(&json!({"preState": pre, "postChanged": decode_entries(&Value::Array(diff))?}))?);
        return Ok(());
    }
    let bundle: Value = serde_json::from_slice(&std::fs::read(first)?)?;
    let actual = apply_bundle(&bundle)?;
    println!("{}", serde_json::to_string(&actual)?);
    Ok(())
}
