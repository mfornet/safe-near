//! Historical Runtime::apply capture and offline replay at the pinned nearcore revision.
//! Compiled both as a node-runtime module and (with imports rewritten) by replay.rs.
use borsh::{BorshDeserialize, BorshSerialize};
use near_parameters::RuntimeConfigStore;
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::BlockBandwidthRequests;
use near_primitives::congestion_info::{BlockCongestionInfo, ExtendedCongestionInfo};
use near_primitives::errors::{EpochError, RuntimeError};
use near_primitives::hash::CryptoHash;
use near_primitives::merkle::merklize;
use near_primitives::receipt::Receipt;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::types::{AccountId, Balance, EpochId, EpochInfoProvider, Gas};
use near_primitives::version::{MIN_SUPPORTED_PROTOCOL_VERSION, PROTOCOL_VERSION};
use near_store::{PartialStorage, Trie};
use node_runtime::{
    ApplyResult, ApplyState, Runtime, SignedValidPeriodTransactions, ValidatorAccountsUpdate,
};
use serde_json::{Value, json};
use std::collections::BTreeMap;
use std::io::Write;
use std::sync::Mutex;

pub const FORMAT: &str = "safe-near-runtime-witness-v1";
pub const REVISION: &str = "44f7ae6cd7ef08bab604e20a473bf77e35d4c993";

pub fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}
pub fn unhex(value: &Value) -> Vec<u8> {
    let s = value.as_str().expect("hex string required");
    assert!(
        s.len() % 2 == 0
            && s.bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "noncanonical hex"
    );
    s.as_bytes()
        .chunks_exact(2)
        .map(|b| u8::from_str_radix(std::str::from_utf8(b).unwrap(), 16).unwrap())
        .collect()
}
pub fn encoded<T: BorshSerialize + ?Sized>(value: &T) -> Value {
    json!(hex(&borsh::to_vec(value).expect("Borsh encode")))
}
pub fn decoded<T: BorshDeserialize>(value: &Value) -> T {
    borsh::from_slice(&unhex(value)).expect("invalid Borsh payload")
}
fn number(value: &Value) -> u64 {
    value.as_u64().expect("u64 required")
}
fn boolean(value: &Value) -> bool {
    value.as_bool().expect("bool required")
}

// Queries are keyed by method plus canonical Borsh arguments. Failed epoch queries
// are deliberately unsupported: they must never become invented successful values.
struct RecordingEpoch<'a> {
    inner: &'a dyn EpochInfoProvider,
    entries: Mutex<BTreeMap<String, Value>>,
}
impl RecordingEpoch<'_> {
    fn save(&self, key: String, value: Value) {
        if let Some(old) = self.entries.lock().unwrap().insert(key, value.clone()) {
            assert_eq!(old, value, "epoch query changed during capture");
        }
    }
}
fn query<T: BorshSerialize + ?Sized>(name: &str, args: &T) -> String {
    format!("{name}:{}", encoded(args).as_str().unwrap())
}
impl EpochInfoProvider for RecordingEpoch<'_> {
    fn validator_stake(
        &self,
        epoch: &EpochId,
        account: &AccountId,
    ) -> Result<Option<Balance>, EpochError> {
        let value = self.inner.validator_stake(epoch, account)?;
        self.save(query("validator_stake", &(epoch, account)), encoded(&value));
        Ok(value)
    }
    fn validator_total_stake(&self, epoch: &EpochId) -> Result<Balance, EpochError> {
        let value = self.inner.validator_total_stake(epoch)?;
        self.save(query("validator_total_stake", epoch), encoded(&value));
        Ok(value)
    }
    fn minimum_stake(&self, hash: &CryptoHash) -> Result<Balance, EpochError> {
        let value = self.inner.minimum_stake(hash)?;
        self.save(query("minimum_stake", hash), encoded(&value));
        Ok(value)
    }
    fn chain_id(&self) -> String {
        let value = self.inner.chain_id();
        self.save("chain_id".into(), json!(value));
        value
    }
    fn shard_layout(&self, epoch: &EpochId) -> Result<ShardLayout, EpochError> {
        let value = self.inner.shard_layout(epoch)?;
        self.save(query("shard_layout", epoch), encoded(&value));
        Ok(value)
    }
}
struct ReplayEpoch {
    entries: BTreeMap<String, Value>,
}
impl ReplayEpoch {
    fn get(&self, key: &str) -> &Value {
        self.entries.get(key).expect("uncaptured epoch query")
    }
}
impl EpochInfoProvider for ReplayEpoch {
    fn validator_stake(
        &self,
        epoch: &EpochId,
        account: &AccountId,
    ) -> Result<Option<Balance>, EpochError> {
        Ok(decoded(
            self.get(&query("validator_stake", &(epoch, account))),
        ))
    }
    fn validator_total_stake(&self, epoch: &EpochId) -> Result<Balance, EpochError> {
        Ok(decoded(self.get(&query("validator_total_stake", epoch))))
    }
    fn minimum_stake(&self, hash: &CryptoHash) -> Result<Balance, EpochError> {
        Ok(decoded(self.get(&query("minimum_stake", hash))))
    }
    fn chain_id(&self) -> String {
        self.get("chain_id").as_str().expect("chain_id").to_owned()
    }
    fn shard_layout(&self, epoch: &EpochId) -> Result<ShardLayout, EpochError> {
        Ok(decoded(self.get(&query("shard_layout", epoch))))
    }
}

pub fn observations(result: &ApplyResult) -> Value {
    // Wall-clock scheduler duration is diagnostic telemetry, not a protocol result.
    // Preserve its original bytes separately in captureTelemetry; compare every
    // other statistics field, including scheduler grants and accounting.
    let mut stats = result.stats.clone();
    stats.bandwidth_scheduler.time_to_run_ms = 0;
    let hashes: Vec<_> = result.outcomes.iter().map(|o| o.to_hashes()).collect();
    let outcome_root = merklize(&hashes).0;
    let mut accesses: Vec<_> = result
        .contract_updates
        .contract_accesses
        .iter()
        .map(encoded)
        .collect();
    accesses.sort_by_key(|x| x.as_str().unwrap().to_owned());
    json!({
        "stateRoot": result.state_root,
        "outcomeRoot": outcome_root,
        "outcomes": encoded(&result.outcomes),
        "computeUsage": result.outcomes.iter().map(|o| o.outcome.compute_usage).collect::<Vec<_>>(),
        "outgoingReceipts": encoded(&result.outgoing_receipts),
        "stateChanges": encoded(&result.state_changes),
        "validatorProposals": encoded(&result.validator_proposals),
        "stats": encoded(&stats),
        "processedReceipts": result.processed_receipts.iter().map(|p| json!({"receipt":encoded(&p.receipt),"source":encoded(&p.source)})).collect::<Vec<_>>(),
        "processedYieldTimeouts": encoded(&result.processed_yield_timeouts),
        "delayedReceiptsCount": result.delayed_receipts_count,
        "congestionInfo": encoded(&result.congestion_info),
        "bandwidthRequests": encoded(&result.bandwidth_requests),
        "bandwidthSchedulerStateHash": result.bandwidth_scheduler_state_hash,
        "contractAccesses": accesses,
        "contractDeploys": result.contract_updates.contract_deploys.iter().map(|c| json!({"hash":c.hash(),"code":hex(c.code())})).collect::<Vec<_>>(),
        "receiptToTx": encoded(&result.receipt_to_tx),
        "gasBurnt": result.outcomes.iter().map(|o| o.outcome.gas_burnt.as_gas() as u128).sum::<u128>().to_string(),
        "tokensBurnt": result.outcomes.iter().map(|o| o.outcome.tokens_burnt.as_yoctonear()).sum::<u128>().to_string()
        ,"balanceBurnt": (result.stats.balance.tx_burnt_amount
            .checked_add(result.stats.balance.other_burnt_amount).unwrap()
            .checked_add(result.stats.balance.slashed_burnt_amount).unwrap()
            .checked_sub(result.stats.balance.subsidized_amount).unwrap()).as_yoctonear().to_string()
    })
}

fn context(state: &ApplyState) -> Value {
    assert!(
        state.next_wasm_config.is_none(),
        "capture currently requires no VM upgrade prewarm"
    );
    assert!(
        (MIN_SUPPORTED_PROTOCOL_VERSION..=PROTOCOL_VERSION)
            .contains(&state.current_protocol_version)
    );
    let config = RuntimeConfigStore::new(None)
        .get_config(state.current_protocol_version)
        .clone();
    assert_eq!(
        *config, *state.config,
        "custom runtime configuration unsupported"
    );
    json!({
        "blockHeight":state.block_height, "prevBlockHash":encoded(&state.prev_block_hash),
        "shardId":state.shard_id, "epochId":encoded(&state.epoch_id), "epochHeight":state.epoch_height,
        "gasPrice":state.gas_price.as_yoctonear().to_string(), "blockTimestamp":state.block_timestamp,
        "gasLimit":state.gas_limit.map(|g| g.as_gas()), "randomSeed":encoded(&state.random_seed),
        "protocolVersion":state.current_protocol_version, "isNewChunk":state.is_new_chunk,
        "saveReceiptToTx":state.save_receipt_to_tx, "applyReason":state.apply_reason.as_str(),
        "runtimeConfig":format!("{:?}", state.config),
        "congestionInfo":state.congestion_info.iter().map(|(shard, info)| json!([shard,encoded(&info.congestion_info),info.missed_chunks_count])).collect::<Vec<_>>(),
        "bandwidthRequests":encoded(&state.bandwidth_requests.shards_bandwidth_requests)
    })
}

pub fn replay(input: &Value) -> Value {
    assert_eq!(input["format"], FORMAT);
    assert_eq!(input["sourceRevision"], REVISION);
    assert!(
        input["validatorAccountsUpdate"].is_null(),
        "epoch account updates unsupported in first fixture"
    );
    let c = &input["context"];
    let protocol = u32::try_from(number(&c["protocolVersion"])).unwrap();
    assert!((MIN_SUPPORTED_PROTOCOL_VERSION..=PROTOCOL_VERSION).contains(&protocol));
    let config = RuntimeConfigStore::new(None).get_config(protocol).clone();
    assert_eq!(
        c["runtimeConfig"],
        format!("{:?}", config),
        "runtime config/backend mismatch"
    );
    let congestion = c["congestionInfo"]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| {
            (
                number(&row[0]).into(),
                ExtendedCongestionInfo::new(decoded(&row[1]), number(&row[2])),
            )
        })
        .collect();
    let state = ApplyState {
        apply_reason: match c["applyReason"].as_str().unwrap() {
            "update_shard" => ApplyChunkReason::UpdateTrackedShard,
            "validate_chunk" => ApplyChunkReason::ValidateChunkStateWitness,
            "view_shard" => ApplyChunkReason::ViewTrackedShard,
            _ => panic!("unknown apply reason"),
        },
        block_height: number(&c["blockHeight"]),
        prev_block_hash: decoded(&c["prevBlockHash"]),
        shard_id: number(&c["shardId"]).into(),
        epoch_id: decoded(&c["epochId"]),
        epoch_height: number(&c["epochHeight"]),
        gas_price: Balance::from_yoctonear(c["gasPrice"].as_str().unwrap().parse().unwrap()),
        block_timestamp: number(&c["blockTimestamp"]),
        gas_limit: if c["gasLimit"].is_null() {
            None
        } else {
            Some(Gas::from_gas(number(&c["gasLimit"])))
        },
        random_seed: decoded(&c["randomSeed"]),
        current_protocol_version: protocol,
        config: config.clone(),
        next_wasm_config: None,
        cache: None,
        trie_access_tracker_state: Default::default(),
        is_new_chunk: boolean(&c["isNewChunk"]),
        save_receipt_to_tx: boolean(&c["saveReceiptToTx"]),
        congestion_info: BlockCongestionInfo::new(congestion),
        bandwidth_requests: BlockBandwidthRequests {
            shards_bandwidth_requests: decoded(&c["bandwidthRequests"]),
        },
        on_post_state_ready: None,
    };
    let provider = ReplayEpoch {
        entries: serde_json::from_value(input["epochQueries"].clone()).unwrap(),
    };
    let mut trie = Trie::from_recorded_storage(
        PartialStorage {
            nodes: decoded(&input["witness"]),
        },
        decoded(&input["preStateRoot"]),
        boolean(&input["flatStorageCosts"]),
    );
    // Preserve proof-size admission as well as trie access accounting.
    trie = trie.recording_reads_with_proof_size_limit(
        config.witness_config.main_storage_proof_size_soft_limit,
    );
    let receipts: Vec<Receipt> = decoded(&input["incomingReceipts"]);
    let transactions = decoded(&input["transactions"]);
    let flags: Vec<bool> = serde_json::from_value(input["transactionValidity"].clone()).unwrap();
    let result = Runtime::new()
        .apply(
            trie,
            &None,
            &state,
            &receipts,
            SignedValidPeriodTransactions::new(transactions, flags),
            &provider,
            Default::default(),
        )
        .expect("offline Runtime::apply failed");
    let observed = observations(&result);
    let telemetry = &input["captureTelemetry"];
    let mut original: near_primitives::chunk_apply_stats::ChunkApplyStatsV1 =
        decoded(&telemetry["originalStats"]);
    assert_eq!(telemetry["bandwidthSchedulerTimeToRunMs"],
        original.bandwidth_scheduler.time_to_run_ms.to_string());
    original.bandwidth_scheduler.time_to_run_ms = 0;
    assert_eq!(encoded(&original), observed["stats"], "deterministic capture statistics differ");
    observed
}

pub fn verify_archive(input: &Value, archive: &Value, result: &Value) {
    use near_primitives::block_header::BlockHeader;
    use near_primitives::sharding::{ChunkHashHeight, ShardChunkHeader};
    use near_primitives::transaction::{ExecutionOutcomeWithId, SignedTransaction};
    use near_primitives::types::chunk_extra::ChunkExtra;
    assert_eq!(archive["format"], "safe-near-archive-anchor-v1");
    assert_eq!(archive["archiveComparisonEstablished"], true);
    let header: BlockHeader = decoded(&archive["blockHeader"]);
    let chunk: ShardChunkHeader = decoded(&archive["chunkHeader"]);
    let extra: ChunkExtra = decoded(&archive["chunkExtra"]);
    let context = &input["context"];
    assert_eq!(json!(header.hash()), archive["blockHash"]);
    assert_eq!(header.height(), number(&archive["blockHeight"]));
    assert_eq!(header.height(), number(&context["blockHeight"]));
    assert_eq!(
        header.prev_hash(),
        &decoded::<CryptoHash>(&context["prevBlockHash"])
    );
    assert_eq!(header.epoch_id(), &decoded::<EpochId>(&context["epochId"]));
    assert_eq!(header.raw_timestamp(), number(&context["blockTimestamp"]));
    assert_eq!(
        header.random_value(),
        &decoded::<CryptoHash>(&context["randomSeed"])
    );
    assert_eq!(
        header.next_gas_price().as_yoctonear().to_string(),
        context["gasPrice"].as_str().unwrap()
    );
    assert_eq!(chunk.shard_id(), number(&archive["shardId"]));
    assert_eq!(chunk.shard_id(), number(&context["shardId"]));
    assert!(chunk.is_new_chunk(header.height()));
    assert!(boolean(&context["isNewChunk"]));
    assert_eq!(
        chunk.prev_state_root(),
        decoded::<CryptoHash>(&input["preStateRoot"])
    );
    assert_eq!(chunk.gas_limit().as_gas(), number(&context["gasLimit"]));
    let transactions: Vec<SignedTransaction> = decoded(&input["transactions"]);
    assert_eq!(
        chunk.tx_root(),
        &merklize(&transactions).0,
        "transactions do not match archived chunk"
    );
    assert_eq!(json!(extra.state_root()), result["stateRoot"]);
    assert_eq!(json!(extra.outcome_root()), result["outcomeRoot"]);
    assert_eq!(json!(extra.state_root()), archive["stateRoot"]);
    assert_eq!(json!(extra.outcome_root()), archive["outcomeRoot"]);
    assert_eq!(
        extra.gas_used().as_gas().to_string(),
        result["gasBurnt"].as_str().unwrap()
    );
    assert_eq!(
        extra.balance_burnt().as_yoctonear().to_string(),
        result["balanceBurnt"].as_str().unwrap()
    );
    assert_eq!(archive["outcomes"], result["outcomes"]);
    assert_eq!(archive["outgoingReceipts"], result["outgoingReceipts"]);
    let outcomes: Vec<ExecutionOutcomeWithId> = decoded(&archive["outcomes"]);
    assert_eq!(
        *extra.outcome_root(),
        merklize(&outcomes.iter().map(|o| o.to_hashes()).collect::<Vec<_>>()).0
    );
    assert_eq!(archive["chainId"], input["epochQueries"]["chain_id"]);
    assert_eq!(archive["genesisConfig"]["chain_id"], archive["chainId"]);
    let proposals: Vec<_> = extra.validator_proposals().map(|v| v.into_v1()).collect();
    assert_eq!(encoded(&proposals), archive["validatorProposalsV1"]);
    let native_proposals: Vec<near_primitives::types::validator_stake::ValidatorStake> =
        decoded(&result["validatorProposals"]);
    assert_eq!(
        encoded(
            &native_proposals
                .into_iter()
                .map(|v| v.into_v1())
                .collect::<Vec<_>>()
        ),
        archive["validatorProposalsV1"]
    );
    assert_eq!(
        encoded(&Some(extra.congestion_info())),
        result["congestionInfo"]
    );
    assert_eq!(
        encoded(
            extra
                .bandwidth_requests()
                .expect("archive bandwidth requests missing")
        ),
        result["bandwidthRequests"]
    );
    let current_chunks: Vec<ShardChunkHeader> = decoded(&archive["chunkHeaders"]);
    let header_root = |chunks: &[ShardChunkHeader]| {
        merklize(
            &chunks
                .iter()
                .map(|c| ChunkHashHeight(c.chunk_hash().clone(), c.height_included()))
                .collect::<Vec<_>>(),
        )
        .0
    };
    assert_eq!(*header.chunk_headers_root(), header_root(&current_chunks));
    assert_eq!(
        current_chunks
            .iter()
            .filter(|c| c.shard_id() == chunk.shard_id())
            .count(),
        1
    );
    assert_eq!(
        encoded(
            current_chunks
                .iter()
                .find(|c| c.shard_id() == chunk.shard_id())
                .unwrap()
        ),
        archive["chunkHeader"]
    );
    let next: BlockHeader = decoded(&archive["nextBlockHeader"]);
    let next_chunks: Vec<ShardChunkHeader> = decoded(&archive["nextChunkHeaders"]);
    assert_eq!(next.prev_hash(), header.hash());
    assert_eq!(next.epoch_id(), header.epoch_id());
    assert_eq!(*next.chunk_headers_root(), header_root(&next_chunks));
    let next_chunk = next_chunks
        .iter()
        .find(|c| c.shard_id() == chunk.shard_id())
        .expect("next shard missing");
    assert!(next_chunk.is_new_chunk(next.height()));
    assert_eq!(next_chunk.prev_state_root(), *extra.state_root());
    assert_eq!(next_chunk.prev_outcome_root(), extra.outcome_root());
    let provider = ReplayEpoch {
        entries: serde_json::from_value(input["epochQueries"].clone()).unwrap(),
    };
    let layout = provider.shard_layout(header.epoch_id()).unwrap();
    let outgoing: Vec<Receipt> = decoded(&result["outgoingReceipts"]);
    let receipt_hashes: Vec<_> = layout
        .shard_infos()
        .map(|info| {
            let shard = info.shard_id();
            let receipts: Vec<_> = outgoing
                .iter()
                .filter(|r| r.receiver_shard_id(&layout).unwrap() == shard)
                .collect();
            near_primitives::hash::hash(&borsh::to_vec(&(shard, receipts)).unwrap())
        })
        .collect();
    assert_eq!(
        *next_chunk.prev_outgoing_receipts_root(),
        merklize(&receipt_hashes).0
    );
}

// Observe raw storage reads without changing trie access accounting or the
// consensus proof recorder. This includes code and NO_SIDE_EFFECTS lookups.
struct RecordingStorage {
    inner: std::sync::Arc<dyn near_store::TrieStorage>,
    bytes: std::sync::Arc<Mutex<BTreeMap<CryptoHash, std::sync::Arc<[u8]>>>>,
}
impl near_store::TrieStorage for RecordingStorage {
    fn retrieve_raw_bytes(
        &self,
        hash: &CryptoHash,
    ) -> Result<std::sync::Arc<[u8]>, near_primitives::errors::StorageError> {
        let bytes = self.inner.retrieve_raw_bytes(hash)?;
        assert_eq!(
            near_primitives::hash::hash(&bytes),
            *hash,
            "archive content hash mismatch"
        );
        self.bytes.lock().unwrap().insert(*hash, bytes.clone());
        Ok(bytes)
    }
    fn as_caching_storage(&self) -> Option<&near_store::TrieCachingStorage> {
        self.inner.as_caching_storage()
    }
}

impl Runtime {
    // Signature intentionally matches Runtime::apply. Nonselected calls are untouched.
    pub fn apply_historical_capture(
        &self,
        mut trie: Trie,
        validator_accounts_update: &Option<ValidatorAccountsUpdate>,
        state: &ApplyState,
        receipts: &[Receipt],
        txs: SignedValidPeriodTransactions,
        provider: &dyn EpochInfoProvider,
        patch: near_primitives::sandbox::state_patch::SandboxStatePatch,
    ) -> Result<ApplyResult, RuntimeError> {
        let output = std::env::var_os("SAFE_NEAR_HISTORY_OUTPUT");
        let selected = output.is_some()
            && std::env::var("SAFE_NEAR_HISTORY_HEIGHT")
                .ok()
                .and_then(|x| x.parse::<u64>().ok())
                == Some(state.block_height)
            && std::env::var("SAFE_NEAR_HISTORY_SHARD")
                .ok()
                .and_then(|x| x.parse::<u64>().ok())
                == Some(state.shard_id.into());
        if !selected {
            return self.apply(
                trie,
                validator_accounts_update,
                state,
                receipts,
                txs,
                provider,
                patch,
            );
        }
        assert!(
            validator_accounts_update.is_none(),
            "first fixture must avoid epoch account updates"
        );
        assert!(
            patch.is_empty(),
            "sandbox patches cannot be captured as history"
        );
        let context = context(state);
        let pre_root = *trie.get_root();
        let flat_costs = trie.historical_flat_costs();
        let captured = std::sync::Arc::new(Mutex::new(BTreeMap::new()));
        let observer = trie.historical_map_storage(|inner| {
            std::sync::Arc::new(RecordingStorage {
                inner,
                bytes: captured.clone(),
            })
        });
        let (transactions, flags) = txs.get_potentially_expired_transactions_and_expiration_flags();
        let transactions = encoded(transactions);
        let flags = flags.to_vec();
        let recording = RecordingEpoch {
            inner: provider,
            entries: Mutex::new(BTreeMap::new()),
        };
        recording.chain_id();
        recording
            .shard_layout(&state.epoch_id)
            .expect("historical shard layout");
        // Retain the recorder already installed by NightshadeRuntime, including its proof limit.
        let result = self.apply(
            trie,
            validator_accounts_update,
            state,
            receipts,
            txs,
            &recording,
            patch,
        )?;
        let witness = result
            .proof
            .as_ref()
            .expect("capture requires the normal historical trie recorder");
        let near_primitives::state::PartialState::TrieValues(nodes) = &witness.nodes;
        let mut backing: BTreeMap<CryptoHash, std::sync::Arc<[u8]>> = nodes
            .iter()
            .map(|bytes| (near_primitives::hash::hash(bytes), bytes.clone()))
            .collect();
        // A warm compiled-contract cache may avoid reading original code bytes.
        // Fetch accessed base code by hash after execution, through the observer.
        for hash in &result.contract_updates.contract_accesses {
            observer
                .retrieve_raw_bytes(&hash.clone().into())
                .expect("accessed base contract code missing");
        }
        backing.extend(
            captured
                .lock()
                .unwrap()
                .iter()
                .map(|(hash, bytes)| (*hash, bytes.clone())),
        );
        let witness =
            near_primitives::state::PartialState::TrieValues(backing.into_values().collect());
        let expected = observations(&result);
        let input = json!({"format":FORMAT,"sourceRevision":REVISION,"context":context,
            "preStateRoot":encoded(&pre_root),"flatStorageCosts":flat_costs,
            "validatorAccountsUpdate":null,"transactions":transactions,"transactionValidity":flags,
            "incomingReceipts":encoded(receipts),"epochQueries":recording.entries.into_inner().unwrap(),
            "witness":encoded(&witness),"nativeExpected":expected,
            "captureTelemetry":{"originalStats":encoded(&result.stats),
                "bandwidthSchedulerTimeToRunMs":result.stats.bandwidth_scheduler.time_to_run_ms.to_string()}});
        // A capture is published only after an independent offline execution reproduces every observation.
        let replayed = replay(&input);
        if replayed != expected {
            let differing: Vec<_> = expected
                .as_object()
                .unwrap()
                .iter()
                .filter(|(key, value)| replayed.get(key.as_str()) != Some(value))
                .map(|(key, _)| key.as_str())
                .collect();
            let diagnostic =
                std::path::PathBuf::from(output.clone().unwrap()).with_extension("mismatch.json");
            let mut file = std::fs::OpenOptions::new()
                .write(true)
                .create_new(true)
                .open(diagnostic)
                .unwrap();
            file.write_all(
                &serde_json::to_vec(
                    &json!({"input":input,"replayed":replayed,"differing":differing}),
                )
                .unwrap(),
            )
            .unwrap();
            panic!("captured witness differs from original apply in {differing:?}");
        }
        let path = std::path::PathBuf::from(output.unwrap());
        let mut file = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(path)
            .expect("capture output exists or cannot be created");
        file.write_all(&serde_json::to_vec(&input).unwrap())
            .unwrap();
        file.sync_all().unwrap();
        Ok(result)
    }
}
