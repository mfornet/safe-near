//! Corpus exporter for a stopped neard localnet (build-time overlay on `state-viewer`).
//!
//! For every new chunk in a block range it writes one raw bundle (a single JSON
//! document): the complete raw pre-state of the shard, the chunk's transactions and
//! incoming receipts in apply order, the full `ApplyState`-level context, the
//! validator data behind `EpochInfoProvider`, and the results neard itself recorded.
//! Before writing, the pinned `Runtime::apply` is run on exactly that data and must
//! reproduce every recorded result; a mismatch aborts the export.
//!
//! Usage: safe-near-corpus-export --home DIR --out DIR --from H --to H [--shard S]...
use anyhow::{Context, Result, anyhow, bail};
use borsh::to_vec as borsh_bytes;
use near_chain::chain::collect_receipts_from_response;
use near_chain::types::RuntimeAdapter;
use near_chain::{Chain, ChainStore, ChainStoreAccess, ReceiptFilter, get_incoming_receipts_for_shard};
use near_chain_configs::GenesisValidationMode;
use near_epoch_manager::shard_assignment::{shard_id_to_index, shard_id_to_uid};
use near_epoch_manager::{EpochManager, EpochManagerAdapter};
use near_primitives::apply::ApplyChunkReason;
use near_primitives::hash::CryptoHash;
use near_primitives::receipt::Receipt;
use near_primitives::transaction::{ExecutionOutcomeWithProof, SignedTransaction};
use near_primitives::types::{AccountId, Balance, EpochInfoProvider, ShardId};
use near_primitives::utils::{get_block_shard_id, get_outcome_id_block_hash};
use near_primitives::views::{ExecutionOutcomeView, ReceiptView, SignedTransactionView};
use near_store::{DBCol, Mode, NodeStorage};
use nearcore::{NightshadeRuntimeExt, load_config};
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions, ValidatorAccountsUpdate};
use serde_json::{Value, json};
use std::collections::{BTreeMap, HashMap};
use std::path::PathBuf;
use std::sync::Arc;

fn hex(bytes: &[u8]) -> String {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut text = String::with_capacity(bytes.len() * 2);
    for byte in bytes {
        text.push(DIGITS[(byte >> 4) as usize] as char);
        text.push(DIGITS[(byte & 15) as usize] as char);
    }
    text
}

fn sid(id: ShardId) -> u64 {
    id.to_string().parse().expect("shard ids are numbers")
}

fn hash_hex(hash: &CryptoHash) -> String {
    hex(hash.as_ref())
}

fn entries_json(entries: &[(Vec<u8>, Vec<u8>)]) -> Value {
    Value::Array(entries.iter().map(|(k, v)| json!([hex(k), hex(v)])).collect())
}

fn accounts_json(map: &HashMap<AccountId, Balance>) -> Value {
    let sorted: BTreeMap<String, String> =
        map.iter().map(|(k, v)| (k.to_string(), v.as_yoctonear().to_string())).collect();
    json!(sorted)
}

struct Args {
    home: PathBuf,
    out: PathBuf,
    from: u64,
    to: u64,
    shards: Vec<ShardId>,
}

fn parse_args() -> Result<Args> {
    let mut home = None;
    let mut out = None;
    let (mut from, mut to) = (None, None);
    let mut shards = Vec::new();
    let mut args = std::env::args().skip(1);
    while let Some(flag) = args.next() {
        let mut value = || args.next().ok_or_else(|| anyhow!("{flag} needs a value"));
        match flag.as_str() {
            "--home" => home = Some(PathBuf::from(value()?)),
            "--out" => out = Some(PathBuf::from(value()?)),
            "--from" => from = Some(value()?.parse()?),
            "--to" => to = Some(value()?.parse()?),
            "--shard" => shards.push(ShardId::new(value()?.parse()?)),
            other => bail!("unknown argument {other}"),
        }
    }
    Ok(Args {
        home: home.context("--home")?,
        out: out.context("--out")?,
        from: from.context("--from")?,
        to: to.context("--to")?,
        shards,
    })
}

fn main() -> Result<()> {
    let args = parse_args()?;
    let near_config = load_config(&args.home, GenesisValidationMode::Full)
        .map_err(|e| anyhow!("loading config: {e:#}"))?;
    let opener = NodeStorage::opener(
        &args.home,
        &near_config.config.store,
        near_config.config.cold_store.as_ref(),
        near_config.cloud_storage_context(),
    );
    let storage = opener.open_in_mode(Mode::ReadOnly)?;
    let store = storage.get_hot_store();
    let epoch_manager =
        EpochManager::new_arc_handle(store.clone(), &near_config.genesis.config, Some(&args.home));
    let runtime = nearcore::NightshadeRuntime::from_config(
        &args.home,
        store.clone(),
        &near_config,
        epoch_manager.clone(),
    )?;
    let chain_store =
        ChainStore::new(store.clone(), false, near_config.genesis.config.transaction_validity_period);
    let tries = runtime.get_tries();
    std::fs::create_dir_all(&args.out)?;

    let mut exported = 0usize;
    for height in args.from..=args.to {
        let Ok(block_hash) = chain_store.get_block_hash_by_height(height) else { continue };
        let block = chain_store.get_block(&block_hash).with_context(|| format!("block at height {height}"))?;
        if block.header().is_genesis() {
            continue;
        }
        let epoch_id = *block.header().epoch_id();
        let mut shard_ids: Vec<ShardId> = epoch_manager.get_shard_layout(&epoch_id)?.shard_ids().collect();
        shard_ids.sort();
        for shard_id in shard_ids {
            if !args.shards.is_empty() && !args.shards.contains(&shard_id) {
                continue;
            }
            let shard_index = shard_id_to_index(epoch_manager.as_ref(), shard_id, &epoch_id)?;
            let chunk_header = block.chunks()[shard_index].clone();
            if !chunk_header.is_new_chunk(height) {
                continue;
            }
            let bundle = export_chunk(
                &near_config, &store, &chain_store, epoch_manager.as_ref(), runtime.as_ref(),
                &tries, &block, shard_id,
            )
            .with_context(|| format!("height {height} shard {shard_id}"))?;
            let directory = args.out.join(format!("h{height:08}-s{shard_id}"));
            std::fs::create_dir_all(&directory)?;
            std::fs::write(directory.join("bundle.json"), serde_json::to_vec(&bundle)?)?;
            exported += 1;
        }
    }
    println!("exported {exported} chunk bundles");
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn export_chunk(
    near_config: &nearcore::NearConfig,
    store: &near_store::Store,
    chain_store: &ChainStore,
    epoch_manager: &near_epoch_manager::EpochManagerHandle,
    runtime: &nearcore::NightshadeRuntime,
    tries: &near_store::ShardTries,
    block: &near_primitives::block::Block,
    shard_id: ShardId,
) -> Result<Value> {
    let height = block.header().height();
    let block_hash = *block.header().hash();
    let prev_hash = *block.header().prev_hash();
    let prev_block = chain_store.get_block(&prev_hash).with_context(|| format!("previous block {prev_hash}"))?;
    let epoch_id = *block.header().epoch_id();
    let shard_uid = shard_id_to_uid(epoch_manager, shard_id, &epoch_id)?;
    let shard_index = shard_id_to_index(epoch_manager, shard_id, &epoch_id)?;
    let chunk_header = block.chunks()[shard_index].clone();
    let chunk = chain_store.get_chunk(&chunk_header.chunk_hash())?;

    let transactions: Vec<SignedTransaction> = chunk.to_transactions().to_vec();
    let validity = chain_store.compute_transaction_validity(prev_block.header(), &chunk);
    let shard_layout = epoch_manager.get_shard_layout_from_prev_block(&prev_hash)?;
    let response = get_incoming_receipts_for_shard(
        chain_store,
        epoch_manager,
        shard_id,
        &shard_layout,
        block_hash,
        prev_block.chunks()[shard_index].height_included(),
        ReceiptFilter::TargetShard,
    )?;
    let receipts: Vec<Receipt> = collect_receipts_from_response(&response);

    // Context, mirroring `NightshadeRuntime::process_state_update`.
    let block_context = Chain::get_apply_chunk_block_context(block, prev_block.header(), true);
    let runtime_epoch_id = epoch_manager.get_epoch_id_from_prev_block(&prev_hash)?;
    if runtime_epoch_id != epoch_id {
        bail!("block epoch id differs from the epoch id derived from the previous block");
    }
    let validator_update = if epoch_manager.is_next_block_epoch_start(&prev_hash)? {
        let (stake_info, validator_reward) = epoch_manager.read().compute_stake_return_info(&prev_hash)?;
        let on_shard = |id: &AccountId| shard_layout.account_id_to_shard_id(id) == shard_id;
        let last_proposals = chunk_header
            .prev_validator_proposals()
            .filter(|v| on_shard(v.account_id()))
            .fold(HashMap::new(), |mut acc, v| {
                let (account_id, stake) = v.account_and_stake();
                acc.insert(account_id, stake);
                acc
            });
        Some(ValidatorAccountsUpdate {
            stake_info: stake_info.into_iter().filter(|(a, _)| on_shard(a)).collect(),
            validator_rewards: validator_reward.into_iter().filter(|(a, _)| on_shard(a)).collect(),
            last_proposals,
            protocol_treasury_account_id: Some(near_config.genesis.config.protocol_treasury_account.clone())
                .filter(|a| on_shard(a)),
        })
    } else {
        None
    };
    let epoch_height = epoch_manager.get_epoch_height_from_prev_block(&prev_hash)?;
    let protocol_version = epoch_manager.get_epoch_protocol_version(&epoch_id)?;
    let prev_protocol_version =
        epoch_manager.get_epoch_protocol_version(&epoch_manager.get_epoch_id(&prev_hash)?)?;
    let config = runtime.get_runtime_config(protocol_version);
    let next_protocol = epoch_manager
        .get_next_epoch_protocol_version_from_prev_block(&prev_hash)
        .ok()
        .filter(|next| *next != protocol_version);
    let mut apply_state = ApplyState {
        apply_reason: ApplyChunkReason::UpdateTrackedShard,
        block_height: block_context.height,
        prev_block_hash: block_context.prev_block_hash,
        shard_id,
        epoch_id,
        epoch_height,
        gas_price: block_context.gas_price,
        block_timestamp: block_context.block_timestamp,
        gas_limit: Some(chunk_header.gas_limit()),
        random_seed: block_context.random_seed,
        current_protocol_version: protocol_version,
        config: Arc::new(config.clone()),
        next_wasm_config: None,
        cache: None,
        is_new_chunk: true,
        save_receipt_to_tx: false,
        congestion_info: block_context.congestion_info.clone(),
        bandwidth_requests: block_context.bandwidth_requests.clone(),
        trie_access_tracker_state: Default::default(),
        on_post_state_ready: None,
    };
    apply_state.next_wasm_config = None;

    // Complete pre-state.
    let prev_state_root = chunk_header.prev_state_root();
    let trie = tries.get_trie_for_shard(shard_uid, prev_state_root);
    let pre_entries: Vec<(Vec<u8>, Vec<u8>)> = trie
        .lock_for_iter()
        .iter()?
        .collect::<std::result::Result<_, _>>()
        .context("iterating the pre-state trie")?;

    // Re-apply with the pinned runtime, as `NightshadeRuntime::apply_chunk` does.
    let proof_limit = config.witness_config.main_storage_proof_size_soft_limit;
    let apply_trie = tries.get_trie_for_shard(shard_uid, prev_state_root).recording_reads_with_proof_size_limit(proof_limit);
    let result = Runtime::new()
        .apply(
            apply_trie,
            &validator_update,
            &apply_state,
            &receipts,
            SignedValidPeriodTransactions::new(transactions.clone(), validity.clone()),
            epoch_manager as &dyn EpochInfoProvider,
            Default::default(),
        )
        .map_err(|e| anyhow!("Runtime::apply failed: {e:?}"))?;

    // What neard recorded for this chunk.
    let extra = chain_store.get_chunk_extra(&block_hash, &shard_uid)?;
    let post_root = *extra.state_root();
    if result.state_root != post_root {
        bail!("re-applied state root {} differs from recorded {}", result.state_root, post_root);
    }
    let recorded_ids: Vec<CryptoHash> = store
        .get_ser(DBCol::OutcomeIds, &get_block_shard_id(&block_hash, shard_id))
        .unwrap_or_default();
    if recorded_ids.len() != result.outcomes.len() {
        bail!("{} recorded outcomes, {} re-applied", recorded_ids.len(), result.outcomes.len());
    }
    let mut outcomes = Vec::new();
    for (id, applied) in recorded_ids.iter().zip(&result.outcomes) {
        let recorded: ExecutionOutcomeWithProof = store
            .get_ser(DBCol::TransactionResultForBlock, &get_outcome_id_block_hash(id, &block_hash))
            .with_context(|| format!("missing recorded outcome {id}"))?;
        // `compute_usage` is not part of the Borsh encoding, so the database does not have it.
        if *id != applied.id || borsh_bytes(&recorded.outcome)? != borsh_bytes(&applied.outcome)? {
            bail!("recorded outcome {id} differs from the re-applied outcome: {:?} vs {:?}", recorded.outcome, applied.outcome);
        }
        let with_id = near_primitives::transaction::ExecutionOutcomeWithId { id: *id, outcome: recorded.outcome.clone() };
        let view = ExecutionOutcomeView::from(recorded.outcome.clone());
        outcomes.push(json!({
            "id": hash_hex(id),
            "borsh": hex(&borsh_bytes(&with_id)?),
            "view": serde_json::to_value(&view)?,
            "computeUsage": applied.outcome.compute_usage,
        }));
    }
    let recorded_outgoing = chain_store.get_outgoing_receipts(&block_hash, shard_id)?;
    if *recorded_outgoing != result.outgoing_receipts {
        bail!("recorded outgoing receipts differ from the re-applied ones");
    }
    let total_gas: u64 = result.outcomes.iter().map(|o| o.outcome.gas_burnt.as_gas()).sum();
    if total_gas != extra.gas_used().as_gas() {
        bail!("recorded gas used differs from the re-applied total");
    }
    let burnt = result.stats.balance.tx_burnt_amount.as_yoctonear()
        + result.stats.balance.other_burnt_amount.as_yoctonear()
        + result.stats.balance.slashed_burnt_amount.as_yoctonear()
        - result.stats.balance.subsidized_amount.as_yoctonear();
    if burnt != extra.balance_burnt().as_yoctonear() {
        bail!("recorded balance burnt differs from the re-applied value");
    }
    let proposals_re = borsh_bytes(&result.validator_proposals)?;
    let recorded_proposals: Vec<_> = extra.validator_proposals().collect();
    if borsh_bytes(&recorded_proposals)? != proposals_re {
        bail!("recorded validator proposals differ from the re-applied ones");
    }
    match (&result.congestion_info, extra.congestion_info()) {
        (Some(applied), recorded) if borsh_bytes(applied)? == borsh_bytes(&recorded)? => {}
        (None, _) => {}
        _ => bail!("recorded congestion info differs from the re-applied one"),
    }
    if let Some(recorded) = extra.bandwidth_requests() {
        if borsh_bytes(recorded)? != borsh_bytes(&result.bandwidth_requests)? {
            bail!("recorded bandwidth requests differ from the re-applied ones");
        }
    }
    let recorded_root = *extra.outcome_root();

    // Post-state, to express the state change as a difference.
    let post_entries: Vec<(Vec<u8>, Vec<u8>)> = tries
        .get_trie_for_shard(shard_uid, post_root)
        .lock_for_iter()
        .iter()?
        .collect::<std::result::Result<_, _>>()
        .context("iterating the post-state trie")?;
    let pre: BTreeMap<&Vec<u8>, &Vec<u8>> = pre_entries.iter().map(|(k, v)| (k, v)).collect();
    let post: BTreeMap<&Vec<u8>, &Vec<u8>> = post_entries.iter().map(|(k, v)| (k, v)).collect();
    let mut diff = Vec::new();
    for (key, value) in &post {
        if pre.get(key) != Some(value) {
            diff.push(json!([hex(key), hex(value)]));
        }
    }
    for key in pre.keys() {
        if !post.contains_key(key) {
            diff.push(json!([hex(key), Value::Null]));
        }
    }

    // Validators behind `EpochInfoProvider`.
    let epoch_info = epoch_manager.get_epoch_info(&epoch_id)?;
    let validators: Vec<Value> = epoch_info
        .validators_iter()
        .map(|v| json!([v.account_id().to_string(), v.stake().as_yoctonear().to_string()]))
        .collect();
    let total_stake = epoch_manager.validator_total_stake(&epoch_id)?;
    let minimum_stake = epoch_manager.minimum_stake(&prev_hash)?;

    let congestion_rows: Vec<Value> = {
        let mut rows = Vec::new();
        for (id, info) in apply_state.congestion_info.iter() {
            rows.push(json!([sid(*id), hex(&borsh_bytes(&info.congestion_info)?), info.missed_chunks_count]));
        }
        rows
    };
    let tx_rows: Vec<Value> = transactions
        .iter()
        .zip(&validity)
        .map(|(tx, ok)| Ok(json!({"borsh": hex(&borsh_bytes(tx)?), "valid": ok, "hash": hash_hex(&tx.get_hash()),
            "view": serde_json::to_value(SignedTransactionView::from(tx.clone()))?})))
        .collect::<Result<_>>()?;
    let treasury = &near_config.genesis.config.protocol_treasury_account;
    let update_json = match &validator_update {
        None => Value::Null,
        Some(update) => json!({
            "stakeInfo": accounts_json(&update.stake_info),
            "validatorRewards": accounts_json(&update.validator_rewards),
            "lastProposals": accounts_json(&update.last_proposals),
            "protocolTreasuryAccountId": update.protocol_treasury_account_id.as_ref().map(|a| a.to_string()),
        }),
    };

    Ok(json!({
        "formatVersion": 1,
        "meta": {
            "chainId": near_config.genesis.config.chain_id,
            "height": height,
            "blockHash": hash_hex(&block_hash),
            "prevBlockHash": hash_hex(&prev_hash),
            "chunkHash": hash_hex(&chunk_header.chunk_hash().0),
            "shardId": sid(shard_id),
            "shardUId": {"version": shard_uid.version, "shardId": shard_uid.shard_id},
            "protocolVersion": protocol_version,
            "prevEpochProtocolVersion": prev_protocol_version,
            "firstBlockOfVersion": protocol_version != prev_protocol_version,
            "nextEpochProtocolVersion": next_protocol,
            "protocolTreasury": treasury.to_string(),
        },
        "context": {
            "applyReason": "UpdateTrackedShard",
            "blockHeight": apply_state.block_height,
            "prevBlockHash": hash_hex(&apply_state.prev_block_hash),
            "epochId": hash_hex(&epoch_id.0),
            "epochHeight": apply_state.epoch_height,
            "gasPrice": apply_state.gas_price.as_yoctonear().to_string(),
            "blockTimestamp": apply_state.block_timestamp,
            "gasLimit": chunk_header.gas_limit().as_gas(),
            "randomSeed": hash_hex(&apply_state.random_seed),
            "currentProtocolVersion": protocol_version,
            "isNewChunk": true,
            "shardLayout": hex(&borsh_bytes(&shard_layout)?),
            "congestionInfo": congestion_rows,
            "bandwidthRequests": hex(&borsh_bytes(&apply_state.bandwidth_requests.shards_bandwidth_requests)?),
            "validatorAccountsUpdate": update_json,
            "epochInfo": {
                "chainId": near_config.genesis.config.chain_id,
                "validators": validators,
                "totalStake": total_stake.as_yoctonear().to_string(),
                "minimumStake": minimum_stake.as_yoctonear().to_string(),
            },
            "proofSizeSoftLimit": proof_limit,
        },
        "preState": {"root": hash_hex(&prev_state_root), "entries": entries_json(&pre_entries)},
        "inputs": {
            "transactions": tx_rows,
            "incomingReceipts": receipts.iter().map(|r| Ok(hex(&borsh_bytes(r)?))).collect::<Result<Vec<_>>>()?,
            "incomingReceiptViews": receipts.iter().map(|r| Ok(serde_json::to_value(ReceiptView::from(r.clone()))?)).collect::<Result<Vec<_>>>()?,
        },
        "expected": {
            "postStateRoot": hash_hex(&post_root),
            "outcomes": outcomes,
            "outcomeRoot": hash_hex(&recorded_root),
            "outgoingReceipts": recorded_outgoing.iter().map(|r| Ok(hex(&borsh_bytes(r)?))).collect::<Result<Vec<_>>>()?,
            "outgoingReceiptViews": recorded_outgoing.iter().map(|r| Ok(serde_json::to_value(ReceiptView::from(r.clone()))?)).collect::<Result<Vec<_>>>()?,
            "stateChanges": hex(&borsh_bytes(&result.state_changes)?),
            "stateDiff": diff,
            "gasUsed": extra.gas_used().as_gas(),
            "balanceBurnt": extra.balance_burnt().as_yoctonear().to_string(),
            "balanceStats": {
                "txBurnt": result.stats.balance.tx_burnt_amount.as_yoctonear().to_string(),
                "slashedBurnt": result.stats.balance.slashed_burnt_amount.as_yoctonear().to_string(),
                "otherBurnt": result.stats.balance.other_burnt_amount.as_yoctonear().to_string(),
                "gasDeficit": result.stats.balance.gas_deficit_amount.as_yoctonear().to_string(),
                "subsidized": result.stats.balance.subsidized_amount.as_yoctonear().to_string(),
            },
            "validatorProposals": hex(&proposals_re),
            "congestionInfo": hex(&borsh_bytes(&extra.congestion_info())?),
            "bandwidthRequests": extra.bandwidth_requests().map(|r| Ok::<_, anyhow::Error>(hex(&borsh_bytes(r)?))).transpose()?,
            "bandwidthSchedulerStateHash": hash_hex(&result.bandwidth_scheduler_state_hash),
            "delayedReceiptsCount": result.delayed_receipts_count,
            "processedYieldTimeouts": hex(&borsh_bytes(&result.processed_yield_timeouts)?),
            "contractUpdates": {"deployed": result.contract_updates.contract_deploys.len(), "called": result.contract_updates.contract_accesses.len()},
        },
    }))
}
