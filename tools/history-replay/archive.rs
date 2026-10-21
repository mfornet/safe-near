// Included in the pinned state-viewer's apply_chain_range module.
// Runs after application and anchors the export to the archive's exact block/shard.
fn safe_near_history_anchor(
    input: &ChunkApplicationInput,
    read_store: &Store,
    genesis: &Genesis,
    result: &ApplyChunkResult,
) {
    use node_runtime::historical_capture::encoded;
    use serde_json::{Value, json};
    use std::io::Write;
    let Some(path) = std::env::var_os("SAFE_NEAR_HISTORY_OUTPUT") else {
        return;
    };
    if std::env::var("SAFE_NEAR_HISTORY_HEIGHT")
        .ok()
        .and_then(|s| s.parse::<u64>().ok())
        != Some(input.block.header().height())
        || std::env::var("SAFE_NEAR_HISTORY_SHARD")
            .ok()
            .and_then(|s| s.parse::<u64>().ok())
            != Some(input.chunk_header.shard_id().into())
    {
        return;
    }
    assert!(
        input
            .chunk_header
            .is_new_chunk(input.block.header().height()),
        "first historical fixture requires a new chunk"
    );
    let path = std::path::PathBuf::from(path);
    let witness: Value =
        serde_json::from_slice(&std::fs::read(&path).expect("runtime did not export witness"))
            .unwrap();
    let block_hash = input.block.header().hash();
    let shard_id = input.chunk_header.shard_id();
    let archive = read_store.chain_store();
    let extra = read_store
        .chunk_store()
        .get_chunk_extra(block_hash, &input.shard_uid)
        .expect("archive ChunkExtra missing");
    assert_eq!(
        extra.state_root(),
        &result.new_root,
        "archive state root mismatch"
    );
    assert_eq!(
        extra.outcome_root(),
        &result.outcome_root(),
        "archive outcome root mismatch"
    );
    assert_eq!(
        extra.gas_used(),
        result.total_gas_burnt,
        "archive gas mismatch"
    );
    assert_eq!(
        extra.balance_burnt(),
        result.total_balance_burnt,
        "archive balance burn mismatch"
    );
    assert_eq!(
        extra.gas_limit(),
        input.chunk_header.gas_limit(),
        "archive gas limit mismatch"
    );
    let ids = archive.get_outcomes_by_block_hash_and_shard_id(block_hash, shard_id);
    let old: Vec<_> = ids
        .into_iter()
        .map(|id| {
            let value = archive
                .get_outcome_by_id_and_block_hash(&id, block_hash)
                .expect("archive outcome missing");
            ExecutionOutcomeWithId {
                id,
                outcome: value.outcome,
            }
        })
        .collect();
    // Compare original persisted bytes, including error/status/logs/metadata. Compute
    // is intentionally not inferred from Borsh (nearcore omits it from that encoding).
    assert_eq!(
        encoded(&old),
        witness["nativeExpected"]["outcomes"],
        "archive outcome bytes mismatch"
    );
    let outgoing = ChainStore::new(
        read_store.clone(),
        false,
        genesis.config.transaction_validity_period,
    )
    .get_outgoing_receipts(block_hash, shard_id)
    .expect("archive outgoing receipts missing");
    assert_eq!(
        encoded(outgoing.as_ref()),
        witness["nativeExpected"]["outgoingReceipts"],
        "archive outgoing receipt bytes mismatch"
    );
    let proposals: Vec<_> = extra.validator_proposals().map(|v| v.into_v1()).collect();
    let fresh: Vec<_> = result
        .validator_proposals
        .iter()
        .cloned()
        .map(|v| v.into_v1())
        .collect();
    assert_eq!(
        encoded(&proposals),
        encoded(&fresh),
        "archive validator proposals mismatch"
    );
    let chain_store = ChainStore::new(
        read_store.clone(),
        false,
        genesis.config.transaction_validity_period,
    );
    let next_hash = chain_store
        .get_next_block_hash(block_hash)
        .expect("successor block missing");
    let next = chain_store
        .get_block(&next_hash)
        .expect("successor block missing");
    assert_eq!(next.header().prev_hash(), block_hash);
    assert_eq!(
        next.header().epoch_id(),
        input.block.header().epoch_id(),
        "first fixture must stay within one epoch"
    );
    let next_chunks: Vec<_> = next.chunks().iter_raw().cloned().collect();
    let next_chunk = next_chunks
        .iter()
        .find(|c| c.shard_id() == shard_id)
        .expect("successor shard missing");
    assert!(
        next_chunk.is_new_chunk(next.header().height()),
        "first fixture requires an immediately following new chunk"
    );
    assert_eq!(
        next_chunk.prev_state_root(),
        result.new_root,
        "successor header state commitment mismatch"
    );
    assert_eq!(
        next_chunk.prev_outcome_root(),
        &result.outcome_root(),
        "successor header outcome commitment mismatch"
    );
    let payload = json!({
        "format":"safe-near-archive-anchor-v1", "chainId":genesis.config.chain_id,
        "genesisConfig":genesis.config,
        "blockHash":block_hash,"blockHeight":input.block.header().height(),
        "shardId":shard_id,"shardUid":encoded(&input.shard_uid),
        "blockHeader":encoded(input.block.header()),"chunkHeader":encoded(&input.chunk_header),
        "chunkHeaders":encoded(&input.block.chunks().iter_raw().cloned().collect::<Vec<_>>()),
        "nextBlockHeader":encoded(next.header()),"nextChunkHeaders":encoded(&next_chunks),
        "chunkExtra":encoded(extra.as_ref()),"stateRoot":extra.state_root(),
        "outcomeRoot":extra.outcome_root(),"gasBurnt":extra.gas_used().as_gas().to_string(),
        "balanceBurnt":extra.balance_burnt().as_yoctonear().to_string(),
        "outcomes":encoded(&old),"outgoingReceipts":encoded(outgoing.as_ref()),
        "validatorProposalsV1":encoded(&proposals),
        "archiveComparisonEstablished":true
    });
    let mut file = std::fs::OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path.with_extension("archive.json"))
        .expect("archive anchor output exists");
    file.write_all(&serde_json::to_vec(&payload).unwrap())
        .unwrap();
    file.sync_all().unwrap();
}
