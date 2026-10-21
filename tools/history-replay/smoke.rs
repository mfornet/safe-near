//! Test-only bridge from the existing native oracle's synthetic example.
//! This never produces an archive anchor or a historical fixture.
use near_parameters::RuntimeConfigStore;
use near_primitives::apply::ApplyChunkReason;
use near_primitives::bandwidth_scheduler::BlockBandwidthRequests;
use near_primitives::congestion_info::{BlockCongestionInfo, ExtendedCongestionInfo};
use near_primitives::hash::CryptoHash;
use near_primitives::test_utils::MockEpochInfoProvider;
use near_primitives::types::{Balance, EpochId, EpochInfoProvider};
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use node_runtime::{ApplyState, Runtime, SignedValidPeriodTransactions};
use std::io::Read;
fn main() {
    let mut text = String::new();
    std::io::stdin().read_to_string(&mut text).unwrap();
    let request: serde_json::Value = serde_json::from_str(&text).unwrap();
    let provider = MockEpochInfoProvider::default();
    let layout = provider.shard_layout(&EpochId::default()).unwrap();
    let shard = layout.shard_uids().next().unwrap();
    let congestion = BlockCongestionInfo::new(
        layout
            .shard_ids()
            .map(|s| (s, ExtendedCongestionInfo::default()))
            .collect(),
    );
    let tries = TestTriesBuilder::new().with_shard_layout(layout).build();
    let mut entries: Vec<(Vec<u8>, Vec<u8>)> =
        serde_json::from_value(request["initialEntries"].clone()).unwrap();
    let contract: Option<Vec<u8>> = request
        .get("code")
        .map(|v| serde_json::from_value(v.clone()).unwrap());
    if let Some(code) = &contract {
        use near_primitives::account::{Account, AccountContract};
        use near_primitives::trie_key::TrieKey;
        let key = TrieKey::Account {
            account_id: "alice.near".parse().unwrap(),
        }
        .to_vec();
        let entry = entries.iter_mut().find(|(k, _)| *k == key).unwrap();
        let mut account: Account = borsh::from_slice(&entry.1).unwrap();
        account.set_contract(AccountContract::Local(near_primitives::hash::hash(code)));
        account.set_storage_usage(account.storage_usage() + code.len() as u64);
        entry.1 = borsh::to_vec(&account).unwrap();
        entries.push((
            TrieKey::ContractCode {
                account_id: "alice.near".parse().unwrap(),
            }
            .to_vec(),
            code.clone(),
        ));
    }
    let changes = tries
        .get_trie_for_shard(shard, CryptoHash::default())
        .update(
            entries.into_iter().map(|(k, v)| (k, Some(v))),
            AccessOptions::DEFAULT,
        )
        .unwrap();
    let mut update = tries.store_update();
    let root = tries.apply_all(&changes, shard, &mut update);
    update.commit();
    let protocol = request["protocolVersion"].as_u64().unwrap() as u32;
    let config = RuntimeConfigStore::new(None).get_config(protocol).clone();
    let b = &request["blocks"][0];
    let txs: Vec<Vec<u8>> = serde_json::from_value(b["transactions"].clone()).unwrap();
    let mut txs: Vec<_> = txs.iter().map(|v| borsh::from_slice(v).unwrap()).collect();
    if contract.is_some() {
        use near_crypto::{InMemorySigner, KeyType};
        use near_primitives::action::{Action, FunctionCallAction};
        use near_primitives::transaction::SignedTransaction;
        let alice = "alice.near".parse().unwrap();
        let signer = InMemorySigner::from_seed(alice, KeyType::ED25519, "safe-near-fixture-alice");
        txs = vec![SignedTransaction::from_actions(
            1,
            "alice.near".parse().unwrap(),
            "alice.near".parse().unwrap(),
            &signer,
            vec![Action::FunctionCall(Box::new(FunctionCallAction {
                method_name: request
                    .get("method")
                    .and_then(|v| v.as_str())
                    .unwrap_or("write")
                    .into(),
                args: vec![],
                gas: near_primitives::types::Gas::from_gas(150_000_000_000_000),
                deposit: Balance::ZERO,
            }))],
            CryptoHash::default(),
        )];
    }
    let count = txs.len();
    let state = ApplyState {
        apply_reason: ApplyChunkReason::UpdateTrackedShard,
        block_height: b["blockHeight"].as_u64().unwrap(),
        prev_block_hash: CryptoHash::default(),
        shard_id: shard.shard_id(),
        epoch_id: EpochId::default(),
        epoch_height: 0,
        gas_price: Balance::from_yoctonear(b["gasPrice"].as_str().unwrap().parse().unwrap()),
        block_timestamp: b["blockTimestamp"].as_u64().unwrap(),
        gas_limit: None,
        random_seed: CryptoHash::default(),
        current_protocol_version: protocol,
        config: config.clone(),
        next_wasm_config: None,
        cache: None,
        trie_access_tracker_state: Default::default(),
        is_new_chunk: true,
        save_receipt_to_tx: false,
        congestion_info: congestion,
        bandwidth_requests: BlockBandwidthRequests::empty(),
        on_post_state_ready: None,
    };
    let mut trie = tries.get_trie_for_shard(shard, root);
    trie.set_use_trie_accounting_cache(
        !request
            .get("flatStorageCosts")
            .and_then(|v| v.as_bool())
            .unwrap_or(false),
    );
    let trie = trie.recording_reads_with_proof_size_limit(
        config.witness_config.main_storage_proof_size_soft_limit,
    );
    let flags = request
        .get("transactionValidity")
        .map(|v| serde_json::from_value(v.clone()).unwrap())
        .unwrap_or(vec![true; count]);
    let result = Runtime::new()
        .apply_historical_capture(
            trie,
            &None,
            &state,
            &[],
            SignedValidPeriodTransactions::new(txs, flags),
            &provider,
            Default::default(),
        )
        .unwrap();
    println!(
        "{}",
        node_runtime::historical_capture::observations(&result)
    );
}
