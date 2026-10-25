//! Chunk production: `ShardChunkWithEncoding::new`, the receipt proofs of the outgoing receipts, and
//! `create_partial_encoded_chunk`.
//!
//! The receipt grouping, `build_receipts_hashes` and `create_receipts_proofs_from_outgoing_receipts`
//! live in `near-chain`, which the oracle does not link; they are transcribed here from
//! `chain/chain/src/chain.rs` (nearcore 2.13.4, lines 4089 to 4151), and the Lean implementation of the
//! same functions (`NearNode.Chain.Apply`) was already compared with the roots of 1024 real blocks.

use crate::chain::*;
use crate::rng::G;
use crate::values::*;
use crate::{hex, Out};
use borsh::BorshSerialize;
use near_crypto::{InMemorySigner, KeyType, SecretKey};
use near_parameters::RuntimeConfigStore;
use near_primitives::action::{Action, FunctionCallAction, TransferAction};
use near_primitives::hash::{hash, CryptoHash};
use near_primitives::merkle::merklize;
use near_primitives::receipt::Receipt;
use near_primitives::shard_layout::ShardLayout;
use near_primitives::sharding::{ReceiptProof, ShardChunkWithEncoding, ShardProof};
use near_primitives::transaction::{SignedTransaction, Transaction, TransactionV0, ValidatedTransaction};
use near_primitives::types::{AccountId, Balance, Gas, ShardId};
use near_primitives::validator_signer::InMemoryValidatorSigner;
use near_primitives::version::PROTOCOL_VERSION;
use reed_solomon_erasure::galois_8::ReedSolomon;
use serde_json::json;
use std::collections::{BTreeMap, HashMap};

pub fn bh<T: BorshSerialize>(v: &T) -> String {
    hex(&borsh::to_vec(v).unwrap())
}

/// `Chain::group_receipts_by_shard`.
fn group(receipts: Vec<Receipt>, layout: &ShardLayout) -> Option<HashMap<ShardId, Vec<Receipt>>> {
    let mut result = HashMap::new();
    for receipt in receipts {
        let shard_id = receipt.receiver_shard_id(layout).ok()?;
        result.entry(shard_id).or_insert_with(Vec::new).push(receipt);
    }
    Some(result)
}

/// `Chain::build_receipts_hashes`.
fn receipts_hashes(receipts: &[Receipt], layout: &ShardLayout) -> Option<Vec<CryptoHash>> {
    let mut result_map: BTreeMap<usize, (ShardId, Vec<&Receipt>)> = BTreeMap::new();
    for info in layout.shard_infos() {
        result_map.insert(info.shard_index(), (info.shard_id(), vec![]));
    }
    for receipt in receipts {
        let shard_id = receipt.receiver_shard_id(layout).ok()?;
        let index = layout.get_shard_index(shard_id).ok()?;
        result_map.get_mut(&index)?.1.push(receipt);
    }
    Some(result_map.into_iter().map(|(_, (id, rs))| hash(&borsh::to_vec(&(id, rs)).unwrap())).collect())
}

/// `Chain::create_receipts_proofs_from_outgoing_receipts`.
pub fn receipt_proofs(
    layout: &ShardLayout,
    shard_id: ShardId,
    outgoing: Vec<Receipt>,
) -> Option<(CryptoHash, Vec<ReceiptProof>)> {
    let hashes = receipts_hashes(&outgoing, layout)?;
    let (root, proofs) = merklize(&hashes);
    let mut by_shard = group(outgoing, layout)?;
    let mut out = vec![];
    for (index, proof) in proofs.into_iter().enumerate() {
        let to = layout.get_shard_id(index).ok()?;
        let receipts = by_shard.remove(&to).unwrap_or_default();
        out.push(ReceiptProof(receipts, ShardProof { from_shard_id: shard_id, to_shard_id: to, proof }));
    }
    Some((root, out))
}

pub fn signer_text(seed: &str) -> SecretKey {
    SecretKey::from_seed(KeyType::ED25519, seed)
}

fn txs(g: &mut G, n: usize) -> Vec<SignedTransaction> {
    let config = RuntimeConfigStore::new(None);
    let config = config.get_config(PROTOCOL_VERSION);
    let mut out = vec![];
    for i in 0..n {
        let signer_id: AccountId = format!("user{}.test", g.below(5)).parse().unwrap();
        let sk = SecretKey::from_seed(KeyType::ED25519, &format!("tx-{i}-{}", g.below(1000)));
        let signer = InMemorySigner::from_secret_key(signer_id.clone(), sk);
        let receiver: AccountId = format!("contract{}.test", g.below(9)).parse().unwrap();
        let actions = match g.below(3) {
            0 => vec![Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(g.below(1000) as u128) })],
            1 => vec![Action::FunctionCall(Box::new(FunctionCallAction {
                method_name: "go".to_string(),
                args: g.bytes(60),
                gas: Gas::from_gas(10_000_000_000_000),
                deposit: Balance::ZERO,
            }))],
            _ => vec![
                Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(1) }),
                Action::Transfer(TransferAction { deposit: Balance::from_yoctonear(2) }),
            ],
        };
        let t = Transaction::V0(TransactionV0 {
            signer_id,
            public_key: signer.public_key(),
            nonce: g.below(1 << 20) as u64,
            receiver_id: receiver,
            block_hash: g.hash(),
            actions,
        });
        let (h, _) = t.get_hash_and_size();
        let tx = SignedTransaction::new(signer.sign(h.as_ref()), t);
        out.push(ValidatedTransaction::new(&config, tx, PROTOCOL_VERSION).map_err(|e| e.0).unwrap().into_signed_tx());
    }
    out
}

pub fn chunks(out: &mut Out) {
    let mut g = G::new(0x4348_554e, "validator/chunks");
    let layouts = [
        ShardLayout::single_shard(),
        ShardLayout::v0(4, 0),
        ShardLayout::v1(vec!["mm.test".parse().unwrap()], None, 1),
        ShardLayout::v2(
            vec!["test1".parse().unwrap(), "test2".parse().unwrap(), "test3".parse().unwrap()],
            (0..4).map(ShardId::new).collect(),
            None,
        ),
    ];
    let codes = [(1usize, 1usize), (1, 2), (2, 1), (3, 2), (5, 3), (17, 6)];
    let mut cases = 0;
    let mut attempt = 0;
    while cases < 30 {
        attempt += 1;
        let layout = &layouts[g.below(layouts.len())];
        let (d, p) = codes[g.below(codes.len())];
        let ntx = g.below(5);
        let transactions = txs(&mut g, ntx);
        let nr = g.below(7);
        let receipts: Vec<Receipt> = (0..nr).map(|_| receipt(&mut g)).collect();
        let shard_id = layout.shard_ids().nth(g.below(layout.shard_ids().count())).unwrap();
        let Some((root, proofs)) = receipt_proofs(layout, shard_id, receipts.clone()) else {
            assert!(attempt < 500, "no receipts the layout accepts");
            continue;
        };
        let seed = format!("chunk-producer-{cases}");
        let sk = signer_text(&seed);
        let account: AccountId = format!("producer{}.test", g.below(4)).parse().unwrap();
        let signer = InMemoryValidatorSigner::from_signer(InMemorySigner::from_secret_key(account.clone(), sk.clone()));
        let rs = ReedSolomon::new(d, p).unwrap();
        let validated: Vec<ValidatedTransaction> = {
            let config = RuntimeConfigStore::new(None);
            let config = config.get_config(PROTOCOL_VERSION);
            transactions
                .iter()
                .map(|t| ValidatedTransaction::new(&config, t.clone(), PROTOCOL_VERSION).map_err(|e| e.0).unwrap())
                .collect()
        };
        let (tx_root, _) = merklize(&transactions);
        let prev_block_hash = g.hash();
        let prev_state_root = g.hash();
        let prev_outcome_root = g.hash();
        let height = g.u64();
        let gas_used = g.gas();
        let gas_limit = g.gas();
        let burnt = g.balance();
        let proposals: Vec<_> = (0..g.below(3)).map(|_| stake(&mut g)).collect();
        let congestion = congestion_info(&mut g);
        let requests = bandwidth_requests(&mut g);
        let split = if g.bool() { Some(trie_split(&mut g)) } else { None };
        let (chunk, paths) = ShardChunkWithEncoding::new(
            prev_block_hash,
            prev_state_root,
            prev_outcome_root,
            height,
            shard_id,
            gas_used,
            gas_limit,
            burnt,
            proposals.clone(),
            validated,
            receipts.clone(),
            root,
            tx_root,
            congestion,
            requests.clone(),
            split.clone(),
            &signer,
            &rs,
            PROTOCOL_VERSION,
        );
        let encoded = chunk.to_encoded_shard_chunk();
        let n_parts = d + p;
        let mut partials = vec![];
        let ord_sets: Vec<(Vec<u64>, Vec<usize>)> = vec![
            (vec![], vec![0]),
            (vec![(n_parts - 1) as u64], vec![0, proofs.len()]),
            ((0..n_parts as u64).rev().step_by(2).collect(), vec![proofs.len()]),
        ];
        for (ords, keeps) in ord_sets {
            for proofs_kept in keeps {
                let kept: Vec<ReceiptProof> = proofs.iter().take(proofs_kept).cloned().collect();
                let partial = encoded.create_partial_encoded_chunk(ords.clone(), kept, &paths);
                partials.push(json!({"ords": ords, "receiptProofs": proofs_kept, "partial": bh(&partial)}));
            }
        }
        let shard_u64: u64 = shard_id.into();
        out.line("chunk", json!({
            "protocol": PROTOCOL_VERSION,
            "account": account.to_string(),
            "secret": sk.to_string(),
            "data": d, "parity": p,
            "layout": bh(layout),
            "shardId": shard_u64,
            "prevBlockHash": hex(&prev_block_hash.0),
            "prevStateRoot": hex(&prev_state_root.0),
            "prevOutcomeRoot": hex(&prev_outcome_root.0),
            "height": height,
            "prevGasUsed": bh(&gas_used),
            "gasLimit": bh(&gas_limit),
            "prevBalanceBurnt": bh(&burnt),
            "validatorProposals": bh(&proposals),
            "transactions": bh(&transactions),
            "receipts": bh(&receipts),
            "congestionInfo": bh(&congestion),
            "bandwidthRequests": bh(&requests),
            "proposedSplit": bh(&split),
            "outgoingReceiptsRoot": hex(&root.0),
            "txRoot": hex(&tx_root.0),
            "receiptProofs": bh(&proofs),
            "receiptsHashes": receipts_hashes(&receipts, layout).unwrap().iter().map(|h| hex(&h.0)).collect::<Vec<_>>(),
            "shardChunk": bh(chunk.to_shard_chunk()),
            "encodedChunk": bh(encoded),
            "paths": bh(&paths),
            "chunkHash": hex(&encoded.chunk_hash().0.0),
            "partials": partials,
        }));
        cases += 1;
    }
}
