//! Full pinned Runtime::apply oracle on a real trie, with externally selected
//! receipt delivery. No VM outcome, result-data routing, or refunds are mocked.
use super::*;
use near_crypto::KeyType;
use near_primitives::account::Account;
use near_primitives::action::{DeleteAccountAction, DeployContractAction, FunctionCallAction};
use near_primitives::bandwidth_scheduler::BlockBandwidthRequests;
use near_primitives::congestion_info::{BlockCongestionInfo, ExtendedCongestionInfo};
use near_primitives::receipt::{ActionReceipt, ReceiptV0};
use near_primitives::shard_layout::{ShardLayout, ShardUId};
use near_primitives::test_utils::MockEpochInfoProvider;
use near_primitives::trie_key::TrieKey;
use near_store::test_utils::TestTriesBuilder;
use near_store::trie::AccessOptions;
use serde_json::{Value, json};
use std::{collections::BTreeMap, fs};

type Error = Box<dyn std::error::Error>;
fn number(v: &Value) -> Result<u64, Error> { Ok(v.as_u64().ok_or("expected u64")?) }
fn amount(v: &Value) -> Result<Balance, Error> { Ok(Balance::from_yoctonear(v.as_str().ok_or("expected decimal balance")?.parse()?)) }
fn bytes(v: &Value) -> Result<Vec<u8>, Error> { Ok(serde_json::from_value(v.clone())?) }
fn text(v: &Value) -> Result<String, Error> { Ok(v.as_str().ok_or("expected string")?.into()) }
fn account(v: &Value) -> Result<AccountId, Error> { Ok(v.as_str().ok_or("expected account")?.parse()?) }
fn action(v: &Value) -> Result<Action, Error> {
    Ok(match v["kind"].as_str().ok_or("missing action kind")? {
        "functionCall" => Action::FunctionCall(Box::new(FunctionCallAction {
            method_name: text(&v["method"])? , args: bytes(&v["args"])? ,
            gas: Gas::from_gas(number(&v["gas"])?), deposit: amount(&v["deposit"])? ,
        })),
        "transfer" => Action::Transfer(TransferAction { deposit: amount(&v["deposit"])? }),
        "deleteAccount" => Action::DeleteAccount(DeleteAccountAction { beneficiary_id: account(&v["beneficiary"])? }),
        "deployContract" => Action::DeployContract(DeployContractAction {code:fs::read(text(&v["codePath"])?)?}),
        _ => return Err("unsupported input action".into()),
    })
}
fn input_receipt(v: &Value, index: usize, block: usize) -> Result<Receipt, Error> {
    let predecessor = account(&v["predecessor"])?;
    let receipt_id = near_primitives::hash::hash(format!("input:{block}:{index}").as_bytes());
    Ok(Receipt::V0(ReceiptV0 {
        predecessor_id: predecessor.clone(), receiver_id: account(&v["receiver"])? , receipt_id,
        receipt: ReceiptEnum::Action(ActionReceipt {
            signer_id: predecessor, signer_public_key: PublicKey::empty(KeyType::ED25519),
            gas_price: Balance::from_yoctonear(100_000_000), output_data_receivers:vec![], input_data_ids:vec![],
            actions:v["actions"].as_array().ok_or("actions")?.iter().map(action).collect::<Result<_,_>>()?,
        }),
    }))
}
fn action_json(a: &Action) -> Result<Value, Error> {
    Ok(match a {
        Action::FunctionCall(a) => json!({"kind":"functionCall","method":a.method_name,"args":a.args,"gas":a.gas.as_gas(),"deposit":a.deposit.as_yoctonear().to_string()}),
        Action::Transfer(a) => json!({"kind":"transfer","deposit":a.deposit.as_yoctonear().to_string()}),
        Action::DeleteAccount(a) => json!({"kind":"deleteAccount","beneficiary":a.beneficiary_id}),
        Action::DeployContract(a) => json!({"kind":"deployContract","size":a.code.len()}),
        _ => return Err("unknown native output action (no silent normalization)".into()),
    })
}
fn receipt_json(r: &Receipt) -> Result<Value,Error> {
    let body=match r.versioned_receipt() {
        VersionedReceiptEnum::Action(a)=>json!({"kind":"action","signer":a.signer_id(),"signerPublicKey":borsh::to_vec(a.signer_public_key())?,"gasPrice":a.gas_price().as_yoctonear().to_string(),"refundTo":a.refund_to(),"inputs":a.input_data_ids(),"outputs":a.output_data_receivers(),"actions":a.actions().iter().map(action_json).collect::<Result<Vec<_>,_>>()?}),
        VersionedReceiptEnum::Data(d)=>json!({"kind":"data","dataId":d.data_id,"data":d.data}),
        _ => return Err("unsupported native receipt variant".into()),
    };
    Ok(json!({"id":r.receipt_id(),"predecessor":r.predecessor_id(),"receiver":r.receiver_id(),"body":body}))
}

fn status_json(status: &ExecutionStatus) -> Value {
    match status {
        ExecutionStatus::SuccessValue(bytes)=>json!({"kind":"value","value":bytes}),
        ExecutionStatus::SuccessReceiptId(id)=>json!({"kind":"receipt","receiptId":id}),
        ExecutionStatus::Failure(error)=>json!({"kind":"failure","error":format!("{error:?}")}),
        ExecutionStatus::Unknown=>json!({"kind":"unknown"}),
    }
}

pub fn execute(request: Value) -> Result<Value,Error> {
    let version:u32=number(&request["protocolVersion"])?.try_into()?;
    if version != 86 { return Err("receipt oracle currently pins protocol 86".into()); }
    let tries=TestTriesBuilder::new().build();
    let shard=ShardUId::single_shard();
    let mut seed=tries.new_trie_update(shard,CryptoHash::default());
    let mut accounts=Vec::new();
    let mut contracts=BTreeMap::new();
    for c in request["contracts"].as_array().ok_or("contracts")? {
        let id=account(&c["account"])?;
        let code=ContractCode::new(fs::read(text(&c["codePath"])?)?,None);
        seed.set_code(id.clone(), &code);
        contracts.insert(id,code);
    }
    for a in request["accounts"].as_array().ok_or("accounts")? {
        let id=account(&a["id"])?;
        let code=contracts.get(&id);
        let contract=code.map(|c|near_primitives::account::AccountContract::Local(*c.hash())).unwrap_or(near_primitives::account::AccountContract::None);
        let usage=182+code.map(|c|c.code().len() as u64).unwrap_or(0);
        set_account(&mut seed,id.clone(),&Account::new(amount(&a["balance"])?,Balance::ZERO,contract,usage));
        accounts.push(id);
    }
    seed.commit(StateChangeCause::InitialState);
    let changes=seed.finalize()?.trie_changes;
    let mut update=tries.store_update();
    let mut root=tries.apply_all(&changes,shard,&mut update);update.commit();
    let epoch=MockEpochInfoProvider::default();
    let runtime=Runtime::new();
    let store=near_parameters::RuntimeConfigStore::new(None);
    let mut config=(**store.get_config(version)).clone();
    // Supported independent backend on this host; production fees/limits remain.
    Arc::make_mut(&mut config.wasm_config).vm_kind=near_parameters::vm::VMKind::Wasmtime;
    let config=Arc::new(config);
    let mut ap=ApplyState {
        apply_reason:ApplyChunkReason::UpdateTrackedShard,block_height:1,prev_block_hash:Default::default(),shard_id:shard.shard_id(),epoch_id:Default::default(),epoch_height:0,
        gas_price:Balance::from_yoctonear(100_000_000),block_timestamp:0,gas_limit:None,random_seed:Default::default(),current_protocol_version:version,config,
        next_wasm_config:None,cache:Some(Box::new(near_vm_runner::FilesystemContractRuntimeCache::test()?)),is_new_chunk:true,save_receipt_to_tx:false,
        congestion_info:BlockCongestionInfo::new(ShardLayout::single_shard().shard_ids().map(|s|(s,ExtendedCongestionInfo::default())).collect()),
        bandwidth_requests:BlockBandwidthRequests::empty(),trie_access_tracker_state:Default::default(),on_post_state_ready:None,
    };
    let mut pending:Vec<Receipt>=vec![];
    let mut trace=vec![];
    let mut profiles=vec![];
    for (height,step) in request["steps"].as_array().ok_or("steps")?.iter().enumerate() {
        ap.block_height=height as u64+1;ap.block_timestamp=ap.block_height*1_000_000_000;
        ap.gas_limit=step.get("gasLimit").filter(|v|!v.is_null()).map(number).transpose()?.map(Gas::from_gas);
        let select=|r:&Receipt|match &step["deliver"] {
            Value::String(s) if s=="all"=>true,
            Value::String(s) if s=="none"=>false,
            Value::Array(ids)=>ids.iter().any(|id|id.as_str()==Some(r.receiver_id().as_str())),
            Value::Object(o)=>o.get("receivers").and_then(Value::as_array).is_some_and(|ids|
                ids.iter().any(|id|id.as_str()==Some(r.receiver_id().as_str()))) &&
                match o.get("kind").and_then(Value::as_str) {
                    Some("data")=>matches!(r.versioned_receipt(),VersionedReceiptEnum::Data(_)),
                    Some("action")=>matches!(r.versioned_receipt(),VersionedReceiptEnum::Action(_)),
                    _=>false,
                },
            _=>false,
        };
        let (mut incoming,held):(Vec<_>,Vec<_>)=pending.into_iter().partition(select);
        for (i,v) in step["inject"].as_array().ok_or("inject")?.iter().enumerate(){incoming.push(input_receipt(v,i,height)?);}
        let result=runtime.apply(tries.get_trie_for_shard(shard,root),&None,&ap,&incoming,SignedValidPeriodTransactions::empty(),&epoch,Default::default())?;
        let mut update=tries.store_update();root=tries.apply_all(&result.trie_changes,shard,&mut update);update.commit();
        if let Some(congestion)=result.congestion_info { ap.congestion_info.insert(shard.shard_id(),ExtendedCongestionInfo::new(congestion,0)); }
        let state=tries.new_trie_update(shard,root);
        let balances=accounts.iter().map(|id|Ok((id.to_string(),get_account(&state,id)?.map(|a|json!({"balance":a.amount().as_yoctonear().to_string(),"storageUsage":a.storage_usage()}))))).collect::<Result<BTreeMap<_,_>,Error>>()?;
        let mut storage=vec![];
        for k in request["inspectKeys"].as_array().ok_or("inspectKeys")? {
            let id=account(&k["account"])?;let key=bytes(&k["key"])?;
            // ContractData contains raw bytes, not a Borsh Vec.
            let raw=state.get(&TrieKey::ContractData{account_id:id.clone(),key:key.clone()},AccessOptions::DEFAULT)?.map(|v|v.to_vec());
            storage.push(json!({"account":id,"key":key,"value":raw}));
        }
        profiles.push(json!({"label":step["label"],"outcomes":result.outcomes.iter().map(|o| {
            let p=match &o.outcome.metadata {
                near_primitives::transaction::ExecutionMetadata::V3(p)=>Some(p.as_ref()),
                near_primitives::transaction::ExecutionMetadata::V4(m)=>Some(&m.profile),
                _=>None,
            };
            json!({"id":o.id,"profile":p.map(|p|json!({"ext":p.wasm_ext_profile.iter().filter(|(_,g)|g.as_gas()!=0).map(|(n,g)|(format!("{n:?}"),json!(g.as_gas()))).collect::<serde_json::Map<_,_>>(),"action":p.action_gas().as_gas(),"wasm":p.wasm_gas.as_gas()}))})
        }).collect::<Vec<_>>()}));
        let outcomes=result.outcomes.iter().map(|o|json!({"id":o.id,"executor":o.outcome.executor_id,"status":status_json(&o.outcome.status),"logs":o.outcome.logs,"gasBurnt":o.outcome.gas_burnt.as_gas(),"tokensBurnt":o.outcome.tokens_burnt.as_yoctonear().to_string(),"receipts":o.outcome.receipt_ids})).collect::<Vec<_>>();
        let outgoing=result.outgoing_receipts.iter().map(receipt_json).collect::<Result<Vec<_>,_>>()?;
        pending=held;pending.extend(result.outgoing_receipts);
        trace.push(json!({"label":step["label"],"incoming":incoming.iter().map(receipt_json).collect::<Result<Vec<_>,_>>()?,"outgoing":outgoing,"outcomes":outcomes,"accounts":balances,"storage":storage,"pending":pending.iter().map(receipt_json).collect::<Result<Vec<_>,_>>()?,"delayed":result.delayed_receipts_count}));
    }
    Ok(json!({"trace":trace,"profiles":profiles,"protocolVersion":version,"backend":"native Runtime::apply / Wasmtime / real trie"}))
}
