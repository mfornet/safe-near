//! Independent VM oracle using the published, pinned nearcore executor.
//! Input and output are JSON; storage and receipt actions are byte-exact.
mod external;
use external::MethodValidatingExternal;

use anyhow::{Context, Result, bail};
use near_parameters::RuntimeConfigStore;
use near_primitives_core::{
    account::AccountContract,
    types::{Balance, Gas},
};
use near_vm_runner::{
    ContractCode,
    logic::{
        VMContext,
        mocks::mock_external::{MockAction, MockedExternal},
        types::{GlobalContractIdentifier, PromiseResult, ReturnData},
    },
};
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
    collections::HashMap,
    io::{self, Read},
    rc::Rc,
    sync::Arc,
};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    code_path: String,
    wat_path: String,
    config_dir: String,
    protocol_version: u32,
    method: String,
    current_account_id: String,
    signer_account_id: String,
    signer_account_pk: Vec<u8>,
    predecessor_account_id: String,
    input: Vec<u8>,
    promise_results: Vec<Option<Vec<u8>>>,
    block_height: u64,
    block_timestamp: u64,
    epoch_height: u64,
    account_balance: String,
    account_locked_balance: String,
    storage_usage: u64,
    attached_deposit: String,
    prepaid_gas: u64,
    random_seed: Vec<u8>,
    view: bool,
    output_data_receivers: Vec<String>,
    storage: Vec<(Vec<u8>, Vec<u8>)>,
    #[serde(default)]
    validate_action_method_utf8: bool,
    /// The current epoch's validators and their stakes (decimal yoctoNEAR).
    #[serde(default)]
    validators: Vec<(String, String)>,
}

fn balance(value: &str) -> Result<Balance> {
    Ok(Balance::from_yoctonear(value.parse::<u128>()?))
}

fn action_json(action: &MockAction) -> Result<(u64, Value)> {
    Ok(match action {
        MockAction::CreateAccount { receipt_index } => {
            (*receipt_index, json!({"kind":"createAccount"}))
        }
        MockAction::DeployContract {
            receipt_index,
            code,
        } => (
            *receipt_index,
            json!({"kind":"deployContract", "code":code}),
        ),
        MockAction::FunctionCallWeight {
            receipt_index,
            method_name,
            args,
            attached_deposit,
            prepaid_gas,
            gas_weight,
        } => {
            if gas_weight.0 != 0 {
                bail!("weighted gas allocation is not yet normalized")
            }
            (
                *receipt_index,
                json!({"kind":"functionCall", "method":method_name, "args":args,
                "deposit":attached_deposit.as_yoctonear().to_string(), "gas":prepaid_gas.as_gas()}),
            )
        }
        MockAction::Transfer {
            receipt_index,
            deposit,
        } => (
            *receipt_index,
            json!({"kind":"transfer", "deposit":deposit.as_yoctonear().to_string()}),
        ),
        MockAction::Stake {
            receipt_index,
            stake,
            public_key,
        } => (
            *receipt_index,
            json!({"kind":"stake", "stake":stake.as_yoctonear().to_string(), "publicKey":borsh::to_vec(public_key)?}),
        ),
        MockAction::DeleteKey {
            receipt_index,
            public_key,
        } => (
            *receipt_index,
            json!({"kind":"deleteKey", "publicKey":borsh::to_vec(public_key)?}),
        ),
        MockAction::UseGlobalContract {
            receipt_index,
            contract_id,
        } => (
            *receipt_index,
            match contract_id {
                GlobalContractIdentifier::CodeHash(hash) => {
                    json!({"kind":"useGlobalContract", "codeHash":hash.0.to_vec()})
                }
                GlobalContractIdentifier::AccountId(account_id) => {
                    json!({"kind":"useGlobalContract", "accountId":account_id.as_bytes()})
                }
            },
        ),
        MockAction::DeleteAccount {
            receipt_index,
            beneficiary_id,
        } => (
            *receipt_index,
            json!({"kind":"deleteAccount", "beneficiaryId":beneficiary_id.as_bytes()}),
        ),
        MockAction::AddKeyWithFullAccess {
            receipt_index,
            public_key,
            nonce,
        } => (
            *receipt_index,
            json!({"kind":"addKey", "publicKey":borsh::to_vec(public_key)?, "nonce":nonce,
                "permission":{"kind":"fullAccess"}}),
        ),
        MockAction::AddKeyWithFunctionCall {
            receipt_index,
            public_key,
            nonce,
            allowance,
            receiver_id,
            method_names,
        } => (
            *receipt_index,
            json!({"kind":"addKey", "publicKey":borsh::to_vec(public_key)?, "nonce":nonce,
                "permission":{"kind":"functionCall", "allowance":allowance.map(|a|a.as_yoctonear().to_string()),
                    "receiverId":receiver_id.as_bytes(), "methodNames":method_names.join(&[b','][..])}}),
        ),
        other => bail!("reference action has no normalization: {other:?}"),
    })
}

fn normalize_receipts(actions: &[MockAction]) -> Result<(Vec<Value>, HashMap<u64, usize>)> {
    let mut indices = HashMap::new();
    let mut receipts = Vec::new();
    for (i, action) in actions.iter().enumerate() {
        if let MockAction::CreateReceipt { receiver_id, .. } = action {
            indices.insert(i as u64, receipts.len());
            receipts.push(
                json!({"receiverId":receiver_id.as_bytes(), "dependencies":[], "actions":[]}),
            );
        }
    }
    for (i, action) in actions.iter().enumerate() {
        if let MockAction::CreateReceipt {
            receipt_indices, ..
        } = action
        {
            let deps: Result<Vec<usize>> = receipt_indices
                .iter()
                .map(|id| {
                    indices
                        .get(id)
                        .copied()
                        .context("dependency does not name a receipt")
                })
                .collect();
            receipts[indices[&(i as u64)]]["dependencies"] = json!(deps?);
        } else {
            let (receipt_id, normalized) = action_json(action)?;
            let index = *indices
                .get(&receipt_id)
                .context("action does not name a receipt")?;
            receipts[index]["actions"]
                .as_array_mut()
                .unwrap()
                .push(normalized);
        }
    }
    Ok((receipts, indices))
}

fn execute(request: Request) -> Result<Value> {
    // Paths are shared with the Lean driver; only the Rust oracle reads Wasm.
    let _ = (&request.wat_path, &request.config_dir);
    if request.protocol_version > 86 {
        bail!("reference supports protocol versions through 86")
    }
    let bytes = std::fs::read(&request.code_path).context("reading deployed Wasm")?;
    let code = ContractCode::new(bytes, None);
    let mut ext = MethodValidatingExternal {
        inner: MockedExternal::with_code(code),
        validate_action_method_utf8: request.validate_action_method_utf8,
    };
    for (account_id, stake) in &request.validators {
        ext.inner.validators.insert(account_id.parse().context("validator account id")?, balance(stake)?);
    }
    for (key, value) in &request.storage {
        if ext
            .inner
            .fake_trie
            .insert(key.clone(), value.clone())
            .is_some()
        {
            bail!("duplicate storage key")
        }
    }
    let configs = RuntimeConfigStore::new(None);
    let config = configs.get_config(request.protocol_version);
    // Only the default `wasmtime_vm` engine is compiled in. Configs that name NearVm keep it on
    // x86_64 (`replace_with_wasmtime_if_unsupported` swaps it elsewhere), so pin Wasmtime here
    // to get the same oracle on every host.
    let mut wasm_config = near_parameters::vm::Config::clone(&config.wasm_config);
    wasm_config.vm_kind = near_parameters::vm::VMKind::Wasmtime;
    let wasm_config = Arc::new(wasm_config);
    let context = VMContext {
        current_account_id: request.current_account_id.parse()?,
        signer_account_id: request.signer_account_id.parse()?,
        signer_account_pk: request.signer_account_pk,
        predecessor_account_id: request.predecessor_account_id.parse()?,
        refund_to_account_id: request.predecessor_account_id.parse()?,
        input: Rc::from(request.input),
        promise_results: request
            .promise_results
            .into_iter()
            .map(|result| match result {
                Some(value) => PromiseResult::Successful(Rc::from(value)),
                None => PromiseResult::Failed,
            })
            .collect::<Vec<_>>()
            .into(),
        block_height: request.block_height,
        block_timestamp: request.block_timestamp,
        epoch_height: request.epoch_height,
        account_balance: balance(&request.account_balance)?,
        account_locked_balance: balance(&request.account_locked_balance)?,
        storage_usage: request.storage_usage,
        account_contract: AccountContract::Local(ext.inner.code_hash),
        attached_deposit: balance(&request.attached_deposit)?,
        prepaid_gas: Gas::from_gas(request.prepaid_gas),
        random_seed: request.random_seed,
        view_config: request
            .view
            .then_some(near_primitives_core::config::ViewConfig {
                max_gas_burnt: config.wasm_config.limit_config.max_gas_burnt,
            }),
        output_data_receivers: request
            .output_data_receivers
            .iter()
            .map(|a| a.parse())
            .collect::<std::result::Result<_, _>>()?,
    };
    let prepared = near_vm_runner::prepare(
        &ext.inner,
        Arc::clone(&wasm_config),
        None,
        context.make_gas_counter(&wasm_config),
        &request.method,
    );
    let outcome = near_vm_runner::run(prepared, &mut ext, &context, Arc::clone(&config.fees))?;
    // The normalized seam includes rollback, as NearVM.run does. Failed VM
    // balance/storage fields are ignored by nearcore's receipt executor.
    let failed = outcome.aborted.is_some();
    let (receipts, indices) = if failed {
        (vec![], HashMap::new())
    } else {
        normalize_receipts(&ext.inner.action_log)?
    };
    let return_data = if failed {
        json!({"kind":"none"})
    } else {
        match outcome.return_data {
            ReturnData::None => json!({"kind":"none"}),
            ReturnData::Value(value) => json!({"kind":"value", "bytes":value}),
            ReturnData::ReceiptIndex(id) => {
                json!({"kind":"receipt", "index":indices.get(&id).context("returned receipt does not exist")?})
            }
        }
    };
    let mut storage: Vec<_> = if failed {
        request.storage
    } else {
        ext.inner.fake_trie.into_iter().collect()
    };
    storage.sort_by(|a, b| a.0.cmp(&b.0));
    let ext_profile: serde_json::Map<String, Value> = outcome
        .profile
        .wasm_ext_profile
        .iter()
        .filter(|(_, gas)| gas.as_gas() != 0)
        .map(|(name, gas)| (format!("{name:?}"), json!(gas.as_gas())))
        .collect();
    Ok(json!({
        "balance":if failed { request.account_balance } else { outcome.balance.as_yoctonear().to_string() },
        "storageUsage":if failed { request.storage_usage } else { outcome.storage_usage },
        "returnData":return_data,
        "gasBurnt":outcome.burnt_gas.as_gas(),
        "gasUsed":if failed { outcome.burnt_gas.as_gas() } else { outcome.used_gas.as_gas() },
        "logs":outcome.logs, "storage":storage, "receipts":receipts,
        "aborted":outcome.aborted.map(|e|e.to_string()), "issue":null,
        "subsidizedAmount":outcome.subsidized_amount.as_yoctonear().to_string(),
        "gasProfile": {"ext":ext_profile, "actionBurnt":outcome.profile.action_gas().as_gas(),
            "wasm":outcome.profile.wasm_gas.as_gas()}
    }))
}

fn main() -> Result<()> {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input)?;
    let request: Request = serde_json::from_str(&input).context("invalid execution request")?;
    println!("{}", execute(request)?);
    Ok(())
}
