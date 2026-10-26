//! Dump nearcore's `RuntimeConfig` as pretty-printed JSON for given protocol
//! versions, so that other implementations (e.g. a Lean model of the NEAR
//! runtime) can load gas costs, fees and limits as data.
//!
//! Usage: `dump-runtime-config <out_dir> [protocol_version ...]`
//!
//! With no versions given, the current `PROTOCOL_VERSION` is dumped together
//! with every protocol version (from 29, the mainnet genesis version, upwards)
//! at which the serialized config differs from the previous version.

use std::path::Path;
use std::process::ExitCode;

use near_parameters::view::RuntimeConfigView;
use near_parameters::{ActionCosts, ExtCosts, RuntimeConfig, RuntimeConfigStore};
use near_primitives_core::types::ProtocolVersion;
use near_primitives_core::version::{
    ProtocolFeature, PROD_GENESIS_PROTOCOL_VERSION, PROTOCOL_VERSION,
};
use serde::Serialize;
use serde_json::{json, Map, Value};
use strum::IntoEnumIterator;

#[derive(Serialize)]
struct ConfigDump {
    #[serde(flatten)]
    view: RuntimeConfigView,
    // RuntimeConfigView omits these execution parameters. Keep their provenance
    // explicit instead of silently choosing zero or copying protocol constants.
    runtime_finance: Value,
    runtime_admission: Value,
    // Global-contract and gas-key execution parameters, also omitted by the view.
    runtime_extra: Value,
    // Compute costs where they differ from the gas cost (the view has gas only).
    compute_costs: Value,
}

/// `{ext: {cost: compute}, action_execution: {cost: compute}, action_send: {cost: compute}}`,
/// listing only the parameters whose compute cost is not their gas cost.
fn compute_json(config: &RuntimeConfig) -> Value {
    let ext_costs = &config.wasm_config.ext_costs;
    let mut ext = Map::new();
    for cost in ExtCosts::iter() {
        if ext_costs.compute_cost(cost) != ext_costs.gas_cost(cost).as_gas() {
            ext.insert(cost.to_string(), json!(ext_costs.compute_cost(cost)));
        }
    }
    let mut execution = Map::new();
    let mut send = Map::new();
    for cost in ActionCosts::iter() {
        let fee = config.fees.fee(cost);
        if fee.execution.compute() != fee.execution.gas().as_gas() {
            execution.insert(cost.to_string(), json!(fee.execution.compute()));
        }
        for component in [&fee.send_sir, &fee.send_not_sir] {
            if component.compute() != component.gas().as_gas() {
                send.insert(cost.to_string(), json!(component.compute()));
            }
        }
    }
    json!({"ext": ext, "action_execution": execution, "action_send": send})
}

fn fee_json(config: &RuntimeConfig, cost: ActionCosts) -> Value {
    let fee = config.fees.fee(cost);
    json!({
        "send_sir": fee.send_sir.gas().as_gas(),
        "send_not_sir": fee.send_not_sir.gas().as_gas(),
        "execution": fee.execution.gas().as_gas(),
    })
}

fn config_json(store: &RuntimeConfigStore, version: ProtocolVersion) -> String {
    let config: &RuntimeConfig = store.get_config(version);
    // `RuntimeConfig` itself does not implement `Serialize` in this version of
    // `near-parameters`; `RuntimeConfigView` is the JSON-stable representation
    // used by the `EXPERIMENTAL_protocol_config` RPC.
    let view = RuntimeConfigView::from(config.clone());
    let dump = ConfigDump {
        view,
        compute_costs: compute_json(config),
        runtime_finance: json!({
            "account_cost_increase": ProtocolFeature::AccountCostIncrease.enabled(version),
            "gas_refund_penalty": [config.fees.gas_refund_penalty.numer(), config.fees.gas_refund_penalty.denom()],
            "min_gas_refund_penalty": config.fees.min_gas_refund_penalty.as_gas(),
        }),
        runtime_admission: json!({
            "strict_nonce": ProtocolFeature::StrictNonce.enabled(version),
            "v1_transactions": ProtocolFeature::GasKeys.enabled(version),
            "transaction_size_includes_signature": ProtocolFeature::PostQuantumSignatures.enabled(version),
            "unique_chunk_transactions": ProtocolFeature::UniqueChunkTransactions.enabled(version),
        }),
        runtime_extra: json!({
            "action_fees": {
                "deploy_global_contract_base": fee_json(config, ActionCosts::deploy_global_contract_base),
                "deploy_global_contract_byte": fee_json(config, ActionCosts::deploy_global_contract_byte),
                "use_global_contract_base": fee_json(config, ActionCosts::use_global_contract_base),
                "use_global_contract_byte": fee_json(config, ActionCosts::use_global_contract_byte),
                "gas_key_transfer_base": fee_json(config, ActionCosts::gas_key_transfer_base),
                "gas_key_byte": fee_json(config, ActionCosts::gas_key_byte),
                "gas_key_nonce_write_base": fee_json(config, ActionCosts::gas_key_nonce_write_base),
            },
            "global_contract_storage_amount_per_byte":
                config.fees.storage_usage_config.global_contract_storage_amount_per_byte.as_yoctonear().to_string(),
            "deploy_global_contract_execution_base":
                config.fees.deploy_global_contract_execution_base,
            "deploy_global_contract_execution_per_byte":
                config.fees.deploy_global_contract_execution_per_byte,
            "include_deploy_global_contract_outcome_burnt_storage":
                ProtocolFeature::IncludeDeployGlobalContractOutcomeBurntStorage.enabled(version),
            "global_contract_distribution_nonce":
                ProtocolFeature::GlobalContractDistributionNonce.enabled(version),
            "fix_delete_account_global_contract_storage_usage":
                ProtocolFeature::FixDeleteAccountGlobalContractStorageUsage.enabled(version),
            "fix_delegate_action_deposit_with_function_call_error":
                ProtocolFeature::FixDelegateActionDepositWithFunctionCallError.enabled(version),
            "delegate_v2": ProtocolFeature::DelegateV2.enabled(version),
            "yield_with_id": ProtocolFeature::YieldWithId.enabled(version),
            "eth_implicit_global_contract": ProtocolFeature::EthImplicitGlobalContract.enabled(version),
            "enforce_per_receipt_storage_proof_limit":
                ProtocolFeature::EnforcePerReceiptStorageProofLimit.enabled(version),
        }),
    };
    serde_json::to_string_pretty(&dump).expect("runtime configuration serialization cannot fail")
}

fn write_config(out_dir: &Path, version: ProtocolVersion, json: &str) -> std::io::Result<()> {
    let path = out_dir.join(format!("runtime_config_v{version}.json"));
    std::fs::write(&path, format!("{json}\n"))?;
    println!("wrote {}", path.display());
    Ok(())
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let Some(out_dir) = args.first() else {
        eprintln!("usage: dump-runtime-config <out_dir> [protocol_version ...]");
        return ExitCode::from(2);
    };
    let out_dir = Path::new(out_dir);
    if let Err(err) = std::fs::create_dir_all(out_dir) {
        eprintln!("cannot create {}: {err}", out_dir.display());
        return ExitCode::FAILURE;
    }

    let mut versions: Vec<ProtocolVersion> = Vec::new();
    for arg in &args[1..] {
        match arg.parse::<ProtocolVersion>() {
            Ok(v) => versions.push(v),
            Err(_) => {
                eprintln!("invalid protocol version: {arg:?}");
                return ExitCode::from(2);
            }
        }
    }

    let store = RuntimeConfigStore::new(None);

    if versions.is_empty() {
        // Every version at which the config changes, plus the current version.
        let mut previous: Option<String> = None;
        for version in PROD_GENESIS_PROTOCOL_VERSION..=PROTOCOL_VERSION {
            let json = config_json(&store, version);
            let changed = previous.as_deref() != Some(json.as_str());
            if changed || version == PROTOCOL_VERSION {
                if let Err(err) = write_config(out_dir, version, &json) {
                    eprintln!("cannot write config for version {version}: {err}");
                    return ExitCode::FAILURE;
                }
            }
            previous = Some(json);
        }
    } else {
        for version in versions {
            let json = config_json(&store, version);
            if let Err(err) = write_config(out_dir, version, &json) {
                eprintln!("cannot write config for version {version}: {err}");
                return ExitCode::FAILURE;
            }
        }
    }
    println!("current PROTOCOL_VERSION = {PROTOCOL_VERSION}");
    ExitCode::SUCCESS
}
