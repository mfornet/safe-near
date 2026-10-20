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
use near_parameters::{RuntimeConfig, RuntimeConfigStore};
use near_primitives_core::types::ProtocolVersion;
use near_primitives_core::version::{
    ProtocolFeature, PROD_GENESIS_PROTOCOL_VERSION, PROTOCOL_VERSION,
};
use serde::Serialize;
use serde_json::{json, Value};

#[derive(Serialize)]
struct ConfigDump {
    #[serde(flatten)]
    view: RuntimeConfigView,
    // RuntimeConfigView omits these execution parameters. Keep their provenance
    // explicit instead of silently choosing zero or copying protocol constants.
    runtime_finance: Value,
    runtime_admission: Value,
}

fn config_json(store: &RuntimeConfigStore, version: ProtocolVersion) -> String {
    let config: &RuntimeConfig = store.get_config(version);
    // `RuntimeConfig` itself does not implement `Serialize` in this version of
    // `near-parameters`; `RuntimeConfigView` is the JSON-stable representation
    // used by the `EXPERIMENTAL_protocol_config` RPC.
    let view = RuntimeConfigView::from(config.clone());
    let dump = ConfigDump {
        view,
        runtime_finance: json!({
            "account_cost_increase": ProtocolFeature::AccountCostIncrease.enabled(version),
            "gas_refund_penalty": [config.fees.gas_refund_penalty.numer(), config.fees.gas_refund_penalty.denom()],
            "min_gas_refund_penalty": config.fees.min_gas_refund_penalty.as_gas(),
        }),
        runtime_admission: json!({
            "strict_nonce": ProtocolFeature::StrictNonce.enabled(version),
            "v1_transactions": ProtocolFeature::GasKeys.enabled(version),
            "transaction_size_includes_signature": ProtocolFeature::PostQuantumSignatures.enabled(version),
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
