# dump-runtime-config

Standalone Rust tool that writes nearcore's `RuntimeConfig` (gas costs, fees
and limits) as pretty-printed JSON, one file per protocol version, so the Lean
model of the NEAR runtime can load these parameters as data instead of
hand-copying numbers.

## nearcore crates used

| crate                  | version  |
|------------------------|----------|
| `near-parameters`      | `0.37.4` |
| `near-primitives-core` | `0.37.4` |
| `serde_json`           | `1`      |

`near-primitives-core 0.37.4` defines `PROTOCOL_VERSION = 86` (stable; the
`nightly` feature is not enabled) and `PROD_GENESIS_PROTOCOL_VERSION = 29`.

`RuntimeConfig` does not implement `serde::Serialize` in this version of
`near-parameters`, so the tool serializes
`near_parameters::view::RuntimeConfigView::from(config.clone())` instead. That
preserves the JSON shape returned by the `EXPERIMENTAL_protocol_config` RPC
method (`runtime_config` field), with a `safe_near` supplement for execution
parameters the view omits. The supplement reads refund penalties directly
from the pinned internal fees and evaluates the pinned `AccountCostIncrease`
protocol feature for each table. No execution constants are copied by hand. The Lean parser requires this
supplement; a bare RPC view is not a complete executable configuration.

## Build and run

```sh
cd tools/dump-runtime-config
cargo build --release
./target/release/dump-runtime-config <out_dir> [protocol_version ...]
```

* With explicit versions, one file per version is written.
* With no versions, the tool iterates protocol versions 29..=86, writes a file
  whenever the serialized JSON differs from the previous version, and always
  writes the file for the current `PROTOCOL_VERSION`.

Files are named `runtime_config_v<version>.json`.

The checked-in output lives in `near-lean/vm/configs/`; regenerate it with:

```sh
cd tools/dump-runtime-config
cargo run --release -- ../../near-lean/vm/configs
```

The crate is intentionally outside every Cargo workspace in the repository
(`[workspace]` table in `Cargo.toml`).

## What the view omits

`RuntimeConfigView` does not expose the following fields of
the internal `RuntimeConfig` in `near-parameters 0.37.4`:

* action fees for `ActionCosts` variants 16..=25:
  `deploy_global_contract_base/byte`, `use_global_contract_base/byte`,
  `deterministic_state_init_base/byte/entry`, `gas_key_transfer_base`,
  `gas_key_byte`, `gas_key_nonce_write_base`;
* `fees.gas_refund_penalty`, `fees.min_gas_refund_penalty` (NEP-536), now
  included in the `safe_near` supplement;
* `fees.deploy_global_contract_execution_base` and its per-byte companion
  (compute costs);
* `fees.storage_usage_config.global_contract_storage_amount_per_byte`;
* `bandwidth_scheduler_config` and `use_state_stored_receipt`;
* the per-host-function *compute* costs (`ExtCostsConfig` stores a
  `ParameterCost { gas, compute }` per entry; the view only emits `gas`).

As a consequence the parameter diffs at protocol versions 74 (bandwidth
scheduler) and 77 (global contracts) do not produce output files, and the
diffs at 46, 50, 55 and 63 are empty in this crate version. If any of the
remaining omitted fields are needed, extend the custom serializer that reads the internal
`RuntimeConfig` directly.
