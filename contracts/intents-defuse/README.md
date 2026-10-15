# NEAR Intents verifier (defuse)

The NEAR Intents settlement contract (`intents.near`): multi-token (NEP-245) balances and signed intent execution.

- Code hash: `BtA1BEFNS619KkvXFsgcpQ21Tb5yMm32aaUkn7xNothk`
- Source: https://github.com/near/intents @ `16d04f6ec4401263f8914638710260da50bb46b0`, crate `contracts/defuse` v0.4.5
- Pinned by: nep330-metadata
- Build: cargo-near-reproducible, Rust 1.97.1, near-sdk 5.29.0, image `sourcescan/cargo-near:0.22.0-rust-1.97.1`
- Reproduced: exact

## Mainnet deployments

- `intents.near`

Deploy block heights and the block at which `contract.wasm` was fetched are in `contract.toml`.

## Rebuild

```
tools/verify_build.sh contracts/intents-defuse
```
