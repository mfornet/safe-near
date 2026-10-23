# NEAR runtime

The Wasm interpreter is connected to NEAR through three layers:

| Package | Entry point | Responsibility |
|---|---|---|
| `near-lean/vm` | `NearVM.run` | One contract call: metering and host functions |
| `near-lean/runtime` | `Near.apply` | Transactions, receipts, account state |
| `near-lean/chain` | block application | Ordering queued work across blocks |

Together they model receipts, promises and callbacks, storage, accounts, access
keys and gas.

## Trust and validation

- Consensus and cryptography are out of scope. Block context is an input, and
  proofs must state which inputs they trust.
- Conformance harnesses compare supported VM and runtime behavior with pinned
  nearcore adapters (`tools/runtime-*-reference`). They are tests, not an
  equivalence proof.

## Divergences from nearcore

Where the Lean code simplifies or omits nearcore behavior, it says so with a
comment starting `nearcore divergence:` (what differs and why), and the place
is listed here. The periodic check ([section 6](PERIODIC_CHECK.md#6-nearcore-divergence-divergence))
looks for simplifications that are neither marked nor listed.

| Where | What differs from nearcore | Why |
|---|---|---|

## Goals

- Replay NEAR history with bit-for-bit agreement, including runtime upgrades.
- Broader real-chain snapshots and fuzzing.
- Specify callback delivery under failed dependencies, resource limits and
  scheduling, and connect it to contract lifetime properties.
