# NEAR Runtime

The generic Wasm interpreter is connected to NEAR through three layers:

- `near-lean/vm`: `NearVM.run` executes a single contract function call with
  metering and NEAR host functions.
- `near-lean/runtime`: `NearRuntime.apply` validates transactions, executes and
  routes receipts, and updates account state.
- `near-lean/chain`: block application and settlement orchestrate queued work
  and report completion explicitly.

Receipts, promises and callbacks, contract storage, account state, access keys,
and gas accounting are modeled across these layers. Full protocol coverage and
an equivalence proof against nearcore remain open. Independent conformance
harnesses compare supported VM and runtime behavior with pinned nearcore
reference adapters.

Consensus and cryptographic verification remain outside these execution layers.
Execution relies on supplied block context and validation assumptions; proofs
must state which inputs are trusted. Block orchestration does not establish
consensus correctness.

## Future validation

We aim to model runtime upgrades and replay NEAR history with bit-for-bit
agreement. Broader real-chain snapshot tests, a nearcore integration or parallel
replay implementation, and fuzzing can increase confidence in the model. These
are goals, not guarantees supplied by current conformance tests.

An earlier implementation effort is recorded in the project history.

## Open questions

Specify callback execution and delivery guarantees under failed dependencies,
resource limits, and scheduling assumptions, and connect those guarantees to
contract lifetime properties.
