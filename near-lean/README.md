# near-lean

NEAR in Lean, bottom up. Each directory is its own Lake package; they share
one toolchain (`lean-toolchain`) and one `packagesDir` (`.lake/packages`).

| Package | Seam in nearcore | What it is |
|---|---|---|
| `wasm/` | wasmer / wasmtime | The Wasm interpreter (Talos), WAT decoder, official test suite |
| `vm/` | `near_vm_runner::run` | One function call: host functions, gas, `VMContext` → `VMOutcome` |
| `runtime/` | `Runtime::apply` | Accounts, access keys, receipts, actions, fees, refunds |
| `chain/` | the "trustless manipulator" | Blocks, reachable states, explicit run completion, measured burnt gas |
| `iris-wasm/` | | Separation logic over the interpreter (Talos codelib), for proofs about Wasm code |
| `programs/` | | Small Rust programs used as interpreter tests |

```
just near-build     # from the repository root: build wasm, vm, runtime, chain
just near-test      # run the three scenario suites on the real wNEAR binary
just near-configs   # regenerate vm/configs from nearcore (needs cargo)
```

## vm

`NearVM.run cfg code codeSize method ctx storage : VMOutcome` executes one
export of a decoded module under a `VMContext` (`NearVM/Context.lean`,
nearcore's struct field for field) and returns a `VMOutcome`
(`NearVM/Outcome.lean`): balance, storage usage, return data, burnt and used
gas, logs, the receipts the call created, and `aborted : Option
FunctionCallError` with nearcore's error taxonomy (`NearVM/Error.lean`).

- `NearVM/Host.lean` and `NearVM/State.lean` are the NEAR host functions
  over the interpreter's store (copied from `iris-wasm/CodeLib/Near`, which
  will be repointed here).
- `NearVM/Metered.lean` wraps every host function with the gas it costs in
  nearcore's `logic.rs`: charges computed from the arguments before the call
  and from its effect after it, action fees and prepaid gas for promises,
  storage-usage accounting, attached deposits leaving the balance, and
  structured `guestPanic` errors carrying the panic message.
- `NearVM/Run.lean` steps the interpreter charging `regular_op_cost` per
  instruction and stops at gas exhaustion.
- `NearVM/Config.lean` loads `RuntimeConfig` from `configs/`: nearcore's own
  parameter tables (`RuntimeConfigView` JSON, one file per protocol version
  at which something changed, produced by `tools/dump-runtime-config`).
  Nothing is hand-copied.

Known gaps against nearcore: trie-dependent costs (`touching_trie_node`,
`read_cached_trie_node`) are not charged. The independent fixtures check exact
instruction and host gas, but do not prove metering correct for all programs.
Contract code enters as WAT text
because there is no binary Wasm decoder in Lean yet; the cryptographic host
functions are rejected by the metered VM until concrete semantics are supplied.

`lake exe vm-tests` runs the real wNEAR binary (`tests/fixtures/w_near.wat`,
printed from `contracts/w-near/contract.wasm`) through `run`: initialisation,
deposits, withdrawals, transfer-call promises with their callback, panics
with the SDK's messages, out-of-gas, storage usage, view calls.

## runtime

`Near.apply cfg applyState codeOf state txs incoming : ApplyResult`
(`NearRuntime/Apply.lean`) is one chunk's worth of work: transactions are
verified and charged. Signer-is-receiver transaction receipts are local;
other transaction receipts become outgoing work for a later chunk. Local,
delayed and incoming receipts run in that order until the gas limit; every receipt yields an
`ExecutionOutcome` when it runs. Action receipts implement eight action kinds
(`applyAction`), roll back on failure, and refund unused gas to the signer
and deposits to the predecessor through system receipts. Function calls go
through `NearVM.run`; the receipts they create get fresh ids, data
dependencies become `input_data_ids` / `output_data_receivers`, and a receipt
whose data has not arrived is postponed until it has. `NearRuntime/Fees.lean`
is `config.rs`: send and execution fees per action, transaction cost.

Model limits such as interpreter fuel exhaustion, cryptographic operations,
yield/resume, validator queries, staking and unstaking are reported as execution issues.
An issue preserves the entire apply's input state and publishes no protocol
outcomes or refunds. Actor checks protect administrative actions; implicit
accounts use decoded Ed25519 public keys and block-derived initial key nonces.
See [runtime/VERIFICATION.md](runtime/VERIFICATION.md) for the reference pin,
trusted inputs, remaining discrepancies, and proof obligations.

`lake exe runtime-tests` deploys wNEAR on `wrap.near` and drives it with
transactions: wrap, unwrap, a transfer-call whose receiver has no contract
(callback refund), out-of-gas with deposit refund, invalid transactions,
implicit accounts, account deletion, gas-limit delaying. Every step checks
that NEAR is conserved: balances plus burnt tokens plus in-flight deposits
never change.

## chain

`NearChain/Step.lean`: a `Snapshot` is a chain state plus the receipts in
flight; `step` applies a block with ordered incoming selection and deferral;
`Reachable` closes it under those same block sequences;
`runIsolated` runs transactions and everything they cause with nothing else
interleaved; `Receipt.touches`, `Receipt.upgrades` and `Block.independentOf`
inspect direct interactions in pending, delayed and postponed queues. They do
not establish independence from indirect contract effects. `settle` and
`runIsolated` return a `RunResult` distinguishing quiescence, exhausted block
budget, invalid delivery schedules and execution issues. `runBlocks` executes
explicit custom blocks without automatically draining deferred work. Its
results are proved reachable; selection preserves the receipt multiset and
the order of deferred work. See [chain/README.md](chain/README.md) for the
`Except`-returning step API and scheduling examples.
Reported completion implies quiescence by proved
lemmas. `measureCallGasBurnt` measures successful settled executions with
maximum attached gas; it does not establish sufficient prepaid gas.
`lake exe chain-tests` exercises these boundaries on wNEAR.

## Axiom audit: no `sorry`, no `native_decide`

A finished proof may depend only on the three standard axioms `propext`,
`Classical.choice` and `Quot.sound`. `tools/axiom-audit.py` checks the
transitive axioms of every declaration in a package (private helpers and proof
fields included) and fails on anything else, in particular `sorryAx` and
`Lean.ofReduceBool` (what `native_decide` and `decide +native` rely on).

```
tools/axiom-audit.py near-lean/wasm --report audit/wasm.json
tools/axiom-audit.py near-lean/iris-wasm --report audit/iris-wasm.json
tools/axiom-audit.py near-lean/programs/lean --report audit/programs.json --allow-sorry
tools/axiom-audit.py near-lean/vm --report audit/vm.json
tools/axiom-audit.py near-lean/runtime --report audit/runtime.json
tools/axiom-audit.py near-lean/chain --report audit/chain.json
```

`wasm` and `iris-wasm` must be clean. `programs` holds specs whose proofs are
open by design, so there `--allow-sorry` tolerates `sorryAx` alone and prints
each sorried declaration; any other nonstandard axiom still fails. CI runs all
three on every change under `near-lean/`. Pass `--no-build` to audit already
built artefacts.

The public VM result also carries a checked receipt DAG: dependencies refer only
to earlier receipts, returned receipt indices exist, and dependency cycles are
impossible (`run_receipts_valid`, `run_dependency_before`,
`run_returnedReceipt_lt`, `run_no_receipt_cycle`). Raw promise handles are checked
before accepting an outcome, so malformed joins cannot silently disappear
during conversion. Rejection is an explicit model issue with rollback, not contract
success. Full host-invariant preservation, correspondence with nearcore beyond the
conformance fixtures, global identifier freshness and scheduler correctness
remain separate obligations.

`NearVM/PromiseGraph.lean` now implements total incremental conversion, replacing
the bounded recursive join walk. It stores each handle's exact ordered receipt
vector, preserves duplicate dependencies and rejects missing/future references
or yielded promises. Executable conversion is proved equivalent to an explicit
transition relation, succeeds exactly on supported well-formed raw graphs, and
preserves receipt validity from the empty graph. Returned receipt identity comes
from that same handle table. Successful `value_return` and `promise_return`
selections now overwrite each other; overwrite lemmas and independent regressions
cover both call orders.
