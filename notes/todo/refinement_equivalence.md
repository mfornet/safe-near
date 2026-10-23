# Restructure refinement as exact equivalence

Follow-up task. Goal: replace the per-contract refinement statements
(`contracts/w-near/verification/Spec/Refinement.lean`,
`contracts/linkdrop/verification/Spec/Refinement.lean`) by one generic
definition, and strengthen it from "the binary refines the model when gas and
funds suffice" to "the binary and the model have exactly the same observable
behaviour", gas and resources included.

This document fixes the design. The agent implements it; it does not re-open
the decisions marked **Decided** without discussing first. Items marked
**Open** are for the agent to settle and document.

## 1. Why the current statements are not equivalence

`Refines` today (wNEAR, line 350 of `Spec/Refinement.lean`) is a one-directional
simulation:

- Gas is not in the model. The clause `R.outOfGas r = false → ...` drops every
  execution the binary aborts for gas. Burnt and used gas are only bounded.
- Funds are not in the model. `ExecutionResources.Supports` is a hypothesis
  that excludes executions where the model schedules a transfer the account
  cannot pay or grows storage the account cannot cover.
- The `RuntimeInterface` is not runtime-generic: `mkInput`, `promises`,
  `encodeRet` and `callbackResult` mention wNEAR types.
- Receipts are compared after a lossy projection (`promisesOf?`), guarded by
  `observationsValid`.
- linkdrop has a divergent copy (empty logs required, no panic-text match,
  receipts instead of promise chains).

The new statement must have none of these escape hatches. Whatever the binary
does on a given input, the model does the same, and vice versa.

## 2. Shape of the new definition

Three parameters, as agreed:

```
Refines (R : RuntimeInterface) (code : R.Code) (M : ContractModel) : Prop
```

### 2.1 `RuntimeInterface` (generic, no contract types) — **Decided**

Lives in a new lightweight Lean library that does not depend on the Wasm
interpreter, so that `Spec/` libraries can import it without building
`NearVM`. Suggested location: `near-lean/interface` (lake package name for the
agent to pick; it must contain only types and no interpreter code). The raw
types it needs (`Bytes`, raw storage as a finite map of byte strings, raw
receipt specs, a raw promise-result type, return data) are moved or duplicated
there; `near-lean/vm` then imports it, or proves its own types coincide.

Fields, all over raw types:

- `Storage`, `Code`, `Result`.
- `exec : Code → Storage → Context → Result`, where `Context` is the
  contract-independent host input: method name, argument bytes, current and
  predecessor account ids, attached deposit, prepaid gas, raw promise results,
  account balance, locked balance, account storage usage, protocol config.
- Observations on `Result`: `storage`, `balance`, `storageUsage`, `burntGas`,
  `usedGas`, `returnData` (bytes or receipt index), `logs`, `receipts` (raw
  receipt specs with dependencies), `failure : Option Failure`.
- `Failure` is a small inductive owned by the interface: `panic (msg)`,
  `outOfGas`, `balanceExceeded`, `lackBalanceForState (deficit)`, `other
  (msg)`, plus `executionIssue (msg)` for interpreter limitations.

The instance for near-lean wraps `NearVM.run` (see 2.4 for the boundary).

### 2.2 `ContractModel` (per contract) — **Decided**

A structure with a typed state, as agreed. Required fields:

- Types: `State`, `Call`, `Outcome`, `Panic`. `Env` is **not** contract-specific
  any more: the model consumes the interface's `Context` directly (raw promise
  results included; the contract parses them itself, so wNEAR's
  `parseU128Result` moves from the adapter into the model).
- `step : Config → Option State → Context → Call → Except Failure Outcome`
  where the failure type is the interface's `Failure` with `panic` carrying the
  contract's `Panic` (so `Panic.message` is part of the model). `Outcome`
  carries, in addition to today's state, promises, return and logs, the gas
  use `{burnt, used}`. A `Failure` result also carries burnt gas and logs,
  since the binary retains both on failure.
- Encoders to raw: `encodeState : State → RawStorage` with its inverse
  `project`, `encodeArgs : Call → Bytes`, `encodeRet : Ret → ReturnData`,
  `encodeReceipts : List Promise → List RawReceiptSpec`,
  `methodName : Call → String`.
- `Call.WF : Call → Prop`, the decodable-argument condition. Argument-decoding
  failures stay outside the model for now (see Open items).
- `Inv : Config → State → Prop`, the reachable-state invariant, and
  `Represents : RawStorage → Option State → Prop` defined from `encodeState`
  and `Inv` as today.

Comparison happens in the raw space: the model encodes, the binary's raw
observations must equal the encoding. No projection of receipts back into the
model, no `observationsValid`.

### 2.3 `Refines` as equality of observations — **Decided**

```
∀ raw st ctx call,
  M.Call.WF call → ctx.method = M.methodName call → ctx.args = M.encodeArgs call →
  M.Represents raw st →
  observe (R.exec code raw ctx) = M.observe (M.step cfg st ctx call)
```

where both sides produce the same record
`{failure, storage, balance, storageUsage, burntGas, usedGas, returnData, logs, receipts}`.
On model failure the record is: the failure, the input storage, input balance
and usage, the burnt gas the model predicts, used = burnt, no return data, the
retained logs, no receipts. There is no `outOfGas → ...` guard and no
`Supports` hypothesis. The remaining hypotheses are representation only.

Because this is an equality, the generic transfer lemma is immediate and should
be proved once in the interface library: every property of `M.step` is a
property of the observed execution of `code`. Also prove the converse
direction's useful corollaries (e.g. the binary never produces an execution
issue when `Refines` holds).

### 2.4 Which boundary — **Decided: the function-call action boundary**

The storage-rent check (`LackBalanceForState`) is not performed by the VM. It
runs in the receipt executor after the call
(`near-lean/runtime/NearRuntime/Apply.lean`, `checkStorageStake`, formula
`usage * storageAmountPerByte - amount - locked`, with the 770-byte
zero-balance exemption). Outgoing deposits, by contrast, are checked inside the
VM at promise creation (`HostError.balanceExceeded`).

To make "insufficient funds to grow storage" a model failure, the near-lean
instance of `exec` is the VM run **followed by** the storage-stake check,
packaged in near-lean as one function (e.g. `applyFunctionCall`) that the
runtime's action executor also uses, so the boundary is a real seam and not a
test-only wrapper. On a rent failure the observations are those of a failed
call: storage, balance and usage rolled back, receipts dropped, gas as burnt by
the VM.

Consequence for the model: `step` ends with the same rent check on the
post-state's measured usage, and `Context` must carry `locked` and the
account's total storage usage (including account and code overhead, which the
contract's key/value storage does not see). The model tracks usage as
`ctx.storageUsage - usage(raw) + usage(encodeState newState)` exactly as the
VM does, including the `u64` bound.

## 3. Gas in the model — **Decided approach, details Open**

Exact equivalence requires the model to predict `burntGas` and `usedGas`
exactly, on success and on failure. The VM's gas is the sum of:

1. Host-side fees: per host call, per byte of storage read/written/removed, per
   log byte, per promise and per action, contract loading by code size. These
   are protocol parameters (`RuntimeConfig.fees`, `wasm.extCosts`) applied to
   quantities the typed model already knows (key and value lengths, number of
   promises, log lengths, argument sizes).
2. Wasm instruction gas: `regularOpCost` times the number of instructions
   executed on the path the binary takes, which depends on the compiled code
   and on input sizes (string lengths, JSON parsing loops, Borsh encoding).

Approach:

- Add `Model/Gas.lean` per contract defining `gasOf : Config → Option State →
  Context → Call → GasUse` as an explicit cost expression. Part (1) is written
  directly from the typed trace of each method. Part (2) is a per-method,
  per-branch function of the input sizes, with named coefficients
  (`opsNearDeposit_base`, `opsPerArgByte`, ...). The coefficients are
  constants of the deployed binary; their values are obtained by measurement
  (`measureCallGasBurnt`, the gas profile in `VMOutcome.gasProfile`) and then
  **proved** equal to the binary's instruction counts as part of the refinement
  proof. Until proved, they are definitions, not axioms, and the audit must
  show them as such.
- `step` consumes gas in source order: each `require` and each host operation
  charges before it runs, so that on `outOfGas` the model's burnt gas and
  retained logs are the ones at the point of exhaustion. This is what makes
  failure observations exact. The agent must check in `NearVM/HostGas.lean`
  and `Run.lean` how burnt gas is finalised on `gasExceeded` and mirror it.
- `usedGas` on success = burnt + gas attached to created promises, as the VM
  computes it.

Open for the agent: whether the Wasm instruction counts are expressed per
method as a flat formula or via a small cost-annotated trace type shared by all
contracts. Pick the one that keeps `Proofs/` readable; document the choice.

What this does **not** do: it does not replace the gas model by a VM run inside
the model. The model stays a readable typed function; gas is an explicit
function alongside it whose correctness is a proof obligation of `Refines`.

## 4. Resources in the model — **Decided**

`Context` carries `balance`, `locked`, `storageUsage`, all from the enclosing
runtime state. The model:

- Deducts each promise's deposit from the liquid balance at creation, in order,
  and fails with `balanceExceeded` when it cannot, at that point (gas burnt so
  far is retained).
- Checks `balance + deposit < 2^128` and the `u64` storage bound as the VM
  does.
- Applies the storage-stake check after computing the post-state (section 2.4).

Existing specs that assumed unlimited resources (`WithdrawAvailable`,
`DepositAvailable`) gain explicit gas and balance hypotheses. Keep them proved.

## 5. Work plan

1. Create the interface library with raw types, `RuntimeInterface`,
   `ContractModel`, `Refines`, and the transfer lemmas. No dependency on the
   interpreter.
2. In near-lean: add the function-call-action boundary function and
   instantiate `RuntimeInterface` with it in a library that imports `NearVM`.
   Prove the instance's observations are total (no `getD []` fallbacks).
3. wNEAR: extend `Model/` (context, gas, resource checks, failure type,
   promise-result parsing), add `Model/Gas.lean`, provide the `ContractModel`
   instance, delete `Spec/Refinement.lean` and most of
   `Spec/RuntimeInstance.lean` in favour of the instance. Re-prove every
   existing spec against the extended `step`. `just wnear-audit` must pass.
4. linkdrop: retarget `Spec/Refinement.lean` to the shared definition.
5. Tests: the adapter regressions (`just runtime-adapter-test`) become equality
   checks of the full observation record, including gas, against the model on
   every fixture. Add fixtures for out-of-gas at several points, balance
   exceeded, and lack-balance-for-state.
6. Update `contracts/w-near/verification/README.md`, the blueprint, and
   `notes/design/SPECIFICATIONS.md`.

Non-goal: proving `Refines` for `contract.wasm`. The task delivers the
statement, the instance, the model extensions, re-proved specs and tests.

## 6. Open items the agent must settle and write down

- Fuel: `NearVM.run` takes a fuel argument and can return an interpreter
  error. Decide whether `Refines` fixes default fuel and asserts no execution
  issue, or quantifies over all sufficient fuel.
- Argument decoding: malformed JSON arguments are still outside the model
  (`Call.WF` plus typed `Call`). Document this as the remaining gap, or add a
  `malformed` call case whose model behaviour is the SDK's deserialisation
  panic.
- Exact burnt gas on failure: required by this document; confirm it is
  determinable from the VM's accounting without replaying the interpreter.
- Where the shared raw types live, and whether `near-lean/vm` imports them or
  proves coincidence.
