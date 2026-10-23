# Restructure refinement as a generic, complete statement

Follow-up task, blocked on the current large rewrite. Goal: replace the
per-contract refinement statements
(`contracts/w-near/verification/Spec/Refinement.lean`,
`contracts/linkdrop/verification/Spec/Refinement.lean`) by one generic
definition that characterises every execution of the binary: no input, gas
amount or resource state is excluded by a hypothesis.

This document fixes the design. The agent implements it; it does not re-open
the decisions marked **Decided** without discussing first. Items marked
**Open** are for the agent to settle and document.

## 1. Why the current statements are not enough

`Refines` today (wNEAR, `Spec/Refinement.lean`) is a one-directional
simulation with escape hatches:

- Gas: the clause `R.outOfGas r = false → ...` drops every execution the
  binary aborts for gas, and nothing says how much gas is enough.
- Funds: `ExecutionResources.Supports` is a hypothesis that excludes executions
  where the model schedules a transfer the account cannot pay or grows storage
  the account cannot cover.
- Input: `call.WF` and a typed `Call` exclude malformed arguments; nothing is
  said about them.
- The `RuntimeInterface` is not runtime-generic: `mkInput`, `promises`,
  `encodeRet` and `callbackResult` mention wNEAR types.
- Receipts are compared after a lossy projection (`promisesOf?`), guarded by
  `observationsValid`; panics are matched by substring (`Panic.matches`).
- linkdrop has a divergent copy (empty logs required, no panic-text match,
  receipts instead of promise chains).

## 2. Principles — **Decided**

- **The low-level model is exact; statements may be bounds.** near-lean's VM
  and runtime stay an exact model of nearcore, including gas. The contract
  model does not track gas; refinement states a gas **upper bound** per call.
  Statements have the form "if the attached gas is at least `B`, then ...",
  never "there exists some gas such that ...".
- **Worst case over the environment.** Gas for storage access depends on the
  whole chunk's trie and its node cache (`prepareStorageCallAux` in
  `near-lean/vm/NearVM/Metered.lean` charges `touching_trie_node` /
  `read_cached_trie_node` from trie-overlay counters). The contract model never
  models the trie. `Refines` quantifies over every context, trie included, so
  the gas bound must hold in the worst case (every node cold, longest path the
  key allows).
- **Typed calls.** Statements are written against a typed `Call`. Inputs that
  are not a serialisation of any call are covered by the refinement, not by the
  model: they fail with no effects.
- **Everything else exact.** Storage, balance, storage usage, return data,
  logs, receipts and failure kind (panic message, balance exceeded, lack of
  balance for state) are compared exactly, in the raw space.

## 3. Interface library — **Decided**

New package `near-lean/interface` (`NearInterface`). Definitions only: no
interpreter, no Wasm, so `Spec/` libraries can import it without building
`NearVM`.

Contents (moved, not duplicated):

- Raw types: `Bytes := List UInt8` (the VM's representation, so no
  conversion), `RawStorage`, `ReturnData`, `ReceiptSpec` / `RawReceipt` with
  dependencies, `PromiseResult`, `TrieOverlay` (needed by `Context`).
- `Context`, `Failure`, `Observation`, `RuntimeInterface`, `ContractModel`,
  `Refines` and the generic lemmas (section 7).

`NearVM` imports these and keeps `abbrev`s under `Wasm.Near` so existing code
compiles unchanged. There is a single copy of each type, so no coincidence
proofs are needed.

### 3.1 `Context`

The contract-independent input of one function-call action: what varies
between real calls.

```lean
structure Context where
  method         : String
  args           : Bytes
  current        : AccountId
  predecessor    : AccountId
  signer         : AccountId
  signerPk       : Bytes
  attached       : Balance
  prepaidGas     : Gas
  promiseResults : List PromiseResult
  balance        : Balance   -- account.amount, before the deposit (see 3.2)
  locked         : Balance
  storageUsage   : Nat       -- whole account, incl. account and code overhead
  blockHeight    : Nat
  timestamp      : Nat
  epochHeight    : Nat
  randomSeed     : Bytes
  trie           : TrieOverlay.State   -- full chunk trie and node cache
  protocol       : RuntimeConfig       -- fees, ext costs, limits, storage price
```

`Context` is not `VMContext`. `VMContext`'s policy fields
(`validateActionMethodUtf8`, `chargeStorageValueAccess`,
`storageReadsFromTrie`, `viewConfig`) are fixed by the near-lean instance to
the values `functionCallContext` in `near-lean/runtime/NearRuntime/Apply.lean`
uses; the instance builds the `VMContext` from `Context`.

### 3.2 Balance convention — **Decided: exactly as NEAR**

The runtime passes `account.amount` from before the deposit
(`functionCallContext`, `accountBalance := account.amount`) and the deposit
separately; the VM credits it when building its state
(`toNearState`: `accountBalance := ctx.accountBalance + ctx.attachedDeposit`).
`Context.balance` is that pre-deposit amount. Anything the model says about
balance follows the same steps, including the `u128` bound. `locked` and
`storageUsage` are the account's raw fields.

### 3.3 `Failure` and `Observation`

```lean
inductive Failure
  | panic (msg : String)          -- exact text as the runtime reports it
  | outOfGas
  | balanceExceeded
  | lackBalanceForState (deficit : Balance)
  | methodNotFound
  | other (msg : String)
  | executionIssue (msg : String) -- interpreter limitation

structure Observation where
  outcome      : Except Failure ReturnData
  storage      : RawStorage
  balance      : Balance
  storageUsage : Nat
  burntGas     : Gas
  usedGas      : Gas
  logs         : List String
  receipts     : List RawReceipt
  trie         : TrieOverlay.State  -- cache warming survives every failure
```

### 3.4 `RuntimeInterface`

```lean
structure RuntimeInterface where
  Code : Type
  exec : Code → RawStorage → Context → Observation
```

All projection from `VMOutcome` happens inside the instance, so the interface
has no `observationsValid` and no `getD []` fallbacks.

## 4. The function-call action boundary — **Decided**

The storage-rent check (`LackBalanceForState`) is not performed by the VM. It
runs in the receipt executor after the call (`checkStorageStake` in
`near-lean/runtime/NearRuntime/Apply.lean`, formula
`usage * storageAmountPerByte - amount - locked`, with the 770-byte
zero-balance exemption). Outgoing deposits, by contrast, are checked inside the
VM at promise creation (`HostError.balanceExceeded`).

The near-lean `exec` is the VM run **followed by** the storage-stake check,
packaged as one function next to `applyFunctionCall` in `near-lean/runtime`.
`applyFunctionCall` is refactored to call it, so the boundary is a real seam
and not a test-only wrapper. On a rent failure the observation is that of a
failed call: storage, balance and usage rolled back, receipts dropped, gas as
burnt by the VM.

**Fuel.** Every Wasm instruction costs at least `regularOpCost > 0`, so
`prepaidGas / regularOpCost + c` fuel always suffices. The instance fixes that
amount and proves it sufficient, so `executionIssue` only means "construct
unsupported by the interpreter", and `Refines` rules it out.

## 5. `ContractModel` (per contract) — **Decided**

```lean
inductive ModelFailure (P : Type)
  | panic (p : P)
  | balanceExceeded
  | lackBalanceForState (deficit : Balance)

structure ContractModel where
  State Call Ret Panic Promise : Type
  -- representation
  encodeState    : State → RawStorage
  Inv            : State → Prop
  -- input
  Parses         : (method : String) → (args : Bytes) → Call → Prop
  -- output
  encodeRet      : Ret → ReturnData
  encodeReceipts : (leftoverGas : Gas) → List Promise → List RawReceipt
  panicMessage   : Panic → String
  -- semantics
  step : Context → Option State → Call → Except (ModelFailure Panic) (Outcome State Ret Promise)
  gas  : Context → Option State → Call → Gas
```

- `Outcome` carries the new state, return value, logs and promises.
- `step` consumes the interface's `Context` directly, raw promise results
  included; the contract parses them itself (wNEAR's `parseU128Result` moves
  from the adapter into the model).
- `step` is exact for failures that do not depend on gas: panics, promise
  deposits the liquid balance cannot pay (`balanceExceeded`, at the promise
  that fails), and the rent check on the post-state (`lackBalanceForState`).
  The model tracks storage usage as
  `ctx.storageUsage - usage(raw) + usage(encodeState newState)`, exactly as the
  VM does, including the `u64` bound.
- `gas` is a bound on `usedGas` (burnt gas plus static gas attached to
  promises), written as a readable formula with named constants. Its soundness
  is a proof obligation of `Refines`, for every `ctx.trie`.
- `encodeReceipts` takes the leftover gas because a promise with
  `with_unused_gas_weight` receives its static gas plus a share of
  `prepaid - used`. The leftover is read from the binary's own observation, so
  this is not an existential.
- `panicMessage` gives the exact runtime text (SDK prefix, any location
  suffix), replacing the substring match.
- `Represents raw none := raw = ∅`, and
  `Represents raw (some s) := Inv s ∧ raw = encodeState s`.

### 5.1 `Parses`

`Parses` is a relation, not `encodeArgs`: near-sdk/serde accepts many byte
strings for the same call (whitespace, field order, ignored unknown fields), so
"not equal to `encodeArgs c`" does not imply failure. For JSON contracts it is
stated at the JSON-value level, e.g. "`args` parses to a JSON object whose
fields `amount`, `receiver_id`, ... decode to `c`". The two clauses of
`Refines` pin it down from both sides: too narrow makes the invalid-input
clause false, too wide makes the valid-call clause false. Error messages and
parse gas are not modelled.

Each model proves `Parses` functional (at most one call per input) as a lemma.

## 6. `Refines` — **Decided**

```lean
/-- Agreement on everything except gas and trie: outcome, storage, balance,
usage, logs, receipts (encoded with `prepaid - r.usedGas` as leftover). On a
model failure: the failure, input storage/balance/usage, the model's logs, no
receipts. -/
def Matches (M) (ctx raw) (r : Observation) (res : Except _ _) : Prop

/-- A failed call with no effects. -/
def RolledBack (ctx raw) (r : Observation) : Prop :=
  r.outcome.isError ∧ r.storage = raw ∧ r.balance = ctx.balance ∧
  r.storageUsage = ctx.storageUsage ∧ r.receipts = []

def Refines (R : RuntimeInterface) (code : R.Code) (M : ContractModel) : Prop :=
  ∀ raw st ctx, M.Represents raw st →
    let r := R.exec code raw ctx
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    -- valid calls
    (∀ c, M.Parses ctx.method ctx.args c →
      let res := M.step ctx st c
      (M.gas ctx st c ≤ ctx.prepaidGas →
        Matches M ctx raw r res ∧ r.usedGas ≤ M.gas ctx st c) ∧
      (Matches M ctx raw r res ∨
        (r.outcome = .error .outOfGas ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs))) ∧
    -- everything that is not a call fails with no effects
    ((¬ ∃ c, M.Parses ctx.method ctx.args c) → RolledBack ctx raw r)
```

- The only hypothesis is representation. No `WF`, no `Supports`, no
  `outOfGas` guard.
- With enough gas, the execution is the model's and the bound holds. Below the
  bound, it is still fully characterised: the model's behaviour or an
  out-of-gas failure with rollback. Specs use the first clause ("with at least
  150 Tgas attached, ...").
- `r.logs <+: res.logs` (logs on out-of-gas are a prefix of the model's) is
  optional; drop it if it gets in the way.

## 7. Generic lemmas (in the interface library)

- `Refines.transfer`: a property of `M.step` under `M.gas ≤ prepaidGas` is a
  property of the observed execution of `code`.
- `Refines.invalid_input`: unparsable input never changes storage, balance or
  receipts.
- `Refines.no_execution_issue`.
- `Refines.failure_rollback`: every failed execution rolls back storage,
  balance, usage and receipts.

## 8. Work plan

1. Create `near-lean/interface`: move the raw types and `TrieOverlay`, define
   `Context`, `Failure`, `Observation`, `RuntimeInterface`, `ContractModel`,
   `Refines` and the generic lemmas. `NearVM` re-exports via `abbrev`.
2. In near-lean/runtime: add the function-call boundary function (VM run then
   storage-stake check), make `applyFunctionCall` use it, instantiate
   `RuntimeInterface`, prove fuel sufficiency and total observations.
3. wNEAR: extend `Model/` (context, balance and rent failures, promise-result
   parsing, `Parses`, `gas`, `encodeReceipts` with leftover gas), provide the
   `ContractModel` instance, delete `Spec/Refinement.lean` and most of
   `Spec/RuntimeInstance.lean`. Re-prove existing specs; specs that assumed
   unlimited resources (`WithdrawAvailable`, `DepositAvailable`) gain explicit
   gas and balance hypotheses. `just wnear-audit` must pass.
4. linkdrop: retarget to the shared definition.
5. Tests: the adapter regressions (`just runtime-adapter-test`) check
   `Matches` and the gas bound on every fixture. Add fixtures for out-of-gas
   below the bound, balance exceeded, lack of balance for state, malformed and
   non-canonical JSON arguments, unknown methods, and worst-case trie states
   for the gas bound.
6. Update `contracts/w-near/verification/README.md`, the blueprint, and
   `notes/design/SPECIFICATIONS.md`.

Non-goal: proving `Refines` for `contract.wasm`. The task delivers the
statement, the instance, the model extensions, re-proved specs and tests.

## 9. Open items the agent must settle and write down

- The worst-case storage-access cost formula: the maximum trie path length for
  a contract key of length `n` under `contractKey`, and whether `Refines`
  needs a bound on `ctx.trie` (e.g. well-formedness) to make it finite.
- How `Parses` is specified for JSON (a shared JSON-value parser in the
  interface library, plus per-contract field decoding), and how its agreement
  with serde's acceptance is tested.
- Whether `Matches` needs anything beyond `RolledBack` for the logs on
  `balanceExceeded` / `lackBalanceForState` (logs up to the failing point).

## 10. Progress and decisions taken while implementing

### Step 1 — done

`near-lean/interface` (`NearInterface`) holds the raw types, config, errors,
trie overlay, `Context` (plus `outputDataReceivers`, which the VM needs),
`Context.WF`, `Failure`, `Observation`, `RuntimeInterface`, `ContractModel`,
`Refines` and the four generic lemmas. Departures from sections 3–6:

- `Refines` has a second hypothesis, `ctx.WF raw`: the guarantees the
  runtime gives every context it builds (integer widths, usage counting the
  records, the trie holding `raw`). It does not depend on the call or the
  contract, so it does not reintroduce `Supports`-style exclusions.
- The gas clause compares against `ctx.gasLimit = min prepaidGas
  maxGasBurnt`, not `prepaidGas`: above the burn limit, more prepaid gas does
  not help.
- `step` returns `Failed` with logs, so the third open item (logs up to the
  failing point) is answered by `Matches` comparing `f.logs` exactly.

### Step 2 — in progress (`near-lean/runtime/NearRuntime/Boundary.lean`)

- **Seam by theorem, not by refactoring `applyFunctionCall`.** About a dozen
  runtime invariants (`GasInvariants`, `FunctionCallInvariants`,
  `PromiseGasInvariants`, ...) pattern-match the body of `applyFunctionCall`.
  Instead of routing it through a new function, the boundary uses the same
  `run` call and fuel, and the seam is stated as
  `functionCallContext_eq_toVMContext` (the receipt executor's VM context is
  `toVMContext` of the matching boundary context). `storageStakeDeficit` in
  `Apply.lean` is now defined as `NearInterface.stakeDeficit`, so there is
  one formula.
- Still to prove: for a receipt whose only action is a function call,
  `runReceiptActions` agrees with `execOn` on everything `Observation` holds
  (the receipt's action fees aside).
- **Storage listing.** The VM reads storage from a list; `RawStorage` is a
  `Finset`, so `nearRuntime` uses `raw.toList` (noncomputable). Obligation:
  `execOn` depends on the listing only through its `toFinset` (keys are
  unique, so lookups agree; `storageKeys` order must not leak into gas or
  outputs). The adapter tests use the computable `execOn`.
- **Fuel.** The naive bound `prepaidGas / regularOpCost + c` is false for
  this interpreter: `block` entry and falling off the end of a block or frame
  cost no gas (`nextInstructionGas`). Between two charged steps, the free
  steps are bounded by the nesting depth of labels times the call depth
  (≤ `execLimits.maxCallDepth`), so a sound fuel is
  `(gasLimit / regularOpCost + 1) * (2 * codeSize + 2) * (maxCallDepth + 1)`,
  given `regularOpCost > 0` in the config. Not proved yet. The instance keeps
  `defaultFuel`, like `applyFunctionCall`, until it is.
- Error mapping (`failureOf`): `guestPanic` → `panic`, `gasExceeded` /
  `gasLimitExceeded` → `outOfGas`, `balanceExceeded`, `methodNotFound`;
  anything with `FunctionCallError.issue?`, plus action-conversion failures,
  → `executionIssue`; everything else → `other`, using nearcore's message.
