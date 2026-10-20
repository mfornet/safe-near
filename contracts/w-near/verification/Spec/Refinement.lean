import Spec.Invariants

/-!
# Refinement: what we need from `near-lean`

This file states the observations the wNEAR proofs need from the runtime
(`RuntimeInterface`) and the proposition linking a deployed module to the
model (`Refines`). `Spec.RuntimeInstance` supplies the executable VM instance;
the refinement proof remains an obligation.

The interface is deliberately minimal: a deterministic executor for a single
function-call action, plus observation functions on its result.
-/

namespace WNear

open Borsh

/-- Result of a function call as the runtime reports it: bytes, or the index
of a promise whose result becomes the call's result. -/
inductive ReturnData
  | value (bytes : Bytes)
  | promise
  deriving DecidableEq

/-- Resources supplied by the enclosing action/chain semantics, before adding
this call's attached deposit. Storage usage includes code and account overhead,
which are absent from the contract's key/value model. -/
structure ExecutionResources where
  balance : Nat
  storageUsage : Nat
  deriving DecidableEq, Repr

/-- Bounded host inputs and enough measured usage to cover stored records. -/
def ExecutionResources.Valid (r : ExecutionResources) (cfg : Config)
    (raw : RawStorage) (env : Env) : Prop :=
  r.balance + env.attachedDeposit < 2^128 ∧
  r.storageUsage < 2^64 ∧ WNear.storageUsage cfg raw ≤ r.storageUsage ∧
  env.prepaidGas < 2^64

/-- Local resource obligations for a model success. Chain-level solvency must
establish these; the mathematical model alone does not own NEAR funds.
The retained overhead is added to the new contract records without truncation. -/
def ExecutionResources.Supports (r : ExecutionResources) (cfg : Config)
    (raw : RawStorage) (env : Env) (result : Except Panic Outcome) : Prop :=
  match result with
  | .error _ => True
  | .ok o => o.nearOut ≤ r.balance + env.attachedDeposit ∧
      r.storageUsage - WNear.storageUsage cfg raw + WNear.storageUsage cfg (encode o.state) < 2^64

/-- The interface required from `near-lean`. -/
@[blueprint "def:runtime-interface"
  (statement := /-- What the proofs need from \texttt{near-lean}: types for storage, code, inputs and results; a deterministic executor of one function call; observation functions on results (failure message, gas exhaustion, resulting storage, return data, logs, promises); and the JSON encoding of return values. -/)]
structure RuntimeInterface where
  /-- Contract storage of one account, as the runtime keeps it. -/
  Storage : Type
  /-- Its key/value content. -/
  entries : Storage → RawStorage
  /-- Deployed code (`contract.wasm` decoded). -/
  Code : Type
  /-- One function-call action: method name, JSON arguments and host context. -/
  Input : Type
  /-- Exact raw callback inputs, including malformed successful return bytes. -/
  CallbackResults : Type
  /-- The contract-specific view of result zero; additional results are retained
  by the executor even though this contract does not inspect them. -/
  callbackResult : CallbackResults → Option PromiseResult
  /-- The input for a typed call under a host context, using near-sdk's JSON
  argument encoding (`U128` as decimal strings, account ids as strings). -/
  mkInput : ExecutionResources → CallbackResults → Env → Call → Input
  /-- Result of executing one function call. -/
  Result : Type
  /-- Deterministic execution of one function call against code and storage. -/
  exec : Code → Storage → Input → Result
  /-- Failure message when the execution failed (panic, host error, gas). -/
  failure : Result → Option String
  /-- A model limitation, distinct from a protocol failure. Refinement must
  prove this absent, rather than exclude such executions by a hypothesis. -/
  executionIssue : Result → Option String
  /-- No information was silently discarded by contract-specific observation
  functions (in particular the projection of the exact receipt graph). -/
  observationsValid : Result → Bool
  /-- Whether the failure is gas exhaustion, which the model does not predict. -/
  outOfGas : Result → Bool
  /-- Storage after the execution; unchanged when the execution failed. -/
  storage : Result → Storage
  /-- Liquid account balance at the VM boundary (before receipt-level rewards). -/
  balance : Result → Nat
  /-- Total measured account storage usage, including retained overhead. -/
  storageUsage : Result → Nat
  burntGas : Result → Nat
  usedGas : Result → Nat
  subsidizedAmount : Result → Nat
  /-- Return data of a successful execution. -/
  returnValue : Result → ReturnData
  /-- Logs emitted, in order. -/
  logs : Result → List String
  /-- Promises created, projected to the model's promise type. -/
  promises : Result → List Promise
  /-- JSON encoding of return values as near-sdk serialises them. -/
  encodeRet : Ret → ReturnData

/-- The contract's panic text appears in the runtime's failure message
(`assert!` adds a source location, the runtime adds `Smart contract panicked:`). -/
def Panic.matches (p : Panic) (msg : String) : Prop :=
  ∃ pre post, msg = pre ++ p.message ++ post

/-- The storage represents a model state, or is empty before `new`. -/
def Represents (R : RuntimeInterface) (cfg : Config) (raw : R.Storage) : Option State → Prop
  | none => R.entries raw = ∅
  | some s => Inv cfg s ∧ R.entries raw = encode s

/-- Every execution of the deployed code that does not run out of gas is
predicted exactly by `step` under bounded, funded resource inputs: same success
or panic, storage, return value, logs and promises, plus balance and storage usage
accounting. Failures, including out of gas, roll back account resources. -/
@[blueprint "spec:refinement"
  (statement := /-- For every well-formed call, exact callback projection and storage representing an optional invariant state, under valid, bounded and funded execution resources: execution reports no model issue or subsidy, obeys the gas bounds, and rolls back storage, balance, storage usage and promises on every failure. When execution is not out of gas, a successful model step agrees on storage, encoded return value, logs and promises, with exact balance and storage-usage accounting; a model panic yields a matching failure and unchanged storage with no promises. -/)]
def Refines (R : RuntimeInterface) (code : R.Code) (cfg : Config) : Prop :=
  ∀ (raw : R.Storage) (st : Option State) (resources : ExecutionResources) (env : Env) (call : Call) (results : R.CallbackResults),
    call.WF → env.promiseResult = R.callbackResult results →
    Represents R cfg raw st →
    resources.Valid cfg (R.entries raw) env →
    resources.Supports cfg (R.entries raw) env (step cfg st env call) →
    let r := R.exec code raw (R.mkInput resources results env call)
    R.executionIssue r = none ∧
    R.subsidizedAmount r = 0 ∧
    R.burntGas r ≤ R.usedGas r ∧ R.usedGas r ≤ env.prepaidGas ∧
    (R.failure r ≠ none →
      R.entries (R.storage r) = R.entries raw ∧ R.balance r = resources.balance ∧
      R.storageUsage r = resources.storageUsage ∧ R.promises r = []) ∧
    (R.outOfGas r = false →
    match step cfg st env call with
    | .ok o =>
        R.observationsValid r = true ∧
        R.failure r = none ∧ R.entries (R.storage r) = encode o.state ∧
        R.returnValue r = R.encodeRet o.ret ∧ R.logs r = o.logs ∧ R.promises r = o.promises ∧
        R.balance r + o.nearOut = resources.balance + env.attachedDeposit ∧
        R.storageUsage r = resources.storageUsage - WNear.storageUsage cfg (R.entries raw) +
          WNear.storageUsage cfg (encode o.state)
    | .error p =>
        (∃ msg, R.failure r = some msg ∧ p.matches msg) ∧
        R.entries (R.storage r) = R.entries raw ∧ R.promises r = [])

end WNear
