import Spec.Invariants

/-!
# Refinement: what we need from `near-lean`

The NEAR runtime in Lean does not exist yet. This file states the interface
the wNEAR proofs need from it (`RuntimeInterface`) and the theorem that links
the deployed binary to the model (`Refines`). Once `near-lean/runtime` exists,
it must provide an instance of `RuntimeInterface` and `Refines` becomes a
theorem about `contracts/w-near/contract.wasm`.

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
  /-- The input for a typed call under a host context, using near-sdk's JSON
  argument encoding (`U128` as decimal strings, account ids as strings). -/
  mkInput : Env → Call → Input
  /-- Result of executing one function call. -/
  Result : Type
  /-- Deterministic execution of one function call against code and storage. -/
  exec : Code → Storage → Input → Result
  /-- Failure message when the execution failed (panic, host error, gas). -/
  failure : Result → Option String
  /-- Whether the failure is gas exhaustion, which the model does not predict. -/
  outOfGas : Result → Bool
  /-- Storage after the execution; unchanged when the execution failed. -/
  storage : Result → Storage
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
predicted exactly by `step`: same success or panic, same storage, return
value, logs and promises. -/
@[blueprint "spec:refinement"
  (statement := /-- For every storage representing an optional state (empty, or the encoding of a state satisfying \cref{def:inv}), every context and call, if executing the deployed code does not run out of gas then: when \cref{def:step} succeeds, the execution succeeds with the encoding of the new state as storage and the same return value, logs and promises; when \cref{def:step} panics, the execution fails with a message containing the panic text and the storage is unchanged. -/)]
def Refines (R : RuntimeInterface) (code : R.Code) (cfg : Config) : Prop :=
  ∀ (raw : R.Storage) (st : Option State) (env : Env) (call : Call),
    Represents R cfg raw st →
    let r := R.exec code raw (R.mkInput env call)
    R.outOfGas r = false →
    match step cfg st env call with
    | .ok o =>
        R.failure r = none ∧ R.entries (R.storage r) = encode o.state ∧
        R.returnValue r = R.encodeRet o.ret ∧ R.logs r = o.logs ∧ R.promises r = o.promises
    | .error p =>
        (∃ msg, R.failure r = some msg ∧ p.matches msg) ∧
        R.entries (R.storage r) = R.entries raw

end WNear
