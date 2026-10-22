import Spec.Safety

/-! Open obligations at the typed execution boundary. This interface has no
instance: supplying a concrete Wasm runner, argument/return encodings, validated
key interpretation, and lossless receipt projection is required before this can
be called deployed-binary refinement. No proof assumes this proposition. -/
namespace Linkdrop.Spec

open Storage

structure Resources where
  balance : Nat
  storageUsage : Nat
  prepaidGas : Nat
  recordOverhead : Nat

def Resources.Valid (r : Resources) (raw : Raw) (e : Env) : Prop :=
  r.balance + e.deposit ≤ maxAmount ∧ r.storageUsage < 2 ^ 64 ∧
    usage r.recordOverhead raw ≤ r.storageUsage ∧ r.prepaidGas < 2 ^ 64

def nearOut (out : Outcome) : Nat :=
  (out.receipts.flatMap fun receipt => receipt.actions.filterMap fun action =>
    match action with | .transfer n => some n | _ => none).sum

/-- A successful abstract call needs enough real liquid NEAR and space for a
representable post-state, including retained account/code overhead. -/
def Resources.Supports (r : Resources) (raw : Raw) (data : Key → Bytes)
    (e : Env) (result : Except Panic Outcome) : Prop :=
  match result with
  | .error _ => True
  | .ok out => nearOut out ≤ r.balance + e.deposit ∧
    ∃ order, LayoutValid data out.state order ∧
      r.storageUsage - usage r.recordOverhead raw +
        usage r.recordOverhead (encode data out.state order) < 2 ^ 64

structure Execution where
  failure : Option String
  modelIssue : Option String
  outOfGas : Bool
  storage : Raw
  balance : Nat
  storageUsage : Nat
  burntGas : Nat
  usedGas : Nat
  -- None is an invalid/unsupported projection, never an empty substitute list.
  receipts : Option (List Receipt)
  result : Option Return
  logs : List String

structure RuntimeInterface where
  -- Code bytes must be the pinned contract.wasm, not a caller-chosen model.
  exec : Bytes → Raw → Resources → Env → Call → Execution

/-- Typed single-call refinement; storage and financial observations are explicit.
Execution failures, including gas exhaustion, roll back storage, balance, measured
usage, and receipts. Success preserves the exact returned local receipt index.
Gas/storage failures other than OOG require stronger resource support or an
extension to the model. This proposition is stated, not proved or instantiated. -/
def RefinesTypedExecution (runtime : RuntimeInterface) (code : Bytes)
    (data : Key → Bytes) : Prop :=
  ∀ raw s resources e c,
    Represents data raw s → e.deposit ≤ maxAmount → c.WF →
    resources.Valid raw e → resources.Supports raw data e (step s e c) →
    let actual := runtime.exec code raw resources e c
    actual.modelIssue = none ∧
    actual.burntGas ≤ actual.usedGas ∧ actual.usedGas ≤ resources.prepaidGas ∧
    (actual.failure ≠ none → actual.storage = raw ∧
      actual.balance = resources.balance ∧ actual.storageUsage = resources.storageUsage ∧
      actual.receipts = some []) ∧
    (actual.outOfGas = false →
      match step s e c with
      | .error _ => actual.failure ≠ none
      | .ok out => actual.failure = none ∧
        Represents data actual.storage out.state ∧
        actual.result = some out.result ∧ actual.receipts = some out.receipts ∧
        actual.logs = [] ∧ actual.balance + nearOut out = resources.balance + e.deposit ∧
        actual.storageUsage = resources.storageUsage - usage resources.recordOverhead raw +
          usage resources.recordOverhead actual.storage)

end Linkdrop.Spec
