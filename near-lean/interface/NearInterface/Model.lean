import NearInterface.Boundary
import NearInterface.Error

/-!
# Contract models

A `ContractModel` is a contract's high-level semantics together with the
encodings that place it in the raw space of `Boundary`: how its state is
stored, which inputs are its calls, how its return values, receipts and
panics look on chain. The model does not track gas; `gas` is an upper bound
whose soundness is part of `Refines`.
-/

namespace NearInterface

open Wasm.Near

/-- Failures a model predicts exactly. Gas exhaustion is not among them: it
depends on the binary and is covered by the gas bound. -/
inductive ModelFailure (Panic : Type)
  | panic (p : Panic)
  /-- A promise deposit the liquid balance cannot pay, at the promise that fails. -/
  | balanceExceeded
  /-- The receipt's storage-stake check fails on the post-state. -/
  | lackBalanceForState (deficit : Balance)
  /-- A log exceeds the protocol's limits on the number or total length of
  logs (`logLimitError`). -/
  | logLimit (error : HostError)

/-- A successful call. -/
structure Outcome (State Ret Promise : Type) where
  state : State
  ret : Ret
  logs : List String
  promises : List Promise

/-- A failed call keeps the logs emitted before the failing point. -/
structure Failed (Panic : Type) where
  failure : ModelFailure Panic
  logs : List String

abbrev StepResult (Panic State Ret Promise : Type) :=
  Except (Failed Panic) (Outcome State Ret Promise)

def StepResult.logs {Panic State Ret Promise : Type} :
    StepResult Panic State Ret Promise → List String
  | .ok o => o.logs
  | .error f => f.logs

/-- The host error the VM raises when a call emits `logs` in this order, and
the logs kept before it: `log_utf8` first checks the number of logs
(`check_can_add_a_log_message`), then that the total length in bytes stays
within `max_total_log_length`. A model's logs are the binary's only while they
fit these protocol limits. -/
def logLimitError (cfg : RuntimeConfig) (logs : List String) : Option (HostError × List String) :=
  go 0 [] logs
where
  go (total : Nat) (kept : List String) : List String → Option (HostError × List String)
    | [] => none
    | l :: ls =>
      let limits := cfg.wasm.limits
      if limits.maxNumberLogs ≤ kept.length then
        some (.numberOfLogsExceeded limits.maxNumberLogs, kept.reverse)
      else if limits.maxTotalLogLength < total + l.utf8ByteSize then
        some (.totalLogLengthExceeded (min (total + l.utf8ByteSize) (2 ^ 64 - 1))
          limits.maxTotalLogLength, kept.reverse)
      else go (total + l.utf8ByteSize) (l :: kept) ls

structure ContractModel where
  State : Type
  Call : Type
  Ret : Type
  Panic : Type
  Promise : Type
  /-- How a state is laid out in contract storage. -/
  encodeState : State → RawStorage
  Inv : State → Prop
  /-- `args` sent to `method` is a serialisation of the call. A relation, since
  a deserialiser accepts many byte strings for one call. -/
  Parses : (method : String) → (args : Bytes) → Call → Prop
  encodeRet : Ret → ReturnData
  /-- The receipts a call's promises become. `leftoverGas` is `prepaid - used`,
  shared among promises that ask for unused gas. -/
  encodeReceipts : (leftoverGas : Gas) → List Promise → List RawReceipt
  /-- The exact failure a panic site produces: usually `.panic msg` with the
  text the contract passes to `panic_utf8`; a host error the contract triggers
  deterministically (reading a missing promise result) is `.other msg`. -/
  panicFailure : Panic → Failure
  /-- One call, exact on every failure that does not depend on gas. -/
  step : Context → Option State → Call → StepResult Panic State Ret Promise
  /-- An upper bound on `usedGas`: burnt gas plus gas attached to promises. -/
  gas : Context → Option State → Call → Gas

namespace ContractModel

variable (M : ContractModel)

/-- Storage holds an invariant state, or nothing before initialisation. -/
def Represents (raw : RawStorage) : Option M.State → Prop
  | none => raw = ∅
  | some s => M.Inv s ∧ raw = M.encodeState s

/-- Each input is at most one call. Every model proves it. -/
def ParsesFunctional : Prop :=
  ∀ method args c c', M.Parses method args c → M.Parses method args c' → c = c'

def ModelFailure.toFailure : ModelFailure M.Panic → Failure
  | .panic p => M.panicFailure p
  | .balanceExceeded => .balanceExceeded
  | .lackBalanceForState deficit => .lackBalanceForState deficit
  | .logLimit error => .other error.message

end ContractModel

end NearInterface
