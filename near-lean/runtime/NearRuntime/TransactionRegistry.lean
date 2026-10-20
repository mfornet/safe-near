import NearRuntime.Apply
import NearRuntime.TransactionEncoding
import NearRuntime.QueueEncoding

/-! Register admitted transaction receipts from original typed transaction
bodies and the existing transaction-conversion transition. This is a preflight
observer of that transition; it does not replace apply, execute receipts, or
infer promise/data identities from native output. -/
namespace Near.TransactionRegistry

structure Input where
  transaction : Transaction
  blockHash : NativeIdentity.Hash
  deriving Inhabited

structure Attempt where
  index : Nat
  body : Bytes
  hash : NativeIdentity.Hash
  receipt : Option Receipt := none
  receiptHash : Option NativeIdentity.Hash := none
  error : Option RuntimeError := none

structure Result where
  state : ChainState
  context : QueueEncoding.Context
  attempts : List Attempt := []

private def extend (context : QueueEncoding.Context) (id : ReceiptId) (hash : NativeIdentity.Hash) :
    Except String QueueEncoding.Context := do
  if context.receipts.any (·.1 == id) || context.formats.any (·.1 == id) then
    throw "transaction receipt logical identity is already registered"
  let receipts := context.receipts ++ [(id, hash)]
  NativeIdentity.validate receipts
  return { context with receipts, formats := context.formats ++ [(id, .legacy)] }

/-- Registering a transaction cannot rewrite established data ownership or
persisted delayed-queue metadata. -/
theorem extend_keeps_queue_context (context next : QueueEncoding.Context) (id : ReceiptId)
    (hash : NativeIdentity.Hash) (h : extend context id hash = .ok next) :
    next.data = context.data ∧ next.delayed = context.delayed := by
  unfold extend at h
  split at h
  · simp [throw, bind, Except.bind] at h
  · cases hv : NativeIdentity.validate (context.receipts ++ [(id, hash)]) with
    | error error => simp [hv, bind, Except.bind] at h
    | ok accepted =>
      cases accepted
      simp [hv, bind, pure, Except.bind, Except.pure] at h
      cases h
      exact ⟨rfl, rfl⟩

/-- Successful conversion is performed by the actual core function. Rejected
transactions leave the threaded state and identity context unchanged, so later
nonces are checked against exactly the admitted prefix. Protocol errors remain
attempts; model limitations or unencodable original bodies abort observation. -/
def observe (cfg : Wasm.Near.RuntimeConfig) (ap : ApplyState) (codes : List (String × Bytes))
    (initial : ChainState) (inputs : List Input) (context : QueueEncoding.Context := {}) : Except String Result := do
  let _ ← QueueEncoding.encode initial codes context (some cfg)
  let mut result : Result := { state := initial, context }
  for (input, index) in inputs.zipIdx do
    let body ← TransactionEncoding.encode codes input.blockHash input.transaction
    let hash := Sha256.hash body
    match convertTransaction cfg ap result.state input.transaction with
    | .error error =>
      if let some issue := error.issue? then throw issue.message
      result := { result with attempts := result.attempts ++ [{ index, body, hash, error := some error }] }
    | .ok (state, receipt, _) =>
      let receiptHash ← NativeIdentity.transactionReceipt hash ap.blockHeight
      let context ← extend result.context receipt.receiptId receiptHash
      result := { state, context, attempts := result.attempts ++ [{ index, body, hash, receipt := some receipt, receiptHash := some receiptHash }] }
  return result

end Near.TransactionRegistry
