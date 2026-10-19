import NearVM.State
import NearVM.Error

/-!
# `VMOutcome`: the output of one function call

Mirrors `near_vm_runner::logic::VMOutcome`, plus the receipts the call
created (nearcore hands those to the `External`; here they are returned).
-/

namespace Wasm.Near

/-- `ReturnData`. -/
inductive ReturnData
  | value (bytes : List UInt8)
  /-- The call's result is the result of the receipt created at this index. -/
  | receiptIndex (idx : Nat)
  | none
  deriving Repr, BEq, Inhabited

/-- One receipt to create, in the order of `promise_batch_create` /
`promise_then` calls. `dependencies` are indices into the same list: the
receipt runs once each of them has produced its data. -/
structure ReceiptSpec where
  receiverId : List UInt8
  actions : List PromiseAction
  dependencies : List Nat := []
  deriving BEq, Inhabited

structure VMOutcome where
  /-- Account balance after the call (unchanged by the VM itself). -/
  balance : Nat
  /-- Storage usage after the call. -/
  storageUsage : Nat
  returnData : ReturnData
  burntGas : Nat
  usedGas : Nat
  logs : List String
  /-- Contract storage after the call (the input storage when the call failed). -/
  storage : List (List UInt8 × List UInt8)
  receipts : List ReceiptSpec
  /-- `none` on success. -/
  aborted : Option FunctionCallError
  gasProfile : GasProfile := {}
  deriving Inhabited

def VMOutcome.succeeded (o : VMOutcome) : Bool := o.aborted.isNone

/-- `some` means this attempt establishes neither success nor protocol failure. -/
def VMOutcome.issue? (o : VMOutcome) : Option ExecutionIssue :=
  o.aborted.bind FunctionCallError.issue?

/-- Promise handles become receipts: `and` promises are not receipts, they
only widen the dependencies of the callback chained on them. -/
def promisesToReceipts (ps : List NearPromise) : List ReceiptSpec :=
  let arr := ps.toArray
  -- Receipt index of promise `i`: promises that are joins have no receipt.
  let receiptIdx : Array (Option Nat) := Id.run do
    let mut out := #[]
    let mut next := 0
    for p in arr do
      match p with
      | .and _ => out := out.push none
      | _ => out := out.push (some next); next := next + 1
    return out
  let rec deps (fuel : Nat) (i : Nat) : List Nat :=
    match fuel with
    | 0 => []
    | fuel + 1 =>
      match arr[i]? with
      | some (.and ds) => ds.flatMap (deps fuel)
      | some _ => (receiptIdx[i]?.bind id).toList
      | none => []
  arr.toList.filterMap fun p =>
    match p with
    | .batch acct actions => some { receiverId := acct, actions := actions }
    | .callback base acct actions =>
      some { receiverId := acct, actions := actions, dependencies := deps arr.size base }
    | .and _ => none
    | .yielded _ _ _ _ _ => none

/-- `promise_return` selects a promise; the result is that promise's receipt. -/
def returnedReceipt? (ps : List NearPromise) (idx : Nat) : Option Nat :=
  let before := ps.take idx
  match ps[idx]? with
  | some (.and _) => none
  | some _ => some (before.filter (fun p => match p with | .and _ => false | _ => true)).length
  | none => none

end Wasm.Near
