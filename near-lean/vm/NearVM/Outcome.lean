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

/-- Each dependency refers to a receipt created earlier in this call. Repeated
edges are allowed: they represent separate data dependencies. -/
def ReceiptSpec.ValidAt (index : Nat) (r : ReceiptSpec) : Prop :=
  ∀ dependency ∈ r.dependencies, dependency < index

def receiptsValidFrom (index : Nat) : List ReceiptSpec → Bool
  | [] => true
  | r :: rs => r.dependencies.all (· < index) && receiptsValidFrom (index + 1) rs

def ReceiptsWellFormedFrom (index : Nat) : List ReceiptSpec → Prop
  | [] => True
  | r :: rs => r.ValidAt index ∧ ReceiptsWellFormedFrom (index + 1) rs

/-- The executable graph check proves backward-only dependencies, rather than
assuming host-created handles were valid. -/
theorem receiptsValidFrom_iff (rs : List ReceiptSpec) (index : Nat) :
    receiptsValidFrom index rs = true ↔ ReceiptsWellFormedFrom index rs := by
  induction rs generalizing index with
  | nil => simp [receiptsValidFrom, ReceiptsWellFormedFrom]
  | cons r rs ih =>
    simp [receiptsValidFrom, ReceiptsWellFormedFrom, ReceiptSpec.ValidAt, List.all_eq_true, ih]

/-- Looking up a receipt in a valid suffix preserves its creation-order bound. -/
theorem dependency_before_index {rs : List ReceiptSpec} {start index dependency : Nat}
    {r : ReceiptSpec} (hwf : ReceiptsWellFormedFrom start rs)
    (hget : rs[index]? = some r) (hdep : dependency ∈ r.dependencies) :
    dependency < start + index := by
  induction rs generalizing start index with
  | nil => simp at hget
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hget
      subst r
      exact hwf.1 _ hdep
    | succ index =>
      have htail : tail[index]? = some r := hget
      have hlt := ih hwf.2 htail
      omega

/-- Nonempty dependency paths in the exact emitted receipt list. -/
inductive ReceiptDependencyPath (rs : List ReceiptSpec) : Nat → Nat → Prop
  | edge {source target : Nat} {r : ReceiptSpec}
      (lookup : rs[source]? = some r) (member : target ∈ r.dependencies) :
      ReceiptDependencyPath rs source target
  | trans {source middle target : Nat}
      (first : ReceiptDependencyPath rs source middle)
      (rest : ReceiptDependencyPath rs middle target) : ReceiptDependencyPath rs source target

/-- Every dependency path strictly decreases creation indices, so callbacks
cannot indirectly depend on themselves. -/
theorem dependencyPath_decreases {rs : List ReceiptSpec}
    (hwf : ReceiptsWellFormedFrom 0 rs) {source target : Nat}
    (path : ReceiptDependencyPath rs source target) : target < source := by
  induction path with
  | edge lookup member =>
    simpa only [Nat.zero_add] using dependency_before_index hwf lookup member
  | trans _ _ ihFirst ihRest => exact Nat.lt_trans ihRest ihFirst

theorem no_receipt_dependency_cycle {rs : List ReceiptSpec}
    (hwf : ReceiptsWellFormedFrom 0 rs) (index : Nat) :
    ¬ReceiptDependencyPath rs index index := by
  intro path
  exact Nat.lt_irrefl index (dependencyPath_decreases hwf path)

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

/-- Validate handles before expanding joins. This prevents the expansion's
structural fuel from hiding cyclic or future join references. Yielded promises
remain unsupported by the metered VM and cannot disappear during conversion. -/
def promisesValidFrom (index : Nat) : List NearPromise → Bool
  | [] => true
  | p :: ps =>
    let valid := match p with
      | .batch _ _ => true
      | .callback base _ _ => base < index
      | .and dependencies => dependencies.all (· < index)
      | .yielded .. => false
    valid && promisesValidFrom (index + 1) ps

def PromiseWellFormedAt (index : Nat) : NearPromise → Prop
  | .batch _ _ => True
  | .callback base _ _ => base < index
  | .and dependencies => ∀ dependency ∈ dependencies, dependency < index
  | .yielded .. => False

def PromisesWellFormedFrom (index : Nat) : List NearPromise → Prop
  | [] => True
  | p :: ps => PromiseWellFormedAt index p ∧ PromisesWellFormedFrom (index + 1) ps

theorem promisesValidFrom_iff (ps : List NearPromise) (index : Nat) :
    promisesValidFrom index ps = true ↔ PromisesWellFormedFrom index ps := by
  induction ps generalizing index with
  | nil => simp [promisesValidFrom, PromisesWellFormedFrom]
  | cons p ps ih =>
    cases p <;> simp [promisesValidFrom, PromisesWellFormedFrom, PromiseWellFormedAt,
      List.all_eq_true, ih]

/-- A returned receipt must exist; dependency edges must point backwards. -/
def VMOutcome.receiptsValid (o : VMOutcome) : Bool :=
  receiptsValidFrom 0 o.receipts && match o.returnData with
    | .receiptIndex index => index < o.receipts.length
    | _ => true

/-- A malformed graph is an interpreter limitation. It rolls back the same
resources as other model issues, retaining diagnostic logs and burnt gas. -/
def VMOutcome.graphIssue (balance usage : Nat) (storage : List (List UInt8 × List UInt8))
    (o : VMOutcome) : VMOutcome :=
  { o with
    balance := balance, storageUsage := usage, storage := storage, receipts := [], returnData := .none
    usedGas := o.burntGas
    aborted := some (.executionIssue (.interpreterError "invalid receipt dependency graph")) }

def VMOutcome.checkReceipts (balance usage : Nat) (storage : List (List UInt8 × List UInt8))
    (o : VMOutcome) : VMOutcome :=
  if o.receiptsValid then o else o.graphIssue balance usage storage

def VMOutcome.checkPromiseHandles (balance usage : Nat) (storage : List (List UInt8 × List UInt8))
    (promises : List NearPromise) (o : VMOutcome) : VMOutcome :=
  if promisesValidFrom 0 promises then o else o.graphIssue balance usage storage

def VMOutcome.checkPromises (balance usage : Nat) (storage : List (List UInt8 × List UInt8))
    (promises : List NearPromise) (o : VMOutcome) : VMOutcome :=
  (o.checkPromiseHandles balance usage storage promises).checkReceipts balance usage storage

theorem checkReceipts_valid (o : VMOutcome) (balance usage : Nat)
    (storage : List (List UInt8 × List UInt8)) :
    (o.checkReceipts balance usage storage).receiptsValid = true := by
  unfold VMOutcome.checkReceipts
  split
  · assumption
  · rfl

theorem checkReceipts_invalid_atomic (o : VMOutcome) (balance usage : Nat)
    (storage : List (List UInt8 × List UInt8)) (h : o.receiptsValid = false) :
    let checked := o.checkReceipts balance usage storage
    checked.balance = balance ∧ checked.storageUsage = usage ∧ checked.storage = storage ∧
    checked.receipts = [] ∧ checked.issue? = some (.interpreterError "invalid receipt dependency graph") := by
  simp [VMOutcome.checkReceipts, VMOutcome.graphIssue, h, VMOutcome.issue?, FunctionCallError.issue?]

theorem checkPromises_valid (o : VMOutcome) (balance usage : Nat)
    (storage : List (List UInt8 × List UInt8)) (promises : List NearPromise) :
    (o.checkPromises balance usage storage promises).receiptsValid = true := by
  exact checkReceipts_valid _ balance usage storage

theorem checkPromises_invalid_atomic (o : VMOutcome) (balance usage : Nat)
    (storage : List (List UInt8 × List UInt8)) (promises : List NearPromise)
    (h : promisesValidFrom 0 promises = false) :
    let checked := o.checkPromises balance usage storage promises
    checked.balance = balance ∧ checked.storageUsage = usage ∧ checked.storage = storage ∧
    checked.receipts = [] ∧ checked.issue? = some (.interpreterError "invalid receipt dependency graph") := by
  simp [VMOutcome.checkPromises, VMOutcome.checkPromiseHandles, VMOutcome.checkReceipts,
    VMOutcome.graphIssue, VMOutcome.receiptsValid, receiptsValidFrom, h,
    VMOutcome.issue?, FunctionCallError.issue?]

theorem VMOutcome.receiptsWellFormed (o : VMOutcome) (h : o.receiptsValid = true) :
    ReceiptsWellFormedFrom 0 o.receipts := by
  unfold VMOutcome.receiptsValid at h
  simp only [Bool.and_eq_true] at h
  exact (receiptsValidFrom_iff o.receipts 0).mp h.1

theorem VMOutcome.returnedReceipt_lt (o : VMOutcome) (h : o.receiptsValid = true)
    {index : Nat} (hreturn : o.returnData = .receiptIndex index) : index < o.receipts.length := by
  unfold VMOutcome.receiptsValid at h
  simp only [hreturn, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- The checked boundary always emits an acyclic receipt graph. -/
theorem checkPromises_no_cycle (o : VMOutcome) (balance usage : Nat)
    (storage : List (List UInt8 × List UInt8)) (promises : List NearPromise) (index : Nat) :
    ¬ReceiptDependencyPath (o.checkPromises balance usage storage promises).receipts index index :=
  no_receipt_dependency_cycle
    ((o.checkPromises balance usage storage promises).receiptsWellFormed
      (checkPromises_valid o balance usage storage promises)) index

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
