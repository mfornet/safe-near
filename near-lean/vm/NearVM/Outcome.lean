import NearVM.State
import NearVM.Error

/-!
# `VMOutcome`: the output of one function call

Mirrors `near_vm_runner::logic::VMOutcome`, plus the receipts the call
created (nearcore hands those to the `External`; here they are returned).
-/

namespace Wasm.Near

structure VMOutcome where
  /-- Liquid balance after the attached deposit and outgoing promise deposits;
  the input balance is restored on a failed VM call. -/
  balance : Nat
  /-- Storage usage after the call. -/
  storageUsage : Nat
  returnData : ReturnData
  burntGas : Nat
  usedGas : Nat
  logs : List String
  /-- Contract storage after the call (the input storage when the call failed). -/
  storage : List (List UInt8 × List UInt8)
  /-- External trie state after the attempt, retaining cache warming on failure.
  Failed-call prospective writes must be rolled back by the receipt executor. -/
  storageAccounting : Option _root_.Near.TrieOverlay.State := none
  receipts : List ReceiptSpec
  /-- `none` on success. -/
  aborted : Option FunctionCallError
  /-- Unused prepaid gas added to weighted function calls after the call
  (`distribute_gas`); included in `usedGas`. The VM runner's own `used_gas`
  is `usedGas - distributedGas`. -/
  distributedGas : Nat := 0
  /-- Attempted sponsored deposits, retained as diagnostics on VM failure. -/
  subsidizedAmount : Nat := 0
  gasProfile : GasProfile := {}
  /-- `promise_yield_resume` payloads, in call order: (data id, payload). -/
  resumes : List (List UInt8 × List UInt8) := []
  deriving Inhabited

def VMOutcome.succeeded (o : VMOutcome) : Bool := o.aborted.isNone

/-- `some` means this attempt establishes neither success nor protocol failure. -/
def VMOutcome.issue? (o : VMOutcome) : Option ExecutionIssue :=
  o.aborted.bind FunctionCallError.issue?

/-- Supported handle creation order: callbacks and joints refer only to earlier
handles. Yielded promises wait for their own data and refer to no handle. -/
def promisesValidFrom (index : Nat) : List NearPromise → Bool
  | [] => true
  | p :: ps =>
    let valid := match p with
      | .batch _ _ => true
      | .callback base _ _ => base < index
      | .and dependencies => dependencies.all (· < index)
      | .yielded .. => true
    valid && promisesValidFrom (index + 1) ps

def PromiseWellFormedAt (index : Nat) : NearPromise → Prop
  | .batch _ _ => True
  | .callback base _ _ => base < index
  | .and dependencies => ∀ dependency ∈ dependencies, dependency < index
  | .yielded .. => True

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
    usedGas := o.burntGas, distributedGas := 0
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

end Wasm.Near
