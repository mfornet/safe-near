import NearRuntime.ReceiptInvariants
import NearVM.PromiseAccounting

namespace Near
open Wasm Wasm.Near

/-- Proof-facing decomposition of the executable id-allocation pass. -/
def allocateFunctionCallIds (specs : List ReceiptSpec) (initial : ChainState)
    (initialIds : Array ReceiptId := #[]) : ChainState × Array ReceiptId := Id.run do
  let mut st := initial
  let mut ids := initialIds
  for _ in specs do
    let (rid, next) := st.freshId
    st := next
    ids := ids.push rid
  return (st, ids)

def linkFunctionCallDependencies (specs : List ReceiptSpec) (initial : ChainState)
    (initialOutputs : Array (List DataReceiver)) (initialInputs : Array (List DataId)) :
    ChainState × Array (List DataReceiver) × Array (List DataId) := Id.run do
  let mut st := initial
  let mut outputs := initialOutputs
  let mut inputs := initialInputs
  for h : i in [0:specs.length] do
    let spec := specs[i]
    for dep in spec.dependencies do
      let (dataId, next) := st.freshId
      st := next
      outputs := outputs.modify dep (· ++ [{ dataId, receiverId := stringOfBytes spec.receiverId }])
      inputs := inputs.modify i (· ++ [dataId])
  return (st, outputs, inputs)

def emitFunctionCallData (receiver : AccountId) (value : Bytes) (outputs : List DataReceiver)
    (initial : ChainState) (initialReceipts : List Receipt := []) : ChainState × List Receipt := Id.run do
  let mut st := initial
  let mut receipts := initialReceipts
  for d in outputs do
    let (rid, next) := st.freshId
    st := next
    receipts := receipts ++ [{
      predecessorId := receiver, receiverId := d.receiverId, receiptId := rid
      receipt := .data { dataId := d.dataId, data := some value } }]
  return (st, receipts)

def emitFunctionCallActions (c : ReceiptCtx) (specs : List ReceiptSpec) (ids : Array ReceiptId)
    (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (initialReceipts : List Receipt := []) : List Receipt := Id.run do
  let mut receipts := initialReceipts
  for h : i in [0:specs.length] do
    let spec := specs[i]
    receipts := receipts ++ [{
      predecessorId := c.receipt.receiverId
      receiverId := stringOfBytes spec.receiverId
      receiptId := ids[i]?.getD 0
      receipt := .action {
        signerId := c.action.signerId
        signerPublicKey := c.action.signerPublicKey
        gasPrice := c.action.gasPrice
        outputDataReceivers := outputs[i]?.getD []
        inputDataIds := inputs[i]?.getD []
        yieldDataId := spec.yieldDataId
        actions := spec.actions.map (actionOfPromiseRaw c.codeOf) } }]
  return receipts

/-- This is definitional equality with the executable implementation, not an
assumed relation to a second receipt constructor. -/
theorem materializeFunctionCallRaw_eq_stages (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) : materializeFunctionCallRaw c isLast outcome initial =
    let allocation := allocateFunctionCallIds outcome.receipts initial
    let linking := linkFunctionCallDependencies outcome.receipts allocation.1
      (Array.replicate outcome.receipts.length []) (Array.replicate outcome.receipts.length [])
    let receivers : List DataReceiver := []
    let returned := match outcome.returnData with
      | .receiptIndex k => (linking.1, [], linking.2.1.modify k (· ++ receivers),
          ExecutionStatus.successReceiptId (allocation.2[k]?.getD 0))
      | .value value => (linking.1, [], linking.2.1, ExecutionStatus.successValue value)
      | .none => (linking.1, [], linking.2.1, ExecutionStatus.successValue [])
    { state := returned.1, receipts := emitFunctionCallActions c outcome.receipts allocation.2
        returned.2.2.1 linking.2.2 returned.2.1, result := returned.2.2.2 } := by
  cases hr : outcome.returnData <;>
    simp only [materializeFunctionCallRaw, allocateFunctionCallIds, linkFunctionCallDependencies,
      emitFunctionCallActions, hr] <;> rfl

/-- A projection untouched by every loop body is untouched by the full pass. -/
theorem foldl_frame (view : β → γ) (step : β → α → β)
    (h : ∀ st item, view (step st item) = view st) (items : List α) (initial : β) :
    view (items.foldl step initial) = view initial := by
  induction items generalizing initial with
  | nil => rfl
  | cons item rest ih => exact (ih (step initial item)).trans (h initial item)

/-- All non-id chain fields; this projection also preserves pending work. -/
def ChainState.withoutIds (st : ChainState) : ChainState :=
  { st with nextId := 0, yieldIndices := none, yieldTimeouts := [], yieldStatus := [] }

theorem allocateFunctionCallIds_frame (specs : List ReceiptSpec) (initial : ChainState)
    (ids : Array ReceiptId) :
    (allocateFunctionCallIds specs initial ids).1.withoutIds = initial.withoutIds := by
  simp only [allocateFunctionCallIds, ChainState.freshId, List.forIn_pure_yield_eq_foldl]
  exact foldl_frame (fun pair : ChainState × Array ReceiptId => pair.1.withoutIds) _
    (by intros; rfl) specs (initial, ids)

theorem linkFunctionCallDependencies_frame (specs : List ReceiptSpec) (initial : ChainState)
    (outputs : Array (List DataReceiver)) (inputs : Array (List DataId)) :
    (linkFunctionCallDependencies specs initial outputs inputs).1.withoutIds = initial.withoutIds := by
  simp only [linkFunctionCallDependencies, ChainState.freshId,
    List.forIn_pure_yield_eq_foldl, pure_bind, Std.Legacy.Range.forIn'_eq_forIn'_range',
    List.forIn'_pure_yield_eq_foldl]
  apply foldl_frame (fun triple : ChainState × Array (List DataReceiver) × Array (List DataId) => triple.1.withoutIds)
  intro triple item
  exact foldl_frame (fun triple : ChainState × Array (List DataReceiver) × Array (List DataId) => triple.1.withoutIds) _
    (by intros; rfl) _ triple

theorem emitFunctionCallData_frame (receiver : AccountId) (value : Bytes) (outputs : List DataReceiver)
    (initial : ChainState) (receipts : List Receipt) :
    (emitFunctionCallData receiver value outputs initial receipts).1.withoutIds = initial.withoutIds := by
  simp only [emitFunctionCallData, ChainState.freshId, List.forIn_pure_yield_eq_foldl]
  exact foldl_frame (fun pair : ChainState × List Receipt => pair.1.withoutIds) _
    (by intros; rfl) outputs (initial, receipts)

theorem foldl_additive (value : β → Nat) (step : β → α → β) (weight : α → Nat)
    (h : ∀ st item, value (step st item) = value st + weight item) (items : List α) (initial : β) :
    value (items.foldl step initial) = value initial + (items.map weight).sum := by
  induction items generalizing initial with
  | nil => simp
  | cons item rest ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [ih, h]
    omega

/-- Valuation ignores metadata and gives data receipts zero financial backing. -/
def chainReceiptValue (value : AccountId → List Action → Nat) (receipt : Receipt) : Nat :=
  match receipt.receipt with
  | .data _ | .globalDistribution _ => 0
  | .action action => value receipt.receiverId action.actions

def chainReceiptsValue (value : AccountId → List Action → Nat) (receipts : List Receipt) : Nat :=
  (receipts.map (chainReceiptValue value)).sum

@[simp] theorem chainReceiptsValue_append (value : AccountId → List Action → Nat) (xs ys : List Receipt) :
    chainReceiptsValue value (xs ++ ys) = chainReceiptsValue value xs + chainReceiptsValue value ys := by
  simp [chainReceiptsValue, List.map_append]

theorem emitFunctionCallData_value (value : AccountId → List Action → Nat) (receiver : AccountId)
    (bytes : Bytes) (outputs : List DataReceiver) (initial : ChainState) (receipts : List Receipt) :
    chainReceiptsValue value (emitFunctionCallData receiver bytes outputs initial receipts).2 =
      chainReceiptsValue value receipts := by
  simp only [emitFunctionCallData, ChainState.freshId, List.forIn_pure_yield_eq_foldl]
  apply foldl_frame (fun pair : ChainState × List Receipt => chainReceiptsValue value pair.2)
  intro pair item
  simp [chainReceiptsValue, chainReceiptValue, List.map_append]

theorem map_range'_get! [Inhabited α] (items : List α) :
    (List.range' 0 items.length).map (fun i => items[i]!) = items := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map, List.getElem_range', Nat.zero_add, Nat.one_mul]
    exact getElem!_pos items i hj

theorem emitFunctionCallActions_value (value : AccountId → List Action → Nat) (c : ReceiptCtx)
    (specs : List ReceiptSpec) (ids : Array ReceiptId) (outputs : Array (List DataReceiver))
    (inputs : Array (List DataId)) (receipts : List Receipt) :
    chainReceiptsValue value (emitFunctionCallActions c specs ids outputs inputs receipts) =
      chainReceiptsValue value receipts +
        (specs.map fun spec => value (stringOfBytes spec.receiverId) (spec.actions.map (actionOfPromiseRaw c.codeOf))).sum := by
  simp only [emitFunctionCallActions, Std.Legacy.Range.forIn'_eq_forIn'_range',
    List.forIn'_pure_yield_eq_foldl, Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  trans chainReceiptsValue value receipts +
    ((List.range' 0 specs.length).attach.map fun i => value (stringOfBytes specs[i.val]!.receiverId)
      (specs[i.val]!.actions.map (actionOfPromiseRaw c.codeOf))).sum
  · apply foldl_additive
    intro acc item
    have hb : item.val < specs.length := by
      have hm := List.mem_range'.mp item.property
      omega
    simp [chainReceiptsValue, chainReceiptValue, List.map_append, getElem!_pos specs item.val hb]
  · rw [List.attach_map_val (f := fun (i : Nat) => value (stringOfBytes specs[i]!.receiverId)
        (specs[i]!.actions.map (actionOfPromiseRaw c.codeOf)))]
    have hm := congrArg (fun xs : List ReceiptSpec =>
        (xs.map fun spec => value (stringOfBytes spec.receiverId)
          (spec.actions.map (actionOfPromiseRaw c.codeOf))).sum) (map_range'_get! specs)
    simpa only [List.map_map, Function.comp_def] using
      congrArg (fun n => chainReceiptsValue value receipts + n) hm

/-- Receipt construction changes no ledger, storage, key or scheduler field. -/
theorem materializeFunctionCallRaw_frame (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    (materializeFunctionCallRaw c isLast outcome initial).state.withoutIds = initial.withoutIds := by
  rw [materializeFunctionCallRaw_eq_stages]
  cases hr : outcome.returnData <;> dsimp only
  all_goals simp only [linkFunctionCallDependencies_frame, allocateFunctionCallIds_frame]

/-- The actual chain receipt constructor preserves every receiver/action
valuation, independently of ids, dependency shapes and returned receipt choice. -/
theorem materializeFunctionCallRaw_value (value : AccountId → List Action → Nat)
    (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome) (initial : ChainState) :
    chainReceiptsValue value (materializeFunctionCallRaw c isLast outcome initial).receipts =
      (outcome.receipts.map fun spec =>
        value (stringOfBytes spec.receiverId) (spec.actions.map (actionOfPromiseRaw c.codeOf))).sum := by
  rw [materializeFunctionCallRaw_eq_stages]
  cases hr : outcome.returnData <;> dsimp only
  all_goals rw [emitFunctionCallActions_value]
  all_goals exact Nat.zero_add _

@[simp] theorem actionOfPromiseRaw_deposit (codeOf : Bytes → ContractCode) (action : PromiseAction) :
    (actionOfPromiseRaw codeOf action).deposit = action.deposit := by
  cases action <;> rfl

/-- Memory-decoded VM deposits survive conversion into runtime actions. -/
theorem materializeFunctionCallRaw_deposits (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    chainReceiptsValue (fun _ actions => Fees.totalDeposit actions)
      (materializeFunctionCallRaw c isLast outcome initial).receipts = receiptsDeposits outcome.receipts := by
  rw [materializeFunctionCallRaw_value]
  simp [Fees.totalDeposit, List.map_map, Function.comp_def, receiptsDeposits, receiptsValue, depositValue]

theorem foldl_preserves (P : β → Prop) (step : β → α → β)
    (hstep : ∀ st item, P st → P (step st item)) (items : List α) (initial : β) (h : P initial) :
    P (items.foldl step initial) := by
  induction items generalizing initial with
  | nil => exact h
  | cons item rest ih => exact ih (step initial item) (hstep initial item h)

/-- Metadata used to interpret the monetary backing of materialized receipts. -/
def Receipt.FromVM (c : ReceiptCtx) (receipt : Receipt) : Prop :=
  receipt.predecessorId = c.receipt.receiverId ∧
  match receipt.receipt with
  | .data _ | .globalDistribution _ => True
  | .action action => action.gasPrice = c.action.gasPrice

theorem emitFunctionCallData_origin (c : ReceiptCtx) (bytes : Bytes) (outputs : List DataReceiver)
    (initial : ChainState) (receipts : List Receipt) (h : ∀ r ∈ receipts, r.FromVM c) :
    ∀ r ∈ (emitFunctionCallData c.receipt.receiverId bytes outputs initial receipts).2, r.FromVM c := by
  simp only [emitFunctionCallData, ChainState.freshId, List.forIn_pure_yield_eq_foldl]
  apply foldl_preserves (fun pair : ChainState × List Receipt => ∀ r ∈ pair.2, r.FromVM c) _ _ _ _ h
  intro pair item hpair r hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · exact hpair r hr
  · exact ⟨rfl, trivial⟩

theorem emitFunctionCallActions_origin (c : ReceiptCtx) (specs : List ReceiptSpec)
    (ids : Array ReceiptId) (outputs : Array (List DataReceiver)) (inputs : Array (List DataId))
    (receipts : List Receipt) (h : ∀ r ∈ receipts, r.FromVM c) :
    ∀ r ∈ emitFunctionCallActions c specs ids outputs inputs receipts, r.FromVM c := by
  simp only [emitFunctionCallActions, Std.Legacy.Range.forIn'_eq_forIn'_range',
    List.forIn'_pure_yield_eq_foldl]
  apply foldl_preserves (fun receipts : List Receipt => ∀ r ∈ receipts, r.FromVM c) _ _ _ _ h
  intro acc item hacc r hr
  simp only [List.mem_append, List.mem_singleton] at hr
  rcases hr with hr | rfl
  · exact hacc r hr
  · exact ⟨rfl, rfl⟩

theorem materializeFunctionCallRaw_origin (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    ∀ r ∈ (materializeFunctionCallRaw c isLast outcome initial).receipts, r.FromVM c := by
  rw [materializeFunctionCallRaw_eq_stages]
  cases hr : outcome.returnData <;> dsimp only
  all_goals apply emitFunctionCallActions_origin
  all_goals simp

/-- Financial valuation includes the exact gas purchase price. The system
predecessor case is retained explicitly rather than assumed impossible. -/
def functionCallReceiptValue (c : ReceiptCtx) (receiver : AccountId) (actions : List Action) : Nat :=
  Fees.totalDeposit actions + (if c.receipt.receiverId == systemAccount then 0
    else Fees.receiptGasBudget c.cfg receiver actions * c.action.gasPrice)

theorem receiptFunds_fromVM (c : ReceiptCtx) (receipt : Receipt) (h : receipt.FromVM c) :
    Fees.receiptFunds c.cfg receipt = chainReceiptValue (functionCallReceiptValue c) receipt := by
  cases hr : receipt.receipt with
  | data data => simp [Fees.receiptFunds, chainReceiptValue, hr]
  | globalDistribution distribution => simp [Fees.receiptFunds, chainReceiptValue, hr]
  | action action =>
    have hp : action.gasPrice = c.action.gasPrice := by simpa only [Receipt.FromVM, hr] using h.2
    simp only [Fees.receiptFunds, hr, Receipt.isRefund, h.1, hp,
      chainReceiptValue, functionCallReceiptValue]

/-- Full outgoing funds, including prepaid execution gas, are retained by the
actual constructor. Data receipts contribute no backing. -/
theorem materializeFunctionCallRaw_funds (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    receiptsFunds c.cfg (materializeFunctionCallRaw c isLast outcome initial).receipts =
      (outcome.receipts.map fun spec => functionCallReceiptValue c (stringOfBytes spec.receiverId)
        (spec.actions.map (actionOfPromiseRaw c.codeOf))).sum := by
  have hv := materializeFunctionCallRaw_value (functionCallReceiptValue c) c isLast outcome initial
  rw [← hv]
  unfold receiptsFunds chainReceiptsValue
  congr 1
  apply List.map_congr_left
  intro receipt hmem
  exact receiptFunds_fromVM c receipt (materializeFunctionCallRaw_origin c isLast outcome initial receipt hmem)

theorem allocateFunctionCallIds_nextId (specs : List ReceiptSpec) (initial : ChainState)
    (ids : Array ReceiptId) :
    (allocateFunctionCallIds specs initial ids).1.nextId = initial.nextId + specs.length := by
  simp only [allocateFunctionCallIds, ChainState.freshId, List.forIn_pure_yield_eq_foldl]
  trans initial.nextId + (specs.map fun _ => 1).sum
  · apply foldl_additive (fun pair : ChainState × Array ReceiptId => pair.1.nextId)
    intros; rfl
  · simp

theorem emitFunctionCallData_nextId (receiver : AccountId) (bytes : Bytes) (outputs : List DataReceiver)
    (initial : ChainState) (receipts : List Receipt) :
    (emitFunctionCallData receiver bytes outputs initial receipts).1.nextId = initial.nextId + outputs.length := by
  simp only [emitFunctionCallData, ChainState.freshId, List.forIn_pure_yield_eq_foldl]
  trans initial.nextId + (outputs.map fun _ => 1).sum
  · apply foldl_additive (fun pair : ChainState × List Receipt => pair.1.nextId)
    intros; rfl
  · simp

theorem sum_range'_get! [Inhabited α] (items : List α) (weight : α → Nat) :
    ((List.range' 0 items.length).attach.map fun i => weight items[i.val]!).sum = (items.map weight).sum := by
  rw [List.attach_map_val (f := fun (i : Nat) => weight items[i]!)]
  have hm := congrArg (fun xs : List α => (xs.map weight).sum) (map_range'_get! items)
  simpa only [List.map_map, Function.comp_def] using hm

theorem linkFunctionCallDependencies_nextId (specs : List ReceiptSpec) (initial : ChainState)
    (outputs : Array (List DataReceiver)) (inputs : Array (List DataId)) :
    (linkFunctionCallDependencies specs initial outputs inputs).1.nextId =
      initial.nextId + (specs.map fun spec => spec.dependencies.length).sum := by
  simp only [linkFunctionCallDependencies, ChainState.freshId, List.forIn_pure_yield_eq_foldl,
    pure_bind, Std.Legacy.Range.forIn'_eq_forIn'_range', List.forIn'_pure_yield_eq_foldl,
    Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  trans initial.nextId + ((List.range' 0 specs.length).attach.map fun i => specs[i.val]!.dependencies.length).sum
  · apply foldl_additive (fun triple : ChainState × Array (List DataReceiver) × Array (List DataId) => triple.1.nextId)
    intro triple item
    have hb : item.val < specs.length := by
      have hm := List.mem_range'.mp item.property
      omega
    rw [getElem!_pos specs item.val hb]
    trans triple.1.nextId + (specs[item.val].dependencies.map fun _ => 1).sum
    · apply foldl_additive (fun triple : ChainState × Array (List DataReceiver) × Array (List DataId) => triple.1.nextId)
      intros; rfl
    · simp
  · rw [sum_range'_get! specs (fun spec => spec.dependencies.length)]

/-- One receipt id per promise and data id per dependency, plus data receipt ids
for direct returns. Returned promises allocate no duplicate output receipts. -/
theorem materializeFunctionCallRaw_nextId (c : ReceiptCtx) (isLast : Bool) (outcome : VMOutcome)
    (initial : ChainState) :
    (materializeFunctionCallRaw c isLast outcome initial).state.nextId = initial.nextId + outcome.receipts.length +
      (outcome.receipts.map fun spec => spec.dependencies.length).sum := by
  rw [materializeFunctionCallRaw_eq_stages]
  cases hr : outcome.returnData <;> dsimp only
  all_goals simp [linkFunctionCallDependencies_nextId,
    allocateFunctionCallIds_nextId]

theorem allocateFunctionCallIds_nil (initial : ChainState) (ids : Array ReceiptId) :
    allocateFunctionCallIds [] initial ids = (initial, ids) := rfl

theorem allocateFunctionCallIds_cons (spec : ReceiptSpec) (specs : List ReceiptSpec)
    (initial : ChainState) (ids : Array ReceiptId) :
    allocateFunctionCallIds (spec :: specs) initial ids =
      allocateFunctionCallIds specs { initial with nextId := initial.nextId + 1 } (ids.push initial.nextId) := by
  simp only [allocateFunctionCallIds, ChainState.freshId, List.forIn_pure_yield_eq_foldl, List.foldl_cons]

/-- Promise receipt ids are the consecutive fresh range, in promise order. -/
theorem allocateFunctionCallIds_ids (specs : List ReceiptSpec) (initial : ChainState) (ids : Array ReceiptId) :
    (allocateFunctionCallIds specs initial ids).2.toList = ids.toList ++ List.range' initial.nextId specs.length := by
  induction specs generalizing initial ids with
  | nil => simp [allocateFunctionCallIds_nil]
  | cons spec specs ih =>
    rw [allocateFunctionCallIds_cons, ih]
    simp [List.range'_succ, List.append_assoc]

theorem allocateFunctionCallIds_nodup (specs : List ReceiptSpec) (initial : ChainState) :
    (allocateFunctionCallIds specs initial).2.toList.Nodup := by
  rw [allocateFunctionCallIds_ids]
  simpa only [Array.toList_empty, List.nil_append] using
    (List.nodup_range' (s := initial.nextId) (n := specs.length))

theorem allocateFunctionCallIds_bounds (specs : List ReceiptSpec) (initial : ChainState) (id : ReceiptId)
    (hmem : id ∈ (allocateFunctionCallIds specs initial).2.toList) :
    initial.nextId ≤ id ∧ id < (allocateFunctionCallIds specs initial).1.nextId := by
  have hm : id ∈ List.range' initial.nextId specs.length := by
    simpa only [allocateFunctionCallIds_ids, Array.toList_empty, List.nil_append] using hmem
  rw [allocateFunctionCallIds_nextId]
  exact List.mem_range'_1.mp hm

end Near
