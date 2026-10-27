import NearRuntime.Refinement
import NearVM.MeteredPureBudget

/-!
# Observing metered budget simulations at the receipt boundary

The byte-log prefix of a stopped interpreter becomes the string-log prefix
reported by the boundary. Both actual protocol gas errors roll back all
receipt effects, even when later action/receipt checks are supplied.
-/
namespace Near.Boundary
open Wasm Wasm.Near NearInterface MeteredPrefix MeteredPureBudget

/-- Boundary log decoding preserves actual byte-log prefixes. -/
theorem logsOf_prefix {small large : NearState} (h : List.IsPrefix small.logs large.logs) :
    List.IsPrefix (logsOf small) (logsOf large) := by
  obtain ⟨suffix, hs⟩ := h
  refine ⟨suffix.map (fun bytes => (String.fromUTF8? ⟨bytes.toArray⟩).getD ""), ?_⟩
  simp only [logsOf, ← hs, List.map_append]

/-- Failure conversion classifies either concrete metering limit as out of gas. -/
theorem failureOf_gasError {error : HostError} (h : GasError error) :
    failureOf (.hostError error) = .outOfGas := by
  rcases h with rfl | rfl <;> rfl

/-- VM outcome conversion retains the stopped machine's decoded logs,
including promise conversion and all failure branches. -/
theorem outcomeOfExecution_logs (ctx : VMContext) (raw : List (Bytes × Bytes))
    (machine : Machine) (error : Option FunctionCallError) :
    (outcomeOfExecution ctx raw machine error).logs = logsOf machine.host := by
  unfold outcomeOfExecution
  dsimp only
  repeat' first | rfl | (split <;> try dsimp only)

/-- The body simulation's gas alternative supplies the complete boundary
alternative: out-of-gas outcome, rollback, and decoded prefix logs. -/
theorem observe_gasFailure (ctx : Context) (raw : List (Bytes × Bytes))
    (low : Machine × Option FunctionCallError) (high : Machine)
    (issue : Option ExecutionIssue) (receiptError : Option RuntimeError)
    (hgas : GasFailure low) (hlogs : LogPrefix low.1 high) :
    let observed := observe ctx raw (outcomeOfExecution (toVMContext ctx) raw low.1 low.2) issue receiptError
    observed.outcome = .error .outOfGas ∧ RolledBack ctx raw.toFinset observed ∧
      observed.logs <+: logsOf high.host := by
  obtain ⟨error, he, ha⟩ := hgas.aborted (toVMContext ctx) raw
  apply observe_outOfGas ha (failureOf_gasError he)
  rw [outcomeOfExecution_logs]
  exact logsOf_prefix hlogs

/-- Only counter limits and diagnostic profiles are omitted. Burnt and
reserved gas, guest context, storage, logs and promise state remain intact. -/
def budgetHost (host : NearState) : NearState :=
  { MeteredHosts.Budget.functional host with
    gas := { burnt := host.gas.burnt, promises := host.gas.promises } }

def budgetStore (store : Store NearState) : Store NearState :=
  { store with host := budgetHost store.host }

def budgetMachine : Machine → Machine
  | .next c => .next {c with store := budgetStore c.store}
  | .done values store => .done values (budgetStore store)
  | .trap reason store => .trap reason (budgetStore store)

def outcomeView (outcome : VMOutcome) : VMOutcome :=
  { outcome with gasProfile := {}, actionProfile := [] }

theorem budgetHost_eq {small large : NearState} (h : MeteredHosts.Budget.HostBelow small large) :
    budgetHost small = budgetHost large := by
  simp only [budgetHost, h.fields, h.gas.burnt, h.gas.promises]

theorem budgetStore_eq {small large : Store NearState} (h : StoreBelow small large) :
    budgetStore small = budgetStore large := by
  have hf := congrArg (fun store : Store NearState => {store with host := budgetHost large.host}) h.fields
  simpa only [budgetStore, budgetHost_eq h.host] using hf

theorem budgetMachine_eq {small large : Machine} (h : MachineBelow small large) :
    budgetMachine small = budgetMachine large := by
  cases h with
  | @next small large h =>
    cases small with
    | mk ss st sl =>
      cases large with
      | mk ls lt ll =>
        obtain ⟨hs, ht, hl⟩ := h
        dsimp only at ht hl
        cases ht
        cases hl
        simp only [budgetMachine]
        rw [show budgetStore ss = budgetStore ls from budgetStore_eq hs]
  | done values h => simp only [budgetMachine, budgetStore_eq h]
  | trapped reason h => simp only [budgetMachine, budgetStore_eq h]

/-- Actual outcome conversion never reads the counter limits. Its only
budget-dependent diagnostics are the profiles erased by outcomeView. -/
theorem outcomeView_budgetMachine (ctx : VMContext) (raw : List (Bytes × Bytes))
    (machine : Machine) (error : Option FunctionCallError) :
    outcomeView (outcomeOfExecution ctx raw (budgetMachine machine) error) =
      outcomeView (outcomeOfExecution ctx raw machine error) := by
  cases machine <;> cases error
  all_goals unfold outcomeOfExecution budgetMachine budgetStore budgetHost MeteredHosts.Budget.functional
  all_goals dsimp only [StepResult.host, GasCounter.used]
  all_goals try simp only [PromiseGraph.returnData?]
  all_goals repeat' first | rfl | (split <;> try dsimp only)

/-- Matched machine results have identical functional VM outcomes, with exact
burnt/used gas; only diagnostic profiles may differ. -/
theorem outcomeView_below (ctx : VMContext) (raw : List (Bytes × Bytes))
    {small large : Machine} (h : MachineBelow small large) (error : Option FunctionCallError) :
    outcomeView (outcomeOfExecution ctx raw small error) =
      outcomeView (outcomeOfExecution ctx raw large error) := by
  rw [← outcomeView_budgetMachine ctx raw small error, ← outcomeView_budgetMachine ctx raw large error,
    budgetMachine_eq h]

/-- The receipt boundary does not observe diagnostic profiles. -/
theorem observe_outcomeView (ctx : Context) (raw : List (Bytes × Bytes)) (outcome : VMOutcome)
    (issue : Option ExecutionIssue) (receiptError : Option RuntimeError) :
    observe ctx raw (outcomeView outcome) issue receiptError = observe ctx raw outcome issue receiptError := rfl

/-- The matching branch of a body simulation yields exact receipt observations,
including storage, stake failure, gas, logs, receipts and final trie. -/
theorem observe_ofExecution_below (ctx : Context) (raw : List (Bytes × Bytes))
    {small large : Machine} (h : MachineBelow small large) (error : Option FunctionCallError)
    (issue : Option ExecutionIssue) (receiptError : Option RuntimeError) :
    observe ctx raw (outcomeOfExecution (toVMContext ctx) raw small error) issue receiptError =
      observe ctx raw (outcomeOfExecution (toVMContext ctx) raw large error) issue receiptError := by
  rw [← observe_outcomeView ctx raw _ issue receiptError, ← observe_outcomeView ctx raw
    (outcomeOfExecution (toVMContext ctx) raw large error) issue receiptError,
    outcomeView_below (toVMContext ctx) raw h error]

/-- The actual public receipt checks and action conversion applied to a raw
attempt, factored only for proving the observation bridge. -/
def observeChecked (codeOf : Bytes → ContractCode) (ctx : Context)
    (raw : List (Bytes × Bytes)) (outcome : VMOutcome) : Observation :=
  let checked := outcome.checkReceipts (toVMContext ctx).accountBalance (toVMContext ctx).storageUsage raw
  observe ctx raw checked (actionsIssue? codeOf checked.receipts)
    (match checkVMReceipts ctx.protocol codeOf ctx.current ctx.signer ctx.signerPk checked.receipts with
      | .error error => some (.newReceiptValidationError error)
      | .ok () => none)

theorem execOn_observeChecked (code : Code) (ctx : Context) (raw : List (Bytes × Bytes))
    (hdecode : code.code.decodeIssue = none) :
    execOn code raw ctx = observeChecked code.codeOf ctx raw
      (runAttempt ctx.protocol code.code.module code.code.size ctx.method (toVMContext ctx) raw
        (fuelFor ctx.protocol code.code.module (toVMContext ctx))) := by
  simp only [execOn, hdecode, run, observeChecked]
  rfl

theorem observeChecked_outcomeView (codeOf : Bytes → ContractCode) (ctx : Context)
    (raw : List (Bytes × Bytes)) (outcome : VMOutcome) :
    observeChecked codeOf ctx raw (outcomeView outcome) = observeChecked codeOf ctx raw outcome := by
  unfold observeChecked VMOutcome.checkReceipts
  rw [show (outcomeView outcome).receiptsValid = outcome.receiptsValid from rfl]
  split <;> rfl

/-- All actual public checks preserve matched machine observations. -/
theorem observeChecked_ofExecution_below (codeOf : Bytes → ContractCode) (ctx : Context)
    (raw : List (Bytes × Bytes)) {small large : Machine} (h : MachineBelow small large)
    (error : Option FunctionCallError) :
    observeChecked codeOf ctx raw (outcomeOfExecution (toVMContext ctx) raw small error) =
      observeChecked codeOf ctx raw (outcomeOfExecution (toVMContext ctx) raw large error) := by
  rw [← observeChecked_outcomeView codeOf ctx raw _, ← observeChecked_outcomeView codeOf ctx raw
    (outcomeOfExecution (toVMContext ctx) raw large error), outcomeView_below (toVMContext ctx) raw h error]

/-- A gas failure has no created receipt graph to invalidate. -/
theorem gasFailure_receiptsValid (ctx : VMContext) (raw : List (Bytes × Bytes))
    (result : Machine × Option FunctionCallError) (h : GasFailure result) :
    (outcomeOfExecution ctx raw result.1 result.2).receiptsValid = true := by
  obtain ⟨error, _, he | ⟨he, reason, store, hm, ht⟩⟩ := h
  · simp [outcomeOfExecution, he, VMOutcome.receiptsValid, receiptsValidFrom]
  · simp [outcomeOfExecution, he, hm, StepResult.host, ht,
      VMOutcome.receiptsValid, receiptsValidFrom]

/-- The public receipt checks retain the simulation's gas alternative. -/
theorem observeChecked_gasFailure (codeOf : Bytes → ContractCode) (ctx : Context)
    (raw : List (Bytes × Bytes)) (low : Machine × Option FunctionCallError) (high : Machine)
    (hgas : GasFailure low) (hlogs : LogPrefix low.1 high) :
    let observed := observeChecked codeOf ctx raw (outcomeOfExecution (toVMContext ctx) raw low.1 low.2)
    observed.outcome = .error .outOfGas ∧ RolledBack ctx raw.toFinset observed ∧
      observed.logs <+: logsOf high.host := by
  unfold observeChecked
  rw [VMOutcome.checkReceipts, gasFailure_receiptsValid (toVMContext ctx) raw low hgas]
  exact observe_gasFailure ctx raw low high _ _ hgas hlogs

theorem observe_logs (ctx : Context) (raw : List (Bytes × Bytes)) (outcome : VMOutcome)
    (issue : Option ExecutionIssue) (receiptError : Option RuntimeError) :
    (observe ctx raw outcome issue receiptError).logs = outcome.logs := by
  unfold observe
  repeat' first | rfl | (split <;> try dsimp only)

theorem observeChecked_logs (codeOf : Bytes → ContractCode) (ctx : Context)
    (raw : List (Bytes × Bytes)) (outcome : VMOutcome) :
    (observeChecked codeOf ctx raw outcome).logs = outcome.logs := by
  unfold observeChecked
  rw [observe_logs]
  unfold VMOutcome.checkReceipts
  split <;> rfl

/-- A valid actual protocol-gas outcome survives public receipt checking. -/
theorem observeChecked_protocolGas (codeOf : Bytes → ContractCode) (ctx : Context)
    (raw : List (Bytes × Bytes)) (outcome : VMOutcome) (error : HostError) (logs : List String)
    (hgas : GasError error) (habort : outcome.aborted = some (.hostError error))
    (hvalid : outcome.receiptsValid = true) (hlogs : outcome.logs <+: logs) :
    let observed := observeChecked codeOf ctx raw outcome
    observed.outcome = .error .outOfGas ∧ RolledBack ctx raw.toFinset observed ∧ observed.logs <+: logs := by
  unfold observeChecked
  rw [VMOutcome.checkReceipts, hvalid]
  exact observe_outOfGas habort (failureOf_gasError hgas) hlogs

/-- Both alternatives of the actual body relation lift through every public
receipt check. The matching branch has exact observations, including gas. -/
theorem observeChecked_matchesOrGas (codeOf : Bytes → ContractCode) (ctx : Context)
    (raw : List (Bytes × Bytes)) (low high : Machine × Option FunctionCallError)
    (h : MatchesOrGas MachineBelow low high) :
    observeChecked codeOf ctx raw (outcomeOfExecution (toVMContext ctx) raw low.1 low.2) =
      observeChecked codeOf ctx raw (outcomeOfExecution (toVMContext ctx) raw high.1 high.2) ∨
    (let observed := observeChecked codeOf ctx raw (outcomeOfExecution (toVMContext ctx) raw low.1 low.2)
     observed.outcome = .error .outOfGas ∧ RolledBack ctx raw.toFinset observed ∧
       observed.logs <+: (observeChecked codeOf ctx raw
         (outcomeOfExecution (toVMContext ctx) raw high.1 high.2)).logs) := by
  rcases h with ⟨hstate, he⟩ | ⟨hgas, hl⟩
  · left
    rw [he]
    exact observeChecked_ofExecution_below codeOf ctx raw hstate.state high.2
  · right
    have hg := observeChecked_gasFailure codeOf ctx raw low high.1 hgas hl
    refine ⟨hg.1, hg.2.1, ?_⟩
    simpa only [observeChecked_logs, outcomeOfExecution_logs] using hg.2.2

end Near.Boundary
