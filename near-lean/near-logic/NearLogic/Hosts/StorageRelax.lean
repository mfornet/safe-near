import NearLogic.Hosts.RelaxFns

/-!
# The storage phase under raised gas limits

`prepareStorageCallAux` (nearcore's external storage phase) touches the gas
counter only by billing charges, so under raised limits it runs the same,
with the limits raised, unless a bill fails under the lower limits
(`prepareStorageCallAux_relax`). The proof walks both runs in step: the
raised host is kept folded as `relax H p m` (`relax_*`, `fold_acc`), and
each bill of the raised run is matched with the lower run's (`bill_case`).
-/

namespace NearLogic

open Wasm Wasm.Near Lean Elab Tactic Meta

theorem relax_storage (h : NearState) (p m : Nat) : (relax h p m).storage = h.storage := rfl
theorem relax_storageAccounting (h : NearState) (p m : Nat) : (relax h p m).storageAccounting = h.storageAccounting := rfl
theorem relax_storageProofSize (h : NearState) (p m : Nat) : (relax h p m).storageProofSize = h.storageProofSize := rfl
theorem relax_storageReadsFromTrie (h : NearState) (p m : Nat) : (relax h p m).storageReadsFromTrie = h.storageReadsFromTrie := rfl
theorem relax_storageKeys (h : NearState) (p m : Nat) : (relax h p m).storageKeys = h.storageKeys := rfl
theorem relax_iterators (h : NearState) (p m : Nat) : (relax h p m).iterators = h.iterators := rfl
theorem relax_nextIteratorId (h : NearState) (p m : Nat) : (relax h p m).nextIteratorId = h.nextIteratorId := rfl
theorem relax_registers (h : NearState) (p m : Nat) : (relax h p m).registers = h.registers := rfl
theorem relax_context (h : NearState) (p m : Nat) : (relax h p m).context = h.context := rfl
theorem relax_subsidizedAmount (h : NearState) (p m : Nat) : (relax h p m).subsidizedAmount = h.subsidizedAmount := rfl
theorem relax_returnData (h : NearState) (p m : Nat) : (relax h p m).returnData = h.returnData := rfl
theorem relax_logs (h : NearState) (p m : Nat) : (relax h p m).logs = h.logs := rfl
theorem relax_promiseResults (h : NearState) (p m : Nat) : (relax h p m).promiseResults = h.promiseResults := rfl
theorem relax_promises (h : NearState) (p m : Nat) : (relax h p m).promises = h.promises := rfl
theorem relax_gasWeights (h : NearState) (p m : Nat) : (relax h p m).gasWeights = h.gasWeights := rfl
theorem relax_returnedPromise (h : NearState) (p m : Nat) : (relax h p m).returnedPromise = h.returnedPromise := rfl
theorem relax_yieldResumes (h : NearState) (p m : Nat) : (relax h p m).yieldResumes = h.yieldResumes := rfl
theorem relax_actionHash (h : NearState) (p m : Nat) : (relax h p m).actionHash = h.actionHash := rfl
theorem relax_existingYields (h : NearState) (p m : Nat) : (relax h p m).existingYields = h.existingYields := rfl
theorem relax_config (h : NearState) (p m : Nat) : (relax h p m).config = h.config := rfl
theorem relax_randomSeed (h : NearState) (p m : Nat) : (relax h p m).randomSeed = h.randomSeed := rfl
theorem relax_gasProfile (h : NearState) (p m : Nat) : (relax h p m).gasProfile = h.gasProfile := rfl
theorem relax_extCosts (h : NearState) (p m : Nat) : (relax h p m).extCosts = h.extCosts := rfl
theorem relax_fees (h : NearState) (p m : Nat) : (relax h p m).fees = h.fees := rfl
theorem relax_outputDataReceivers (h : NearState) (p m : Nat) : (relax h p m).outputDataReceivers = h.outputDataReceivers := rfl
theorem relax_lastError (h : NearState) (p m : Nat) : (relax h p m).lastError = h.lastError := rfl
theorem relax_lastExecutionIssue (h : NearState) (p m : Nat) : (relax h p m).lastExecutionIssue = h.lastExecutionIssue := rfl
theorem relax_yieldCreateToken (h : NearState) (p m : Nat) : (relax h p m).yieldCreateToken = h.yieldCreateToken := rfl
theorem relax_crypto (h : NearState) (p m : Nat) : (relax h p m).crypto = h.crypto := rfl
theorem relax_registerWrite (h : NearState) (p m : Nat) : (relax h p m).registerWrite = h.registerWrite := rfl
theorem relax_storageLog (h : NearState) (p m : Nat) : (relax h p m).storageLog = h.storageLog := rfl
theorem relax_actionProfile (h : NearState) (p m : Nat) : (relax h p m).actionProfile = h.actionProfile := rfl

theorem fold_acc (h : NearState) (p m : Nat) (x : Option _root_.Near.TrieOverlay.State) :
    ({ h with storageAccounting := x, gas := (relax h p m).gas } : NearState) =
      relax { h with storageAccounting := x } p m := rfl

theorem fold_store (s : HostStore NearState) (h : NearState) (p m : Nat) :
    ({ s with host := relax h p m } : HostStore NearState) = relaxSt { s with host := h } p m := rfl

theorem getMemOrReg_relaxHost (mem : Memory) (h : NearState) (p m : Nat) (a b : UInt64) :
    getMemOrReg { mem, host := relax h p m } a b = getMemOrReg { mem, host := h } a b := rfl

theorem recordedStorageError_relax (h : NearState) (p m : Nat) (t : _root_.Near.TrieOverlay.State) :
    recordedStorageError (relax h p m) t = recordedStorageError h t := rfl

/-- The relation between the raised and the lower run of the phase. -/
def StorageRel (p m : Nat) (x y : HostStore NearState × Option FunctionCallError) : Prop :=
  (∃ e, y.2 = some (.hostError e) ∧ isGasError e) ∨ x = (relaxSt y.1 p m, y.2)

/-- Fold the raised run's hosts back into `relax H p m`. -/
macro "relax_norm" : tactic => `(tactic| simp only [getMemOrReg_relaxHost, recordedStorageError_relax, fold_acc,
  relax_storage, relax_storageAccounting, relax_storageProofSize, relax_storageReadsFromTrie, relax_storageKeys, relax_iterators, relax_nextIteratorId, relax_registers, relax_context, relax_subsidizedAmount, relax_returnData, relax_logs, relax_promiseResults, relax_promises, relax_gasWeights, relax_returnedPromise, relax_yieldResumes, relax_actionHash, relax_existingYields, relax_config, relax_randomSeed, relax_gasProfile, relax_extCosts, relax_fees, relax_outputDataReceivers, relax_lastError, relax_lastExecutionIssue, relax_yieldCreateToken, relax_crypto, relax_registerWrite, relax_storageLog, relax_actionProfile] at *)

set_option hygiene false in
/-- Find a bill `applyCharges (relax H p m) cs` of the raised run and case on
the lower run's `applyCharges H cs`. -/
elab "bill_case" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e => e.isAppOfArity ``applyCharges 2 && (e.getArg! 0).isAppOfArity ``relax 3 &&
      !e.hasLooseBVars)
    | throwError "bill_case: no raised bill"
  let hs ← Term.exprToSyntax ((e.getArg! 0).getArg! 0)
  let css ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| obtain ⟨⟨h1, e1⟩, hb⟩ : ∃ r, applyCharges $hs $css = r := ⟨_, rfl⟩))
  evalTactic (← `(tactic| have hlim := applyCharges_gas_limits $hs $css))

theorem applyCharges_relax_of {ns h1 : NearState} {cs : List Charge} {p m : Nat} (hp : ns.gas.prepaid ≤ p)
    (hm : ns.gas.maxBurnt ≤ m) (hb : applyCharges ns cs = (h1, none)) :
    applyCharges (relax ns p m) cs = (relax h1 p m, none) := by
  rw [applyCharges_relax ns cs p m hp hm (by rw [hb])]
  rw [hb]

/-- Case on the outermost closed `if` condition or `match` discriminant of the raised run, and
reduce the lower run (`hy`) with it. -/
elab "csplit" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let env ← getEnv
  let isSplit (e : Lean.Expr) : Bool :=
    !e.hasLooseBVars && ((e.isAppOfArity ``ite 5 && !(e.getArg! 1).hasLooseBVars &&
      ((e.getArg! 1).find? (fun t => t.isConstOf ``applyCharges)).isNone) ||
      (match e.getAppFn with
       | Lean.Expr.const n _ => (Lean.Meta.Match.Extension.getMatcherInfo? env n).isSome
       | _ => false))
  let some e := tgt.find? isSplit | throwError "csplit: nothing to split"
  if e.isAppOfArity ``ite 5 then
    let g ← getMainGoal
    let r ← g.byCases (e.getArg! 1) `hc
    replaceMainGoal [r.1.mvarId, r.2.mvarId]
    evalTactic (← `(tactic| all_goals (try simp only [$(mkIdent `hc):ident, ↓reduceIte, ite_true, ite_false,
      Bool.false_eq_true, fold_store] at $(mkIdent `hy):ident ⊢)))
  else
    let some info := Lean.Meta.Match.Extension.getMatcherInfo? env e.getAppFn.constName! | throwError "csplit"
    let d := e.getArg! (info.numParams + 1)
    let g ← getMainGoal
    let (_, g) ← g.generalize #[{ expr := d, xName? := `x, hName? := `hd }]
    replaceMainGoal [g]
    evalTactic (← `(tactic| cases $(mkIdent `x):ident <;> (try simp only [$(mkIdent `hd):ident, fold_store] at $(mkIdent `hy):ident ⊢)))

set_option hygiene false in
/-- One raised bill, matched with the lower one (in `hy`). -/
macro "bill_step" : tactic => `(tactic| (
  bill_case
  rw [hb] at hlim
  rcases e1 with _ | e1 <;> first
  | (simp only [hb, Option.map_some, Option.isSome_some, ite_true] at hy
     subst hy
     left
     exact ⟨e1, rfl, applyCharges_error _ _ (by rw [hb])⟩)
  | (rw [applyCharges_relax_of (by dsimp only at *; omega) (by dsimp only at *; omega) hb]
     simp only [hb, Option.map_none, Option.isSome_none, Bool.false_eq_true, ite_false, fold_store] at hy ⊢)))

set_option maxHeartbeats 8000000 in
theorem storageAux_rel (name : String) (before : HostStore NearState) (args : List Value) (p m : Nat)
    (hp : before.host.gas.prepaid ≤ p) (hm : before.host.gas.maxBurnt ≤ m) :
    StorageRel p m (prepareStorageCallAux name (relaxSt before p m) args) (prepareStorageCallAux name before args) := by
  generalize hy : prepareStorageCallAux name before args = y
  unfold prepareStorageCallAux at hy ⊢
  simp only [Id.run, pure, relaxSt, getMemOrReg_relaxHost, recordedStorageError_relax, fold_acc,
    relax_storage, relax_storageAccounting, relax_storageProofSize, relax_storageReadsFromTrie, relax_storageKeys, relax_iterators, relax_nextIteratorId, relax_registers, relax_context, relax_subsidizedAmount, relax_returnData, relax_logs, relax_promiseResults, relax_promises, relax_gasWeights, relax_returnedPromise, relax_yieldResumes, relax_actionHash, relax_existingYields, relax_config, relax_randomSeed, relax_gasProfile, relax_extCosts, relax_fees, relax_outputDataReceivers, relax_lastError, relax_lastExecutionIssue, relax_yieldCreateToken, relax_crypto, relax_registerWrite, relax_storageLog, relax_actionProfile] at hy ⊢
  simp only [fold_store]
  repeat' (first
    | (subst hy; right; rfl)
    | (bill_step; try relax_norm; try simp only [fold_store] at *)
    | (csplit; try relax_norm; try simp only [fold_store] at *))

/-- `prepareStorageCall` under raised limits: a failed bill, or the same
result with the limits raised. -/
theorem prepareStorageCall_relax (name : String) (before : HostStore NearState) (args : List Value) (p m : Nat)
    (hp : before.host.gas.prepaid ≤ p) (hm : before.host.gas.maxBurnt ≤ m) :
    (∃ e, (prepareStorageCall name before args).2 = some (.hostError e) ∧ isGasError e) ∨
      prepareStorageCall name (relaxSt before p m) args =
        (relaxSt (prepareStorageCall name before args).1 p m, (prepareStorageCall name before args).2) := by
  rcases storageAux_rel name before args p m hp hm with ⟨e, he, hg⟩ | hr
  · exact Or.inl ⟨e, he, hg⟩
  · right
    unfold prepareStorageCall
    rw [hr]
    rfl

theorem prepareStorageCall_limits (name : String) (before : HostStore NearState) (args : List Value) :
    (prepareStorageCall name before args).1.host.gas.prepaid = before.host.gas.prepaid ∧
      (prepareStorageCall name before args).1.host.gas.maxBurnt = before.host.gas.maxBurnt := ⟨rfl, rfl⟩

/-- The call of a storage host respects raised limits when its functional
part commutes with raising them and keeps them. -/
theorem invokeRelax_storage (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hfn : ∀ st args p m, fn.invoke (relaxSt st p m) args = (fn.invoke st args).relax p m)
    (hkeep : ∀ st args vals st2, fn.invoke st args = .Return vals st2 →
      st2.host.gas.prepaid = st.host.gas.prepaid ∧ st2.host.gas.maxBurnt = st.host.gas.maxBurnt) :
    InvokeRelax extra name fn := by
  intro st args p m hp hm
  have hl := prepareStorageCall_limits name st args
  rcases prepareStorageCall_relax name st args p m hp hm with ⟨e, he, hg⟩ | hr
  · left
    refine ⟨(prepareStorageCall name st args).1, e, ?_, hg⟩
    simp only [invokeStorageCall]
    rw [he]
  · simp only [invokeStorageCall]
    rw [hr]
    generalize prepareStorageCall name st args = r at hl ⊢
    obtain ⟨after, err⟩ := r
    simp only at hl ⊢
    cases err with
    | none =>
      simp only
      rw [hfn]
      exact finishMeteredCall_relax extra name after args _ p m fun vals st2 h => by
        obtain ⟨h1, h2⟩ := hkeep after args vals st2 h
        exact ⟨by rw [h1, hl.1]; exact hp, by rw [h2, hl.2]; exact hm⟩
    | some err =>
      right
      cases err <;> rfl

end NearLogic
