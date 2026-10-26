import NearVM.Metered
import NearVM.Context
import NearVM.PromiseGraph
import NearVM.InterpreterInvariant

namespace Wasm.Near

/-- The host's recursive lookup has exactly the usual list-index semantics. -/
theorem getPromise_eq_getElem? (ps : List NearPromise) (index : Nat) :
    getPromise? ps index = ps[index]? := by
  induction ps generalizing index with
  | nil => rfl
  | cons p ps ih => cases index <;> simp [getPromise?, ih]

theorem promiseIndexValid_iff (st : HostStore NearState) (index : Nat) :
    promiseIndexValid st index = true ↔ index < st.host.promises.length := by
  simp [promiseIndexValid, getPromise_eq_getElem?]

theorem promiseDepsValid_iff (st : HostStore NearState) (dependencies : List Nat) :
    promiseDepsValid st dependencies = true ↔
      ∀ index ∈ dependencies, index < st.host.promises.length := by
  simp [promiseDepsValid, List.all_eq_true, promiseIndexValid_iff]

theorem promiseWellFormed_lookup {ps : List NearPromise} {start index : Nat} {p : NearPromise}
    (hwf : PromisesWellFormedFrom start ps) (hget : getPromise? ps index = some p) :
    PromiseWellFormedAt (start + index) p := by
  induction ps generalizing start index with
  | nil => simp [getPromise?] at hget
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [getPromise?, Option.some.injEq] at hget
      subst p
      exact hwf.1
    | succ index =>
      have htail : getPromise? tail index = some p := hget
      have he : start + 1 + index = start + (index + 1) := by omega
      simpa only [he] using ih hwf.2 htail

/-- Appending a new handle preserves all existing indices and requires its
references to be strictly earlier than its creation index. -/
theorem promisesWellFormed_snoc (ps : List NearPromise) (start : Nat) (p : NearPromise)
    (hwf : PromisesWellFormedFrom start ps) (hp : PromiseWellFormedAt (start + ps.length) p) :
    PromisesWellFormedFrom start (ps ++ [p]) := by
  induction ps generalizing start with
  | nil => exact ⟨hp, trivial⟩
  | cons head tail ih =>
    refine ⟨hwf.1, ih (start + 1) hwf.2 ?_⟩
    have he : start + (head :: tail).length = start + 1 + tail.length := by
      simp only [List.length_cons]
      omega
    simpa only [he] using hp

theorem setPromise_length {ps result : List NearPromise} {index : Nat} {p : NearPromise}
    (h : setPromise? ps index p = some result) : result.length = ps.length := by
  induction ps generalizing index result with
  | nil => simp [setPromise?] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [setPromise?, Option.some.injEq] at h
      subst result
      rfl
    | succ index =>
      obtain ⟨rest, hrest, he⟩ := Option.map_eq_some_iff.mp h
      subst result
      simp only [List.length_cons, ih hrest]

/-- Replacing one handle with a handle valid at the same index preserves the
whole dependency invariant. No other slot is renumbered. -/
theorem setPromise_preserves {ps result : List NearPromise} {start index : Nat} {p : NearPromise}
    (hwf : PromisesWellFormedFrom start ps) (hp : PromiseWellFormedAt (start + index) p)
    (h : setPromise? ps index p = some result) : PromisesWellFormedFrom start result := by
  induction ps generalizing start index result with
  | nil => simp [setPromise?] at h
  | cons head tail ih =>
    cases index with
    | zero =>
      simp only [setPromise?, Option.some.injEq] at h
      subst result
      exact ⟨hp, hwf.2⟩
    | succ index =>
      obtain ⟨rest, hrest, he⟩ := Option.map_eq_some_iff.mp h
      subst result
      refine ⟨hwf.1, ih hwf.2 ?_ hrest⟩
      have he : start + (index + 1) = start + 1 + index := by omega
      simpa only [he] using hp

/-- Appending an action changes neither the dependency structure nor handle
count, for both independent receipts and callbacks. -/
theorem appendPromiseAction_preserves {ps result : List NearPromise} {index start : Nat}
    {action : PromiseAction} (hwf : PromisesWellFormedFrom start ps)
    (h : appendPromiseAction? ps index action = some result) :
    PromisesWellFormedFrom start result ∧ result.length = ps.length := by
  unfold appendPromiseAction? at h
  cases lookup : getPromise? ps index with
  | none => simp [lookup] at h
  | some p =>
    cases p with
    | batch account actions =>
      simp only [lookup] at h
      exact ⟨setPromise_preserves (p := .batch account (actions ++ [action])) hwf trivial h, setPromise_length h⟩
    | callback base account actions =>
      simp only [lookup] at h
      have hbase := promiseWellFormed_lookup hwf lookup
      have hnew : PromiseWellFormedAt (start + index)
          (.callback base account (actions ++ [action])) := hbase
      exact ⟨setPromise_preserves hwf hnew h, setPromise_length h⟩
    | and dependencies => simp [lookup] at h
    | yielded account actions dataId =>
      simp only [lookup] at h
      exact ⟨setPromise_preserves (p := .yielded account (actions ++ [action]) dataId) hwf trivial h,
        setPromise_length h⟩

theorem appendPromise_preserves (st : HostStore NearState) (p : NearPromise)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hp : PromiseWellFormedAt st.host.promises.length p) :
    PromisesWellFormedFrom 0 (appendPromise st p).host.promises := by
  apply promisesWellFormed_snoc _ _ _ hwf
  simpa only [Nat.zero_add] using hp

theorem appendBatchPromise_preserves (st : HostStore NearState) (account : List UInt8)
    (actions : List PromiseAction) (hwf : PromisesWellFormedFrom 0 st.host.promises) :
    PromisesWellFormedFrom 0 (appendPromise st (.batch account actions)).host.promises :=
  appendPromise_preserves st _ hwf trivial

theorem appendCallbackPromise_preserves (st : HostStore NearState) (base : Nat) (account : List UInt8)
    (actions : List PromiseAction) (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hbase : promiseIndexValid st base = true) :
    PromisesWellFormedFrom 0 (appendPromise st (.callback base account actions)).host.promises :=
  appendPromise_preserves st _ hwf ((promiseIndexValid_iff st base).mp hbase)

theorem appendJointPromise_preserves (st : HostStore NearState) (dependencies : List Nat)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hdeps : promiseDepsValid st dependencies = true) :
    PromisesWellFormedFrom 0 (appendPromise st (.and dependencies)).host.promises :=
  appendPromise_preserves st _ hwf ((promiseDepsValid_iff st dependencies).mp hdeps)

/-- The invariant is preserved in every returned host store, including traps;
this is stronger than the condition needed by successful VM conversion. -/
def HostResultPromisesWellFormed :=
  HostResult.Satisfies (fun ns : NearState => PromisesWellFormedFrom 0 ns.promises)

def HostPreservesPromises :=
  NearHostFn.Preserves (fun ns : NearState => PromisesWellFormedFrom 0 ns.promises)

theorem checkAccountId_preserves_promises (name : String) (st : HostStore NearState)
    (account : List UInt8) (next : Unit → HostResult NearState)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hnext : HostResultPromisesWellFormed (next ())) :
    HostResultPromisesWellFormed (checkAccountId name st account next) := by
  unfold checkAccountId
  split
  · exact hnext
  · exact hwf

theorem checkPublicKey_preserves_promises (name : String) (st : HostStore NearState)
    (key : List UInt8) (next : Unit → HostResult NearState)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hnext : HostResultPromisesWellFormed (next ())) :
    HostResultPromisesWellFormed (checkPublicKey name st key next) := by
  unfold checkPublicKey
  split
  · exact hnext
  · exact hwf

theorem disallowInView_preserves_promises (name : String) (fn : NearHostFn NearState)
    (hfn : HostPreservesPromises fn) : HostPreservesPromises (disallowInView name fn) := by
  intro st args hwf
  unfold disallowInView
  dsimp only
  split
  · exact hwf
  · exact hfn st args hwf

theorem appendPromiseActionResult_preserves {weight : UInt64} (name : String) (st : HostStore NearState)
    (index : UInt64) (action : PromiseAction) (hwf : PromisesWellFormedFrom 0 st.host.promises) :
    HostResultPromisesWellFormed (appendPromiseActionResult name st index action weight) := by
  unfold appendPromiseActionResult
  cases h : appendPromiseAction? st.host.promises index.toNat action with
  | none =>
    exact hwf
  | some result =>
    exact (appendPromiseAction_preserves hwf h).1

theorem createBatchPromiseResult_preserves (name : String) (st : HostStore NearState)
    (account : List UInt8) (hwf : PromisesWellFormedFrom 0 st.host.promises) :
    HostResultPromisesWellFormed (createBatchPromiseResult name st account) := by
  unfold createBatchPromiseResult
  apply checkAccountId_preserves_promises _ _ _ _ hwf
  exact appendBatchPromise_preserves st account [] hwf

theorem createCallbackPromiseResult_preserves (name : String) (st : HostStore NearState)
    (base : UInt64) (account : List UInt8) (hwf : PromisesWellFormedFrom 0 st.host.promises) :
    HostResultPromisesWellFormed (createCallbackPromiseResult name st base account) := by
  unfold createCallbackPromiseResult
  split
  · rename_i hbase
    apply checkAccountId_preserves_promises _ _ _ _ hwf
    exact appendCallbackPromise_preserves st base.toNat account [] hwf hbase
  · exact hwf

theorem appendJointPromise_find_preserves (st : HostStore NearState) (dependencies : List Nat)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hfind : dependencies.find? (fun index => !promiseIndexValid st index) = none) :
    PromisesWellFormedFrom 0 (appendPromise st (.and dependencies)).host.promises := by
  apply appendJointPromise_preserves _ _ hwf
  simpa [promiseDepsValid, List.all_eq_true] using hfind

/-- Close each branch of a promise host from `hwf`. -/
local macro "promise_preserves_tac" hwf:ident : tactic => `(tactic| (
    dsimp only
    repeat (first
      | exact $hwf
      | exact appendBatchPromise_preserves _ _ _ $hwf
      | exact appendCallbackPromise_preserves _ _ _ _ $hwf (by assumption)
      | exact appendJointPromise_find_preserves _ _ $hwf (by assumption)
      | exact appendPromiseActionResult_preserves _ _ _ _ $hwf
      | exact createBatchPromiseResult_preserves _ _ _ $hwf
      | exact createCallbackPromiseResult_preserves _ _ _ _ $hwf
      | apply checkAccountId_preserves_promises _ _ _ _ $hwf
      | apply checkPublicKey_preserves_promises _ _ _ _ $hwf
      | split)))

theorem promiseCreateFn_preserves : HostPreservesPromises promiseCreateFn := by
  unfold promiseCreateFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseThenFn_preserves : HostPreservesPromises promiseThenFn := by
  unfold promiseThenFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseAndFn_preserves : HostPreservesPromises promiseAndFn := by
  unfold promiseAndFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchCreateFn_preserves : HostPreservesPromises promiseBatchCreateFn := by
  unfold promiseBatchCreateFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchThenFn_preserves : HostPreservesPromises promiseBatchThenFn := by
  unfold promiseBatchThenFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionCreateAccountFn_preserves : HostPreservesPromises promiseBatchActionCreateAccountFn := by
  unfold promiseBatchActionCreateAccountFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionDeployContractFn_preserves : HostPreservesPromises promiseBatchActionDeployContractFn := by
  unfold promiseBatchActionDeployContractFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionFunctionCallFn_preserves : HostPreservesPromises promiseBatchActionFunctionCallFn := by
  unfold promiseBatchActionFunctionCallFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionFunctionCallWeightFn_preserves : HostPreservesPromises promiseBatchActionFunctionCallWeightFn := by
  unfold promiseBatchActionFunctionCallWeightFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionTransferFn_preserves : HostPreservesPromises promiseBatchActionTransferFn := by
  unfold promiseBatchActionTransferFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionStakeFn_preserves : HostPreservesPromises promiseBatchActionStakeFn := by
  unfold promiseBatchActionStakeFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionAddKeyWithFullAccessFn_preserves : HostPreservesPromises promiseBatchActionAddKeyWithFullAccessFn := by
  unfold promiseBatchActionAddKeyWithFullAccessFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionAddKeyWithFunctionCallFn_preserves : HostPreservesPromises promiseBatchActionAddKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddKeyWithFunctionCallFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionDeleteKeyFn_preserves : HostPreservesPromises promiseBatchActionDeleteKeyFn := by
  unfold promiseBatchActionDeleteKeyFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionDeleteAccountFn_preserves : HostPreservesPromises promiseBatchActionDeleteAccountFn := by
  unfold promiseBatchActionDeleteAccountFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionUseGlobalContractFn_preserves : HostPreservesPromises promiseBatchActionUseGlobalContractFn := by
  unfold promiseBatchActionUseGlobalContractFn useGlobalContractFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionUseGlobalContractByAccountIdFn_preserves : HostPreservesPromises promiseBatchActionUseGlobalContractByAccountIdFn := by
  unfold promiseBatchActionUseGlobalContractByAccountIdFn useGlobalContractFn
  apply disallowInView_preserves_promises
  intro st args hwf
  promise_preserves_tac hwf

theorem promiseBatchActionTransferToGasKeyFn_preserves : HostPreservesPromises promiseBatchActionTransferToGasKeyFn := by
  unfold promiseBatchActionTransferToGasKeyFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendBatchPromise_preserves _ _ _ hwf
    | exact appendCallbackPromise_preserves _ _ _ _ hwf (by assumption)
    | exact appendJointPromise_find_preserves _ _ hwf (by assumption)
    | exact appendPromiseActionResult_preserves _ _ _ _ hwf
    | exact createBatchPromiseResult_preserves _ _ _ hwf
    | exact createCallbackPromiseResult_preserves _ _ _ _ hwf
    | apply checkAccountId_preserves_promises _ _ _ _ hwf
    | apply checkPublicKey_preserves_promises _ _ _ _ hwf
    | split)

theorem promiseBatchActionAddGasKeyWithFullAccessFn_preserves : HostPreservesPromises promiseBatchActionAddGasKeyWithFullAccessFn := by
  unfold promiseBatchActionAddGasKeyWithFullAccessFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendBatchPromise_preserves _ _ _ hwf
    | exact appendCallbackPromise_preserves _ _ _ _ hwf (by assumption)
    | exact appendJointPromise_find_preserves _ _ hwf (by assumption)
    | exact appendPromiseActionResult_preserves _ _ _ _ hwf
    | exact createBatchPromiseResult_preserves _ _ _ hwf
    | exact createCallbackPromiseResult_preserves _ _ _ _ hwf
    | apply checkAccountId_preserves_promises _ _ _ _ hwf
    | apply checkPublicKey_preserves_promises _ _ _ _ hwf
    | split)

theorem promiseBatchActionAddGasKeyWithFunctionCallFn_preserves : HostPreservesPromises promiseBatchActionAddGasKeyWithFunctionCallFn := by
  unfold promiseBatchActionAddGasKeyWithFunctionCallFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendBatchPromise_preserves _ _ _ hwf
    | exact appendCallbackPromise_preserves _ _ _ _ hwf (by assumption)
    | exact appendJointPromise_find_preserves _ _ hwf (by assumption)
    | exact appendPromiseActionResult_preserves _ _ _ _ hwf
    | exact createBatchPromiseResult_preserves _ _ _ hwf
    | exact createCallbackPromiseResult_preserves _ _ _ _ hwf
    | apply checkAccountId_preserves_promises _ _ _ _ hwf
    | apply checkPublicKey_preserves_promises _ _ _ _ hwf
    | split)

theorem promiseBatchActionDeployGlobalContractFn_preserves : HostPreservesPromises promiseBatchActionDeployGlobalContractFn := by
  unfold promiseBatchActionDeployGlobalContractFn deployGlobalContractFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendBatchPromise_preserves _ _ _ hwf
    | exact appendCallbackPromise_preserves _ _ _ _ hwf (by assumption)
    | exact appendJointPromise_find_preserves _ _ hwf (by assumption)
    | exact appendPromiseActionResult_preserves _ _ _ _ hwf
    | exact createBatchPromiseResult_preserves _ _ _ hwf
    | exact createCallbackPromiseResult_preserves _ _ _ _ hwf
    | apply checkAccountId_preserves_promises _ _ _ _ hwf
    | apply checkPublicKey_preserves_promises _ _ _ _ hwf
    | split)

theorem promiseBatchActionDeployGlobalContractByAccountIdFn_preserves : HostPreservesPromises promiseBatchActionDeployGlobalContractByAccountIdFn := by
  unfold promiseBatchActionDeployGlobalContractByAccountIdFn deployGlobalContractFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact appendBatchPromise_preserves _ _ _ hwf
    | exact appendCallbackPromise_preserves _ _ _ _ hwf (by assumption)
    | exact appendJointPromise_find_preserves _ _ hwf (by assumption)
    | exact appendPromiseActionResult_preserves _ _ _ _ hwf
    | exact createBatchPromiseResult_preserves _ _ _ hwf
    | exact createCallbackPromiseResult_preserves _ _ _ _ hwf
    | apply checkAccountId_preserves_promises _ _ _ _ hwf
    | apply checkPublicKey_preserves_promises _ _ _ _ hwf
    | split)

/-- Gas accounting, including exhaustion, does not mutate promise handles. -/
theorem applyCharge_promises (ns : NearState) (charge : Charge) :
    (applyCharge ns charge).1.promises = ns.promises := by
  cases charge <;> rfl

theorem applyCharges_promises (ns : NearState) (charges : List Charge) :
    (applyCharges ns charges).1.promises = ns.promises := by
  induction charges generalizing ns with
  | nil => rfl
  | cons charge charges ih =>
    cases hc : applyCharge ns charge with
    | mk next error =>
      have hp := applyCharge_promises ns charge
      rw [hc] at hp
      cases error with
      | none => simpa only [applyCharges, hc] using (ih next).trans hp
      | some error => simpa only [applyCharges, hc] using hp

theorem updateStorageUsage_promises (extra : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) : (updateStorageUsage extra name before after args).host.promises = after.host.promises := by
  unfold updateStorageUsage
  repeat (first | rfl | (dsimp only; split))
  all_goals first | rfl | (split <;> rfl)

theorem deductDeposit_promises (name : String) (before after : HostStore NearState) (args : List Value) :
    (deductDeposit name before after args).1.host.promises = after.host.promises := by
  unfold deductDeposit promiseDeposit? deductPromiseDeposit
  repeat (first | rfl | (dsimp only; split))
  all_goals first | rfl | (split <;> rfl)

theorem finishMeteredCall_preserves (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (result : HostResult NearState) (hwf : HostResultPromisesWellFormed result) :
    HostResultPromisesWellFormed (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st msg => exact hwf
  | Return vals st =>
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk ns error =>
      dsimp only
      have hp := applyCharges_promises st.host (chargesAfter name before st args)
      rw [hc] at hp
      have hns : PromisesWellFormedFrom 0 ns.promises := by
        rw [hp]
        exact hwf
      cases error with
      | some error => exact hns
      | none =>
        cases hd : deductDeposit name before { st with host := ns } args with
        | mk final error =>
          dsimp only
          have hp := deductDeposit_promises name before { st with host := ns } args
          rw [hd] at hp
          have hfinal : PromisesWellFormedFrom 0 final.host.promises := by
            rw [hp]
            exact hns
          cases error with
          | some error => exact hfinal
          | none =>
            cases he : actionMethodEncodingError name before args with
            | some error => exact hfinal
            | none =>
              change PromisesWellFormedFrom 0 (updateStorageUsage extra name before final args).host.promises
              rw [updateStorageUsage_promises]
              exact hfinal

/-- Metering preserves the host invariant even if charging, deposit deduction
or storage accounting turns a successful host call into a trap. -/
theorem metered_preserves_promises (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hfn : HostPreservesPromises fn) : HostPreservesPromises (metered extra name fn) := by
  intro st args hwf
  unfold metered
  dsimp only
  split
  · exact hwf
  · split
    · change PromisesWellFormedFrom 0 (applyCharges st.host _).1.promises
      rw [applyCharges_promises]
      exact hwf
    · let ns := (applyCharges st.host (chargesBefore name st args)).1
      let st1 : HostStore NearState := { st with
        host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }
      have hwf1 : PromisesWellFormedFrom 0 st1.host.promises := by
        change PromisesWellFormedFrom 0 (applyCharges st.host _).1.promises
        rw [applyCharges_promises]
        exact hwf
      cases herr : (applyCharges st.host (chargesBefore name st args)).2 with
      | some error => exact hwf1
      | none =>
        cases hp : preInvokeError name st1 args with
        | some error => exact hwf1
        | none =>
          unfold invokeStorageCall
          dsimp only
          let st2 := (prepareStorageCall name st1 args).1
          have hwf2 : PromisesWellFormedFrom 0 st2.host.promises := hwf1
          cases hs : (prepareStorageCall name st1 args).2 with
          | none => exact finishMeteredCall_preserves extra name st2 args _ (hfn st2 args hwf2)
          | some error => cases error <;> exact hwf2

/-- A successful preserving host call leaves a graph the executable converter
accepts, with validity proved before the output boundary check. -/
theorem HostPreservesPromises.convertible {fn : NearHostFn NearState}
    (hfn : HostPreservesPromises fn) (st after : HostStore NearState) (args vals : List Value)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hreturn : fn.invoke st args = .Return vals after) :
    ∃ graph, convertPromises after.host.promises = some graph ∧ graph.Valid := by
  have hafter := hfn st args hwf
  rw [hreturn] at hafter
  obtain ⟨graph, converts⟩ := convertPromises_total after.host.promises hafter
  exact ⟨graph, converts, convertPromises_valid converts⟩

theorem metered_promiseCreateFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseCreateFn) :=
  metered_preserves_promises extra name promiseCreateFn promiseCreateFn_preserves

theorem metered_promiseThenFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseThenFn) :=
  metered_preserves_promises extra name promiseThenFn promiseThenFn_preserves

theorem metered_promiseAndFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseAndFn) :=
  metered_preserves_promises extra name promiseAndFn promiseAndFn_preserves

theorem metered_promiseBatchCreateFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchCreateFn) :=
  metered_preserves_promises extra name promiseBatchCreateFn promiseBatchCreateFn_preserves

theorem metered_promiseBatchThenFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchThenFn) :=
  metered_preserves_promises extra name promiseBatchThenFn promiseBatchThenFn_preserves

theorem metered_promiseBatchActionCreateAccountFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionCreateAccountFn) :=
  metered_preserves_promises extra name promiseBatchActionCreateAccountFn promiseBatchActionCreateAccountFn_preserves

theorem metered_promiseBatchActionDeployContractFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionDeployContractFn) :=
  metered_preserves_promises extra name promiseBatchActionDeployContractFn promiseBatchActionDeployContractFn_preserves

theorem metered_promiseBatchActionFunctionCallFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionFunctionCallFn) :=
  metered_preserves_promises extra name promiseBatchActionFunctionCallFn promiseBatchActionFunctionCallFn_preserves

theorem metered_promiseBatchActionFunctionCallWeightFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionFunctionCallWeightFn) :=
  metered_preserves_promises extra name promiseBatchActionFunctionCallWeightFn promiseBatchActionFunctionCallWeightFn_preserves

theorem metered_promiseBatchActionTransferFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionTransferFn) :=
  metered_preserves_promises extra name promiseBatchActionTransferFn promiseBatchActionTransferFn_preserves

theorem metered_promiseBatchActionStakeFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionStakeFn) :=
  metered_preserves_promises extra name promiseBatchActionStakeFn promiseBatchActionStakeFn_preserves

theorem metered_promiseBatchActionAddKeyWithFullAccessFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionAddKeyWithFullAccessFn) :=
  metered_preserves_promises extra name promiseBatchActionAddKeyWithFullAccessFn promiseBatchActionAddKeyWithFullAccessFn_preserves

theorem metered_promiseBatchActionAddKeyWithFunctionCallFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionAddKeyWithFunctionCallFn) :=
  metered_preserves_promises extra name promiseBatchActionAddKeyWithFunctionCallFn promiseBatchActionAddKeyWithFunctionCallFn_preserves

theorem metered_promiseBatchActionDeleteKeyFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionDeleteKeyFn) :=
  metered_preserves_promises extra name promiseBatchActionDeleteKeyFn promiseBatchActionDeleteKeyFn_preserves

theorem metered_promiseBatchActionDeleteAccountFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionDeleteAccountFn) :=
  metered_preserves_promises extra name promiseBatchActionDeleteAccountFn promiseBatchActionDeleteAccountFn_preserves

theorem metered_promiseBatchActionUseGlobalContractFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionUseGlobalContractFn) :=
  metered_preserves_promises extra name promiseBatchActionUseGlobalContractFn promiseBatchActionUseGlobalContractFn_preserves

theorem metered_promiseBatchActionUseGlobalContractByAccountIdFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionUseGlobalContractByAccountIdFn) :=
  metered_preserves_promises extra name promiseBatchActionUseGlobalContractByAccountIdFn promiseBatchActionUseGlobalContractByAccountIdFn_preserves

theorem metered_promiseBatchActionTransferToGasKeyFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionTransferToGasKeyFn) :=
  metered_preserves_promises extra name promiseBatchActionTransferToGasKeyFn promiseBatchActionTransferToGasKeyFn_preserves

theorem metered_promiseBatchActionAddGasKeyWithFullAccessFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionAddGasKeyWithFullAccessFn) :=
  metered_preserves_promises extra name promiseBatchActionAddGasKeyWithFullAccessFn promiseBatchActionAddGasKeyWithFullAccessFn_preserves

theorem metered_promiseBatchActionAddGasKeyWithFunctionCallFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionAddGasKeyWithFunctionCallFn) :=
  metered_preserves_promises extra name promiseBatchActionAddGasKeyWithFunctionCallFn promiseBatchActionAddGasKeyWithFunctionCallFn_preserves

theorem metered_promiseBatchActionDeployGlobalContractFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionDeployGlobalContractFn) :=
  metered_preserves_promises extra name promiseBatchActionDeployGlobalContractFn promiseBatchActionDeployGlobalContractFn_preserves

theorem metered_promiseBatchActionDeployGlobalContractByAccountIdFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseBatchActionDeployGlobalContractByAccountIdFn) :=
  metered_preserves_promises extra name promiseBatchActionDeployGlobalContractByAccountIdFn promiseBatchActionDeployGlobalContractByAccountIdFn_preserves

theorem checkDataLimit_preserves_promises (name label : String) (limit : Option Nat) (size : Nat)
    (st : HostStore NearState) (next : Unit → HostResult NearState)
    (hwf : PromisesWellFormedFrom 0 st.host.promises)
    (hnext : HostResultPromisesWellFormed (next ())) {error : Option (Nat → Nat → HostError)} :
    HostResultPromisesWellFormed (checkDataLimit name label limit size st next error) := by
  unfold checkDataLimit
  split
  · exact hnext
  · split <;> exact hwf

theorem checkedSetRegister_promises {st after : HostStore NearState} {register : UInt64}
    {bytes : List UInt8} (h : checkedSetRegister? st register bytes = some after) :
    after.host.promises = st.host.promises := by
  unfold checkedSetRegister? at h
  split at h
  · cases h
    rfl
  · split at h
    · cases h
      rfl
    · cases h

theorem writeRegisterResult_preserves (name : String) (st : HostStore NearState) (register : UInt64)
    (bytes : List UInt8) (vals : List Value) (hwf : PromisesWellFormedFrom 0 st.host.promises) :
    HostResultPromisesWellFormed (writeRegisterResult name st register bytes vals) := by
  unfold writeRegisterResult
  cases h : checkedSetRegister? st register bytes with
  | none => exact hwf
  | some after =>
    change PromisesWellFormedFrom 0 after.host.promises
    rw [checkedSetRegister_promises h]
    exact hwf

theorem chainIdFn_preserves : HostPreservesPromises chainIdFn := by
  intro st args hwf
  unfold chainIdFn contextRegisterFn
  dsimp only
  split
  · exact writeRegisterResult_preserves _ _ _ _ _ hwf
  · exact hwf

theorem promiseYieldCreateFn_preserves : HostPreservesPromises promiseYieldCreateFn := by
  unfold promiseYieldCreateFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first | exact hwf | split)
  all_goals first
    | trivial
    | exact appendPromise_preserves _ _ (by rw [checkedSetRegister_promises ‹_›]; exact hwf) trivial

theorem promiseYieldResumeFn_preserves : HostPreservesPromises promiseYieldResumeFn := by
  unfold promiseYieldResumeFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | split)

theorem valueReturnFn_preserves : HostPreservesPromises valueReturnFn := by
  intro st args hwf
  unfold valueReturnFn
  dsimp only
  repeat (first
    | exact hwf
    | apply checkDataLimit_preserves_promises _ _ _ _ _ _ hwf
    | split)

theorem promiseReturnFn_preserves : HostPreservesPromises promiseReturnFn := by
  unfold promiseReturnFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first | exact hwf | split)

theorem promiseResultsCountFn_preserves : HostPreservesPromises promiseResultsCountFn := by
  intro st args hwf
  unfold promiseResultsCountFn
  dsimp only
  split <;> exact hwf

theorem promiseResultFn_preserves : HostPreservesPromises promiseResultFn := by
  unfold promiseResultFn
  apply disallowInView_preserves_promises
  intro st args hwf
  dsimp only
  repeat (first
    | exact hwf
    | exact writeRegisterResult_preserves _ _ _ _ _ hwf
    | split)

theorem metered_valueReturnFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name valueReturnFn) :=
  metered_preserves_promises extra name valueReturnFn valueReturnFn_preserves

theorem metered_promiseReturnFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseReturnFn) :=
  metered_preserves_promises extra name promiseReturnFn promiseReturnFn_preserves

theorem metered_promiseResultsCountFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseResultsCountFn) :=
  metered_preserves_promises extra name promiseResultsCountFn promiseResultsCountFn_preserves

theorem metered_promiseResultFn_preserves (extra : Nat) (name : String) :
    HostPreservesPromises (metered extra name promiseResultFn) :=
  metered_preserves_promises extra name promiseResultFn promiseResultFn_preserves

/-- The actual VM initialization starts inside the preserved invariant. -/
theorem toNearState_promises_wellFormed (cfg : RuntimeConfig) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) :
    PromisesWellFormedFrom 0 (ctx.toNearState cfg storage).promises := by
  trivial

end Wasm.Near
