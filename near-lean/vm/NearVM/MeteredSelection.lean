import NearVM.HostSelection

namespace Wasm.Near

theorem applyCharge_returnedPromise (ns : NearState) (charge : Charge) :
    (applyCharge ns charge).1.returnedPromise = ns.returnedPromise := by
  cases charge <;> rfl

theorem applyCharges_returnedPromise (ns : NearState) (charges : List Charge) :
    (applyCharges ns charges).1.returnedPromise = ns.returnedPromise := by
  induction charges generalizing ns with
  | nil => rfl
  | cons charge charges ih =>
    cases hc : applyCharge ns charge with
    | mk next error =>
      have hp := applyCharge_returnedPromise ns charge
      rw [hc] at hp
      cases error with
      | none => simpa only [applyCharges, hc] using (ih next).trans hp
      | some error => simpa only [applyCharges, hc] using hp

theorem applyCharges_selection (ns : NearState) (charges : List Charge)
    (hwf : ReturnSelectionValid ns) : ReturnSelectionValid (applyCharges ns charges).1 :=
  ReturnSelectionValid.of_fields (applyCharges_promises ns charges) (applyCharges_returnedPromise ns charges) hwf

theorem updateStorageUsage_selection (extra : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) (hwf : ReturnSelectionValid after.host) :
    ReturnSelectionValid (updateStorageUsage extra name before after args).host := by
  unfold updateStorageUsage
  repeat (first | exact hwf | (dsimp only; split))
  all_goals first | exact hwf | (split <;> exact hwf)

theorem deductDeposit_selection (name : String) (before after : HostStore NearState) (args : List Value)
    (hwf : ReturnSelectionValid after.host) : ReturnSelectionValid (deductDeposit name before after args).1.host := by
  unfold deductDeposit promiseDeposit? deductPromiseDeposit
  repeat (first | exact hwf | (dsimp only; split))
  all_goals first | exact hwf | (split <;> exact hwf)

theorem finishMeteredCall_selection (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (result : HostResult NearState) (hwf : HostResultSelectionValid result) :
    HostResultSelectionValid (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st msg => exact hwf
  | Return vals st =>
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk ns error =>
      dsimp only
      have hns := applyCharges_selection st.host (chargesAfter name before st args) hwf
      rw [hc] at hns
      cases error with
      | some error => exact hns
      | none =>
        cases hd : deductDeposit name before { st with host := ns } args with
        | mk final error =>
          dsimp only
          have hfinal := deductDeposit_selection name before { st with host := ns } args hns
          rw [hd] at hfinal
          cases error with
          | some error => exact hfinal
          | none =>
            cases he : actionMethodEncodingError name before args with
            | some error => exact hfinal
            | none => exact updateStorageUsage_selection extra name before final args hfinal

theorem metered_preserves_selection (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hfn : HostPreservesSelection fn) : HostPreservesSelection (metered extra name fn) := by
  intro st args hwf
  unfold metered
  dsimp only
  split
  · exact hwf
  · split
    · change ReturnSelectionValid (applyCharges st.host _).1
      exact applyCharges_selection _ _ hwf
    · let ns := (applyCharges st.host (chargesBefore name st args)).1
      let st1 : HostStore NearState := { st with
        host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }
      have hwf1 : ReturnSelectionValid st1.host := by
        change ReturnSelectionValid (applyCharges st.host _).1
        exact applyCharges_selection _ _ hwf
      cases herr : (applyCharges st.host (chargesBefore name st args)).2 with
      | some error => exact hwf1
      | none =>
        cases hp : preInvokeError name st1 args with
        | some error => exact hwf1
        | none =>
          unfold invokeStorageCall
          dsimp only
          let st2 := (prepareStorageCall name st1 args).1
          have hwf2 : ReturnSelectionValid st2.host := hwf1
          cases hs : (prepareStorageCall name st1 args).2 with
          | none => exact finishMeteredCall_selection extra name st2 args _ (hfn st2 args hwf2)
          | some error => cases error <;> exact hwf2

set_option maxRecDepth 16384 in
/-- Every function published by the runtime's metered registry preserves
creation-order validity, including rejected unsupported and deprecated calls. -/
theorem meteredHostFns_selection (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostPreservesSelection entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals first
      | (intro st args hwf; exact hwf)
      | apply metered_preserves_selection
    all_goals first
      | exact inputFn_selection
      | exact readRegisterFn_selection
      | exact registerLenFn_selection
      | exact writeRegisterFn_selection
      | exact storageWriteFn_selection
      | exact storageReadFn_selection
      | exact storageRemoveFn_selection
      | exact storageHasKeyFn_selection
      | exact currentAccountIdFn_selection
      | exact predecessorAccountIdFn_selection
      | exact signerAccountIdFn_selection
      | exact signerAccountPkFn_selection
      | exact attachedDepositFn_selection
      | exact blockIndexFn_selection
      | exact blockTimestampFn_selection
      | exact epochHeightFn_selection
      | exact storageUsageFn_selection
      | exact accountBalanceFn_selection
      | exact accountLockedBalanceFn_selection
      | exact prepaidGasFn_selection
      | exact usedGasFn_selection
      | exact randomSeedFn_selection
      | exact logUtf8Fn_selection
      | exact logUtf16Fn_selection
      | exact panicMetered_selection
      | exact panicUtf8Metered_selection
      | exact abortMetered_selection
      | exact gasFn_selection
      | exact promiseCreateFn_selection
      | exact promiseThenFn_selection
      | exact promiseAndFn_selection
      | exact promiseBatchCreateFn_selection
      | exact promiseBatchThenFn_selection
      | exact promiseBatchActionCreateAccountFn_selection
      | exact promiseBatchActionDeployContractFn_selection
      | exact promiseBatchActionFunctionCallFn_selection
      | exact promiseBatchActionTransferFn_selection
      | exact promiseBatchActionStakeFn_selection
      | exact promiseBatchActionAddKeyWithFullAccessFn_selection
      | exact promiseBatchActionAddKeyWithFunctionCallFn_selection
      | exact promiseBatchActionDeleteKeyFn_selection
      | exact promiseBatchActionDeleteAccountFn_selection
      | exact valueReturnFn_selection
      | exact promiseReturnFn_selection
      | exact promiseResultsCountFn_selection
      | exact promiseResultFn_selection
  · subst entry
    exact gasFn_selection

/-- Resolution cannot introduce a function outside the proved host registry. -/
theorem resolveMeteredImports_selection (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesSelection fn := by
  induction imports generalizing env with
  | nil =>
    simp only [resolveMeteredImports, Except.ok.injEq] at h
    subst env
    simp
  | cons decl rest ih =>
    cases hf : (meteredHostFns cfg).find? (fun p => importMatches p.fst decl) with
    | none => simp [resolveMeteredImports, hf] at h
    | some entry =>
      obtain ⟨found, fn⟩ := entry
      cases hr : resolveMeteredImports cfg rest with
      | error message => simp [resolveMeteredImports, hf, hr] at h
      | ok tail =>
        simp only [resolveMeteredImports, hf, hr, Except.ok.injEq] at h
        subst env
        intro candidate hc
        simp only [List.mem_cons] at hc
        rcases hc with rfl | hc
        · exact meteredHostFns_selection cfg (found, candidate) (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_selection (cfg : RuntimeConfig) (m : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg m = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesSelection fn :=
  resolveMeteredImports_selection cfg m.importDecls env h

end Wasm.Near
