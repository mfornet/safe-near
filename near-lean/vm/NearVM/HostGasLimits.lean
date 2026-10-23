import NearVM.HostGas
import NearVM.ExecutionPromises

namespace Wasm.Near

/-- Limits are fixed by call context, independently of burnt/reserved gas. -/
def GasLimits (prepaid maxBurnt : Nat) (ns : NearState) : Prop :=
  ns.gas.prepaid = prepaid ∧ ns.gas.maxBurnt = maxBurnt

def HostPreservesGasLimits (fn : NearHostFn NearState) : Prop :=
  ∀ prepaid maxBurnt, NearHostFn.Preserves (GasLimits prepaid maxBurnt) fn

theorem HostPreservesGas.limits {fn : NearHostFn NearState} (h : HostPreservesGas fn) :
    HostPreservesGasLimits fn := by
  intro prepaid maxBurnt st args hwf
  have hg := h st args
  cases hr : fn.invoke st args <;> rw [hr] at hg <;>
    dsimp only [HostResult.Satisfies] at hg ⊢ <;> simpa only [GasLimits, hg] using hwf

variable {prepaid maxBurnt : Nat}

theorem applyCharges_gasLimits (ns : NearState) (charges : List Charge)
    (h : GasLimits prepaid maxBurnt ns) : GasLimits prepaid maxBurnt (applyCharges ns charges).1 := by
  have hl := applyCharges_gas_limits ns charges
  exact ⟨hl.1.trans h.1, hl.2.trans h.2⟩

theorem gasFn_gasLimits : HostPreservesGasLimits gasFn := by
  intro prepaid maxBurnt st args hwf
  unfold gasFn
  dsimp only
  split
  · rename_i n
    have hl := GasCounter.deduct_limits st.host.gas n.toNat n.toNat
    split <;> exact ⟨hl.1.trans hwf.1, hl.2.trans hwf.2⟩
  · exact hwf

theorem updateStorageUsage_gasLimits (extra : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) (hwf : GasLimits prepaid maxBurnt after.host) :
    GasLimits prepaid maxBurnt (updateStorageUsage extra name before after args).host := by
  unfold updateStorageUsage
  repeat (first | exact hwf | (dsimp only; split))
  all_goals first | exact hwf | (split <;> exact hwf)

theorem deductDeposit_gasLimits (name : String) (before after : HostStore NearState) (args : List Value)
    (hwf : GasLimits prepaid maxBurnt after.host) : GasLimits prepaid maxBurnt (deductDeposit name before after args).1.host := by
  unfold deductDeposit promiseDeposit? deductPromiseDeposit
  repeat (first | exact hwf | (dsimp only; split))
  all_goals first | exact hwf | (split <;> exact hwf)

theorem finishMeteredCall_gasLimits (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (result : HostResult NearState) (hwf : HostResult.Satisfies (GasLimits prepaid maxBurnt) result) :
    HostResult.Satisfies (GasLimits prepaid maxBurnt) (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st msg => exact hwf
  | Return vals st =>
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk ns error =>
      dsimp only
      have hns := applyCharges_gasLimits st.host (chargesAfter name before st args) hwf
      rw [hc] at hns
      cases error with
      | some error => exact hns
      | none =>
        cases hd : deductDeposit name before { st with host := ns } args with
        | mk final error =>
          dsimp only
          have hfinal := deductDeposit_gasLimits name before { st with host := ns } args hns
          rw [hd] at hfinal
          cases error with
          | some error => exact hfinal
          | none =>
            cases he : actionMethodEncodingError name before args with
            | some error => exact hfinal
            | none => exact updateStorageUsage_gasLimits extra name before final args hfinal

theorem metered_preserves_gasLimits (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hfn : HostPreservesGasLimits fn) : HostPreservesGasLimits (metered extra name fn) := by
  intro prepaid maxBurnt st args hwf
  unfold metered
  dsimp only
  split
  · exact hwf
  · split
    · change GasLimits prepaid maxBurnt (applyCharges st.host _).1
      exact applyCharges_gasLimits _ _ hwf
    · let ns := (applyCharges st.host (chargesBefore name st args)).1
      let st1 : HostStore NearState := { st with
        host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }
      have hwf1 : GasLimits prepaid maxBurnt st1.host := by
        change GasLimits prepaid maxBurnt (applyCharges st.host _).1
        exact applyCharges_gasLimits _ _ hwf
      cases herr : (applyCharges st.host (chargesBefore name st args)).2 with
      | some error => exact hwf1
      | none =>
        cases hp : preInvokeError name st1 args with
        | some error => exact hwf1
        | none =>
          unfold invokeStorageCall
          dsimp only
          let st2 := (prepareStorageCall name st1 args).1
          have hwf2 : GasLimits prepaid maxBurnt st2.host := hwf1
          cases hs : (prepareStorageCall name st1 args).2 with
          | none => exact finishMeteredCall_gasLimits extra name st2 args _ (hfn prepaid maxBurnt st2 args hwf2)
          | some error => cases error <;> exact hwf2

set_option maxRecDepth 16384 in
/-- Every published metered host preserves call gas limits, including
unsupported/deprecated rejection paths and the explicit gas import. -/
theorem meteredHostFns_gasLimits (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostPreservesGasLimits entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals first
      | (intro prepaid maxBurnt st args hwf; exact hwf)
      | apply metered_preserves_gasLimits
    all_goals first
      | exact HostPreservesGas.limits inputFn_gas
      | exact HostPreservesGas.limits readRegisterFn_gas
      | exact HostPreservesGas.limits registerLenFn_gas
      | exact HostPreservesGas.limits writeRegisterFn_gas
      | exact HostPreservesGas.limits storageWriteFn_gas
      | exact HostPreservesGas.limits storageReadFn_gas
      | exact HostPreservesGas.limits storageRemoveFn_gas
      | exact HostPreservesGas.limits storageHasKeyFn_gas
      | exact HostPreservesGas.limits currentAccountIdFn_gas
      | exact HostPreservesGas.limits predecessorAccountIdFn_gas
      | exact HostPreservesGas.limits signerAccountIdFn_gas
      | exact HostPreservesGas.limits signerAccountPkFn_gas
      | exact HostPreservesGas.limits attachedDepositFn_gas
      | exact HostPreservesGas.limits blockIndexFn_gas
      | exact HostPreservesGas.limits blockTimestampFn_gas
      | exact HostPreservesGas.limits epochHeightFn_gas
      | exact HostPreservesGas.limits storageUsageFn_gas
      | exact HostPreservesGas.limits accountBalanceFn_gas
      | exact HostPreservesGas.limits accountLockedBalanceFn_gas
      | exact HostPreservesGas.limits prepaidGasFn_gas
      | exact HostPreservesGas.limits usedGasFn_gas
      | exact HostPreservesGas.limits randomSeedFn_gas
      | exact HostPreservesGas.limits logUtf8Fn_gas
      | exact HostPreservesGas.limits logUtf16Fn_gas
      | exact HostPreservesGas.limits panicMetered_gas
      | exact HostPreservesGas.limits panicUtf8Metered_gas
      | exact HostPreservesGas.limits abortMetered_gas
      | exact gasFn_gasLimits
      | exact HostPreservesGas.limits promiseCreateFn_gas
      | exact HostPreservesGas.limits promiseThenFn_gas
      | exact HostPreservesGas.limits promiseAndFn_gas
      | exact HostPreservesGas.limits promiseBatchCreateFn_gas
      | exact HostPreservesGas.limits promiseBatchThenFn_gas
      | exact HostPreservesGas.limits promiseBatchActionCreateAccountFn_gas
      | exact HostPreservesGas.limits promiseBatchActionDeployContractFn_gas
      | exact HostPreservesGas.limits promiseBatchActionFunctionCallFn_gas
      | exact HostPreservesGas.limits promiseBatchActionFunctionCallWeightFn_gas
      | exact HostPreservesGas.limits promiseBatchActionTransferFn_gas
      | exact HostPreservesGas.limits promiseBatchActionStakeFn_gas
      | exact HostPreservesGas.limits promiseBatchActionAddKeyWithFullAccessFn_gas
      | exact HostPreservesGas.limits promiseBatchActionAddKeyWithFunctionCallFn_gas
      | exact HostPreservesGas.limits promiseBatchActionDeleteKeyFn_gas
      | exact HostPreservesGas.limits promiseBatchActionDeleteAccountFn_gas
      | exact HostPreservesGas.limits valueReturnFn_gas
      | exact HostPreservesGas.limits promiseReturnFn_gas
      | exact HostPreservesGas.limits promiseResultsCountFn_gas
      | exact HostPreservesGas.limits promiseResultFn_gas
  · subst entry
    exact gasFn_gasLimits

/-- Resolution cannot introduce a function outside the proved host registry. -/
theorem resolveMeteredImports_gasLimits (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesGasLimits fn := by
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
        · exact meteredHostFns_gasLimits cfg (found, candidate) (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_gasLimits (cfg : RuntimeConfig) (m : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg m = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesGasLimits fn :=
  resolveMeteredImports_gasLimits cfg m.importDecls env h

end Wasm.Near
