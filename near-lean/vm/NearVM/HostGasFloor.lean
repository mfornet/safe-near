import NearVM.HostGasLimits

/-!
# Host functions never lower burnt gas

Every host function a resolved module can call keeps the counter's burnt gas
at or above where it was, within the call's fixed limits. With the per-step
facts of `NearVM.Fuel`, this is what lets gas bound how long a call runs. The
proof follows `HostGasLimits` host by host: every gas change is a charge.
-/

namespace Wasm.Near

/-- Burnt gas is at least `b`, within the fixed limits `prepaid` and `maxBurnt`. -/
def GasFloor (b prepaid maxBurnt : Nat) (ns : NearState) : Prop :=
  ns.gas.Floor b prepaid maxBurnt

def HostPreservesGasFloor (fn : NearHostFn NearState) : Prop :=
  ∀ b prepaid maxBurnt, NearHostFn.Preserves (GasFloor b prepaid maxBurnt) fn

theorem HostPreservesGas.floor {fn : NearHostFn NearState} (h : HostPreservesGas fn) :
    HostPreservesGasFloor fn := by
  intro b prepaid maxBurnt st args hwf
  have hg := h st args
  cases hr : fn.invoke st args <;> rw [hr] at hg <;>
    dsimp only [HostResult.Satisfies] at hg ⊢ <;> simpa only [GasFloor, hg] using hwf

variable {b prepaid maxBurnt : Nat}

theorem applyCharges_gasFloor (ns : NearState) (charges : List Charge)
    (h : GasFloor b prepaid maxBurnt ns) : GasFloor b prepaid maxBurnt (applyCharges ns charges).1 :=
  applyCharges_floor ns charges h

theorem gasFn_gasFloor : HostPreservesGasFloor gasFn := by
  intro b prepaid maxBurnt st args hwf
  unfold gasFn
  dsimp only
  split
  · rename_i n
    have hl := GasCounter.deduct_floor n.toNat n.toNat hwf
    split <;> exact hl
  · exact hwf

theorem updateStorageUsage_gasFloor (extra : Nat) (name : String) (before after : HostStore NearState)
    (args : List Value) (hwf : GasFloor b prepaid maxBurnt after.host) :
    GasFloor b prepaid maxBurnt (updateStorageUsage extra name before after args).host := by
  unfold updateStorageUsage
  repeat (first | exact hwf | (dsimp only; split))
  all_goals first | exact hwf | (split <;> exact hwf)

theorem deductDeposit_gasFloor (name : String) (before after : HostStore NearState) (args : List Value)
    (hwf : GasFloor b prepaid maxBurnt after.host) : GasFloor b prepaid maxBurnt (deductDeposit name before after args).1.host := by
  unfold deductDeposit promiseDeposit? deductPromiseDeposit
  repeat (first | exact hwf | (dsimp only; split))
  all_goals first | exact hwf | (split <;> exact hwf)

theorem finishMeteredCall_gasFloor (extra : Nat) (name : String) (before : HostStore NearState)
    (args : List Value) (result : HostResult NearState) (hwf : HostResult.Satisfies (GasFloor b prepaid maxBurnt) result) :
    HostResult.Satisfies (GasFloor b prepaid maxBurnt) (finishMeteredCall extra name before args result) := by
  cases result with
  | Trap st msg => exact hwf
  | Return vals st =>
    unfold finishMeteredCall
    dsimp only
    cases hc : applyCharges st.host (chargesAfter name before st args) with
    | mk ns error =>
      dsimp only
      have hns := applyCharges_gasFloor st.host (chargesAfter name before st args) hwf
      rw [hc] at hns
      cases error with
      | some error => exact hns
      | none =>
        cases hd : deductDeposit name before { st with host := ns } args with
        | mk final error =>
          dsimp only
          have hfinal := deductDeposit_gasFloor name before { st with host := ns } args hns
          rw [hd] at hfinal
          cases error with
          | some error => exact hfinal
          | none =>
            cases he : actionMethodEncodingError name before args with
            | some error => exact hfinal
            | none => exact updateStorageUsage_gasFloor extra name before final args hfinal

theorem metered_preserves_gasFloor (extra : Nat) (name : String) (fn : NearHostFn NearState)
    (hfn : HostPreservesGasFloor fn) : HostPreservesGasFloor (metered extra name fn) := by
  intro b prepaid maxBurnt st args hwf
  unfold metered
  dsimp only
  split
  · exact hwf
  · split
    · change GasFloor b prepaid maxBurnt (applyCharges st.host _).1
      exact applyCharges_gasFloor _ _ hwf
    · let ns := (applyCharges st.host (chargesBefore name st args)).1
      let st1 : HostStore NearState := { st with
        host := { ns with context := { ns.context with usedGas := UInt64.ofNat ns.gas.used } } }
      have hwf1 : GasFloor b prepaid maxBurnt st1.host := by
        change GasFloor b prepaid maxBurnt (applyCharges st.host _).1
        exact applyCharges_gasFloor _ _ hwf
      cases herr : (applyCharges st.host (chargesBefore name st args)).2 with
      | some error => exact hwf1
      | none =>
        cases hp : preInvokeError name st1 args with
        | some error => exact hwf1
        | none =>
          unfold invokeStorageCall
          dsimp only
          let st2 := (prepareStorageCall name st1 args).1
          have hwf2 : GasFloor b prepaid maxBurnt st2.host := prepareStorageCall_floor name st1 args hwf1
          cases hs : (prepareStorageCall name st1 args).2 with
          | none => exact finishMeteredCall_gasFloor extra name st2 args _ (hfn b prepaid maxBurnt st2 args hwf2)
          | some error => cases error <;> exact hwf2

set_option maxRecDepth 16384 in
/-- Every published metered host keeps burnt gas at or above its floor. -/
theorem meteredHostFns_gasFloor (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostPreservesGasFloor entry.2 := by
  simp only [meteredHostFns, List.mem_append, List.mem_map, List.mem_singleton] at h
  rcases h with ⟨⟨decl, fn⟩, hin, heq⟩ | heq
  · subst entry
    simp only [nearHostFns, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals first
      | (intro b prepaid maxBurnt st args hwf; exact hwf)
      | apply metered_preserves_gasFloor
    all_goals first
      | exact HostPreservesGas.floor inputFn_gas
      | exact HostPreservesGas.floor readRegisterFn_gas
      | exact HostPreservesGas.floor registerLenFn_gas
      | exact HostPreservesGas.floor writeRegisterFn_gas
      | exact HostPreservesGas.floor storageWriteFn_gas
      | exact HostPreservesGas.floor storageReadFn_gas
      | exact HostPreservesGas.floor storageRemoveFn_gas
      | exact HostPreservesGas.floor storageHasKeyFn_gas
      | exact HostPreservesGas.floor currentAccountIdFn_gas
      | exact HostPreservesGas.floor predecessorAccountIdFn_gas
      | exact HostPreservesGas.floor signerAccountIdFn_gas
      | exact HostPreservesGas.floor signerAccountPkFn_gas
      | exact HostPreservesGas.floor attachedDepositFn_gas
      | exact HostPreservesGas.floor blockIndexFn_gas
      | exact HostPreservesGas.floor blockTimestampFn_gas
      | exact HostPreservesGas.floor epochHeightFn_gas
      | exact HostPreservesGas.floor storageUsageFn_gas
      | exact HostPreservesGas.floor accountBalanceFn_gas
      | exact HostPreservesGas.floor accountLockedBalanceFn_gas
      | exact HostPreservesGas.floor prepaidGasFn_gas
      | exact HostPreservesGas.floor usedGasFn_gas
      | exact HostPreservesGas.floor randomSeedFn_gas
      | exact HostPreservesGas.floor logUtf8Fn_gas
      | exact HostPreservesGas.floor logUtf16Fn_gas
      | exact HostPreservesGas.floor panicMetered_gas
      | exact HostPreservesGas.floor panicUtf8Metered_gas
      | exact HostPreservesGas.floor abortMetered_gas
      | exact gasFn_gasFloor
      | exact HostPreservesGas.floor promiseCreateFn_gas
      | exact HostPreservesGas.floor promiseThenFn_gas
      | exact HostPreservesGas.floor promiseAndFn_gas
      | exact HostPreservesGas.floor promiseBatchCreateFn_gas
      | exact HostPreservesGas.floor promiseBatchThenFn_gas
      | exact HostPreservesGas.floor promiseBatchActionCreateAccountFn_gas
      | exact HostPreservesGas.floor promiseBatchActionDeployContractFn_gas
      | exact HostPreservesGas.floor promiseBatchActionFunctionCallFn_gas
      | exact HostPreservesGas.floor promiseBatchActionFunctionCallWeightFn_gas
      | exact HostPreservesGas.floor promiseBatchActionTransferFn_gas
      | exact HostPreservesGas.floor promiseBatchActionStakeFn_gas
      | exact HostPreservesGas.floor promiseBatchActionAddKeyWithFullAccessFn_gas
      | exact HostPreservesGas.floor promiseBatchActionAddKeyWithFunctionCallFn_gas
      | exact HostPreservesGas.floor promiseBatchActionDeleteKeyFn_gas
      | exact HostPreservesGas.floor promiseBatchActionDeleteAccountFn_gas
      | exact HostPreservesGas.floor valueReturnFn_gas
      | exact HostPreservesGas.floor promiseReturnFn_gas
      | exact HostPreservesGas.floor promiseResultsCountFn_gas
      | exact HostPreservesGas.floor promiseResultFn_gas
  · subst entry
    exact gasFn_gasFloor

/-- Resolution cannot introduce a function outside the proved host registry. -/
theorem resolveMeteredImports_gasFloor (cfg : RuntimeConfig) (imports : List ImportDecl)
    (env : HostEnv NearState) (h : resolveMeteredImports cfg imports = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesGasFloor fn := by
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
        · exact meteredHostFns_gasFloor cfg (found, candidate) (List.mem_of_find?_eq_some hf)
        · exact ih tail hr candidate hc

theorem resolveMetered_gasFloor (cfg : RuntimeConfig) (m : Module) (env : HostEnv NearState)
    (h : resolveMetered cfg m = .ok env) :
    ∀ fn ∈ env.funcs, HostPreservesGasFloor fn :=
  resolveMeteredImports_gasFloor cfg m.importDecls env h

end Wasm.Near
