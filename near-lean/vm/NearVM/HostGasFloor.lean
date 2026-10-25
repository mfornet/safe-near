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

theorem gasFn_gasFloor (opCost : Nat) : HostPreservesGasFloor (gasFn opCost) := by
  intro b prepaid maxBurnt st args hwf
  unfold gasFn
  dsimp only
  split
  · rename_i n
    have hl := GasCounter.deduct_floor (n.toNat * opCost) (n.toNat * opCost) hwf
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
          | some error => split <;> first | exact hwf2 | contradiction

/-- Every published metered host keeps burnt gas at or above its floor. -/
theorem meteredHostFns_gasFloor (cfg : RuntimeConfig) (entry : ImportDecl × NearHostFn NearState)
    (h : entry ∈ meteredHostFns cfg) : HostPreservesGasFloor entry.2 := by
  revert entry h
  simp only [meteredHostFns, List.forall_mem_append, List.forall_mem_map, List.forall_mem_singleton]
  refine ⟨?_, gasFn_gasFloor _⟩
  simp only [nearHostFns, List.forall_mem_cons]
  and_intros
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor inputFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor readRegisterFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor registerLenFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor writeRegisterFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor valueReturnFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor storageWriteFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor storageReadFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor storageRemoveFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor storageHasKeyFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor panicMetered_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor panicUtf8Metered_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor currentAccountIdFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor predecessorAccountIdFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor signerAccountIdFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor attachedDepositFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor logUtf8Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor sha256Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor keccak256Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor signerAccountPkFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor blockIndexFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor blockIndexFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor blockTimestampFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor epochHeightFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor storageUsageFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor accountBalanceFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor accountLockedBalanceFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor prepaidGasFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor usedGasFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor validatorStakeFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor validatorTotalStakeFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor logUtf16Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor abortMetered_gas
  · intro b prepaid maxBurnt st args hwf; exact hwf -- storage_iter_prefix
  · intro b prepaid maxBurnt st args hwf; exact hwf -- storage_iter_range
  · intro b prepaid maxBurnt st args hwf; exact hwf -- storage_iter_next
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor keccak512Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor ripemd160Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor ecrecoverFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor ed25519VerifyFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor p256VerifyFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor randomSeedFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor altBn128G1MultiexpFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor altBn128G1SumFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor altBn128PairingCheckFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381G1MultiexpFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381G2MultiexpFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381MapFpToG1Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381MapFp2ToG2Fn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381P1DecompressFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381P2DecompressFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381P1SumFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381P2SumFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor bls12381PairingCheckFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseCreateFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseThenFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseAndFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchCreateFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchThenFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionCreateAccountFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionDeployContractFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionFunctionCallFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionFunctionCallWeightFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionTransferFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionStakeFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionAddKeyWithFullAccessFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionAddKeyWithFunctionCallFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionDeleteKeyFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionDeleteAccountFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionDeployGlobalContractFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionDeployGlobalContractByAccountIdFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionUseGlobalContractFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionUseGlobalContractByAccountIdFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseYieldCreateFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseYieldResumeFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseResultsCountFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseResultFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseReturnFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionTransferToGasKeyFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionAddGasKeyWithFullAccessFn_gas
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor promiseBatchActionAddGasKeyWithFunctionCallFn_gas
  · apply metered_preserves_gasFloor; intro b prepaid maxBurnt st args hwf; exact hwf -- promise_yield_create_with_id
  · apply metered_preserves_gasFloor; intro b prepaid maxBurnt st args hwf; exact hwf -- promise_yield_resume_with_yield_id
  · apply metered_preserves_gasFloor; intro b prepaid maxBurnt st args hwf; exact hwf -- promise_set_refund_to
  · apply metered_preserves_gasFloor; intro b prepaid maxBurnt st args hwf; exact hwf -- promise_batch_action_state_init_by_account_id
  · apply metered_preserves_gasFloor; exact HostPreservesGas.floor chainIdFn_gas
  · simp

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
