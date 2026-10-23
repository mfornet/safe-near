import NearVM.ExecutionGas

namespace Wasm.Near

/-- The per-call burn limit, including a view call's explicit limit. -/
def VMContext.gasBurnLimit (ctx : VMContext) (cfg : RuntimeConfig) : Nat :=
  match ctx.viewConfig with
  | some view => view.maxGasBurnt
  | none => cfg.wasm.limits.maxGasBurnt

/-- Gas observations exposed to the receipt layer. -/
def VMOutcome.GasBounded (prepaid maxBurnt : Nat) (outcome : VMOutcome) : Prop :=
  outcome.burntGas ≤ outcome.usedGas ∧ outcome.usedGas ≤ prepaid ∧ outcome.burntGas ≤ maxBurnt

theorem failedBefore_gas_bounded (ctx : VMContext) (storage : List (Bytes × Bytes))
    (burnt : Nat) (error : FunctionCallError) (profile : GasProfile) (prepaid maxBurnt : Nat)
    (hp : burnt ≤ prepaid) (hm : burnt ≤ maxBurnt) :
    (VMOutcome.failedBefore ctx storage burnt error profile).GasBounded prepaid maxBurnt :=
  ⟨Nat.le_refl _, hp, hm⟩

theorem graphIssue_gas_bounded (outcome : VMOutcome) (balance usage : Nat) (storage : List (Bytes × Bytes))
    (prepaid maxBurnt : Nat) (h : outcome.GasBounded prepaid maxBurnt) :
    (outcome.graphIssue balance usage storage).GasBounded prepaid maxBurnt :=
  ⟨Nat.le_refl _, Nat.le_trans h.1 h.2.1, h.2.2⟩

theorem checkReceipts_gas_bounded (outcome : VMOutcome) (balance usage : Nat) (storage : List (Bytes × Bytes))
    (prepaid maxBurnt : Nat) (h : outcome.GasBounded prepaid maxBurnt) :
    (outcome.checkReceipts balance usage storage).GasBounded prepaid maxBurnt := by
  unfold VMOutcome.checkReceipts
  split
  · exact h
  · exact graphIssue_gas_bounded _ _ _ _ _ _ h

/-- Packing a failed, successful or invalid-graph result retains the gas bounds. -/
theorem outcomeOfExecution_gas_bounded (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : Machine) (error : Option FunctionCallError) (prepaid maxBurnt : Nat)
    (hctx : ctx.prepaidGas ≤ prepaid)
    (h : final.host.gas.burnt ≤ final.host.gas.used ∧
      final.host.gas.used ≤ prepaid ∧ final.host.gas.burnt ≤ maxBurnt) :
    (outcomeOfExecution ctx storage final error).GasBounded prepaid maxBurnt := by
  unfold outcomeOfExecution
  dsimp only
  split
  · exact ⟨Nat.le_refl _, Nat.le_trans h.1 h.2.1, h.2.2⟩
  · split
    · exact graphIssue_gas_bounded _ _ _ _ _ _ h
    · split
      · exact graphIssue_gas_bounded _ _ _ _ _ _ h
      · rename_i graph _ _ _ _
        have := distributeGas_le (ctx.prepaidGas - final.host.gas.used) graph.handles final.host.gasWeights
          graph.receipts
        refine ⟨?_, ?_, h.2.2⟩ <;> dsimp only <;> omega

/-- Entry charging establishes counter bounds before either its error exit or
metered execution. Concrete imported hosts preserve the supplied limits. -/
theorem runInitialized_gas_bounded (cfg : WasmConfig) (fuel : Nat) (m : Machine)
    (prepaid maxBurnt : Nat) (hlimits : MachineHostInvariant (GasLimits prepaid maxBurnt) m) :
    let gas := (runInitialized cfg fuel m).1.host.gas
    gas.burnt ≤ gas.used ∧ gas.used ≤ prepaid ∧ gas.burnt ≤ maxBurnt := by
  unfold runInitialized
  dsimp only
  have hp := chargeWasm_hostInvariant (P := GasLimits prepaid maxBurnt)
    (by
      intro current n h
      have hl := chargeHost_gas_limits current n
      exact ⟨Eq.trans hl.1 h.1, Eq.trans hl.2 h.2⟩) m (entryCost cfg m) hlimits
  have hb := chargeWasm_gas_bounded m (entryCost cfg m)
  split
  · exact ⟨Nat.le_add_right _ _, Nat.le_trans hb.2 (Nat.le_of_eq hp.host.1),
      Nat.le_trans hb.1 (Nat.le_of_eq hp.host.2)⟩
  · have hfinal := runMetered_fixed_budget cfg fuel _ prepaid maxBurnt hp hb
    exact ⟨Nat.le_add_right _ _, hfinal.2, hfinal.1⟩

/-- Contract loading preserves the original limits and establishes bounded gas. -/
theorem loading_gas_bounds (cfg : RuntimeConfig) (ctx : VMContext) (storage : List (Bytes × Bytes))
    (codeSize : Nat) (host : NearState) (error : Option HostError)
    (hload : applyCharges (ctx.toNearState cfg storage) (loadingCharges codeSize) = (host, error)) :
    GasLimits ctx.prepaidGas (ctx.gasBurnLimit cfg) host ∧ host.gas.Bounded := by
  have hl := applyCharges_gas_limits (ctx.toNearState cfg storage) (loadingCharges codeSize)
  have hb := applyCharges_gas_bounded (ctx.toNearState cfg storage) (loadingCharges codeSize)
    (VMContext.toNearState_gas_bounded ctx cfg storage)
  rw [hload] at hl hb
  exact ⟨hl, hb⟩

/-- Every raw VM attempt fits the call's budgets. No assumption about the
contract, its outcome, imported-host behavior or interpreter fuel is required. -/
theorem runAttempt_gas_bounded (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (runAttempt cfg code codeSize method ctx storage fuel).GasBounded ctx.prepaidGas (ctx.gasBurnLimit cfg) := by
  rcases runAttempt_cases cfg code codeSize method ctx storage fuel with
    ⟨host1, loadErr, burnt, e, profile, hload, hburnt, heq⟩ |
    ⟨host1, env, store, imports, valid, store', inst, entry, c, hload, hresolve, halloc, hinst,
      hstart, heq⟩
  · rw [heq]
    have hg := loading_gas_bounds cfg ctx storage codeSize host1 loadErr hload
    have hp : host1.gas.burnt ≤ ctx.prepaidGas :=
      Nat.le_trans (Nat.le_add_right _ _) (Nat.le_trans hg.2.2 (Nat.le_of_eq hg.1.1))
    have hm : host1.gas.burnt ≤ ctx.gasBurnLimit cfg := Nat.le_trans hg.2.1 (Nat.le_of_eq hg.1.2)
    exact failedBefore_gas_bounded _ _ _ _ _ _ _ (Nat.le_trans hburnt hp) (Nat.le_trans hburnt hm)
  · rw [heq]
    have hg := loading_gas_bounds cfg ctx storage codeSize host1 none hload
    have hl := resolvedStart_gasLimits hresolve halloc hinst hstart
    have hlim : MachineHostInvariant (GasLimits ctx.prepaidGas (ctx.gasBurnLimit cfg)) (.next c) := by
      show ConfigHostInvariant _ c
      rw [← hg.1.1, ← hg.1.2]
      exact hl
    have hf := runInitialized_gas_bounded cfg.wasm fuel (.next c) _ _ hlim
    exact outcomeOfExecution_gas_bounded _ _ _ _ _ _ (Nat.le_refl _) hf

/-- The public VM result exposes bounded burnt/used gas on success, protocol
failure and explicit model issues, including the graph-validation boundary. -/
theorem run_gas_bounded (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (run cfg code codeSize method ctx storage fuel).GasBounded ctx.prepaidGas (ctx.gasBurnLimit cfg) :=
  checkReceipts_gas_bounded _ _ _ _ _ _ (runAttempt_gas_bounded cfg code codeSize method ctx storage fuel)

/-- Direct budget facts for receipt and contract proofs. -/
theorem run_burntGas_le_usedGas (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (run cfg code codeSize method ctx storage fuel).burntGas ≤
      (run cfg code codeSize method ctx storage fuel).usedGas :=
  (run_gas_bounded cfg code codeSize method ctx storage fuel).1

theorem run_usedGas_le_prepaid (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (run cfg code codeSize method ctx storage fuel).usedGas ≤ ctx.prepaidGas :=
  (run_gas_bounded cfg code codeSize method ctx storage fuel).2.1

theorem run_burntGas_le_prepaid (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (run cfg code codeSize method ctx storage fuel).burntGas ≤ ctx.prepaidGas := by
  have h := run_gas_bounded cfg code codeSize method ctx storage fuel
  exact Nat.le_trans h.1 h.2.1

/-! ## Distributed gas

The gas a call itself uses, `usedGas - distributedGas`, is at least its burnt
gas: distribution only adds unused prepaid gas on top. -/

def VMOutcome.DistributionBounded (o : VMOutcome) : Prop :=
  o.burntGas + o.distributedGas ≤ o.usedGas

theorem graphIssue_distributionBounded (outcome : VMOutcome) (balance usage : Nat)
    (storage : List (Bytes × Bytes)) : (outcome.graphIssue balance usage storage).DistributionBounded := by
  simp [VMOutcome.DistributionBounded, VMOutcome.graphIssue]

theorem checkReceipts_distributionBounded (outcome : VMOutcome) (balance usage : Nat)
    (storage : List (Bytes × Bytes)) (h : outcome.DistributionBounded) :
    (outcome.checkReceipts balance usage storage).DistributionBounded := by
  unfold VMOutcome.checkReceipts
  split
  · exact h
  · exact graphIssue_distributionBounded _ _ _ _

theorem outcomeOfExecution_distributionBounded (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : Machine) (error : Option FunctionCallError)
    (h : final.host.gas.burnt ≤ final.host.gas.used) :
    (outcomeOfExecution ctx storage final error).DistributionBounded := by
  unfold outcomeOfExecution
  dsimp only
  split
  · simp [VMOutcome.DistributionBounded]
  · split
    · exact graphIssue_distributionBounded _ _ _ _
    · split
      · exact graphIssue_distributionBounded _ _ _ _
      · simp only [VMOutcome.DistributionBounded]
        omega

theorem runAttempt_distributionBounded (cfg : RuntimeConfig) (code : Module) (codeSize : Nat)
    (method : String) (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (runAttempt cfg code codeSize method ctx storage fuel).DistributionBounded := by
  rcases runAttempt_cases cfg code codeSize method ctx storage fuel with
    ⟨host1, loadErr, burnt, e, profile, hload, hburnt, heq⟩ |
    ⟨host1, env, store, imports, valid, store', inst, entry, c, hload, hresolve, halloc, hinst,
      hstart, heq⟩
  · rw [heq]
    simp [VMOutcome.DistributionBounded, VMOutcome.failedBefore]
  · rw [heq]
    have hg := loading_gas_bounds cfg ctx storage codeSize host1 none hload
    have hl := resolvedStart_gasLimits hresolve halloc hinst hstart
    have hlim : MachineHostInvariant (GasLimits ctx.prepaidGas (ctx.gasBurnLimit cfg)) (.next c) := by
      show ConfigHostInvariant _ c
      rw [← hg.1.1, ← hg.1.2]
      exact hl
    have hf := runInitialized_gas_bounded cfg.wasm fuel (.next c) _ _ hlim
    exact outcomeOfExecution_distributionBounded _ _ _ _ hf.1

theorem run_distributionBounded (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (run cfg code codeSize method ctx storage fuel).DistributionBounded :=
  checkReceipts_distributionBounded _ _ _ _ (runAttempt_distributionBounded cfg code codeSize method ctx storage fuel)

end Wasm.Near
