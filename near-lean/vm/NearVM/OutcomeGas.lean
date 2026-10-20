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
  ⟨Nat.le_refl _, h.1.trans h.2.1, h.2.2⟩

theorem checkReceipts_gas_bounded (outcome : VMOutcome) (balance usage : Nat) (storage : List (Bytes × Bytes))
    (prepaid maxBurnt : Nat) (h : outcome.GasBounded prepaid maxBurnt) :
    (outcome.checkReceipts balance usage storage).GasBounded prepaid maxBurnt := by
  unfold VMOutcome.checkReceipts
  split
  · exact h
  · exact graphIssue_gas_bounded _ _ _ _ _ _ h

/-- Packing a failed, successful or invalid-graph result retains the gas bounds. -/
theorem outcomeOfExecution_gas_bounded (ctx : VMContext) (storage : List (Bytes × Bytes))
    (final : SmallStep.Config NearState) (error : Option FunctionCallError) (prepaid maxBurnt : Nat)
    (h : final.store.wasm.host.gas.burnt ≤ final.store.wasm.host.gas.used ∧
      final.store.wasm.host.gas.used ≤ prepaid ∧ final.store.wasm.host.gas.burnt ≤ maxBurnt) :
    (outcomeOfExecution ctx storage final error).GasBounded prepaid maxBurnt := by
  unfold outcomeOfExecution
  dsimp only
  split
  · exact ⟨Nat.le_refl _, h.1.trans h.2.1, h.2.2⟩
  · split
    · exact graphIssue_gas_bounded _ _ _ _ _ _ h
    · split
      · exact graphIssue_gas_bounded _ _ _ _ _ _ h
      · exact h

/-- Entry charging establishes counter bounds before either its error exit or
metered execution. Concrete imported hosts preserve the supplied limits. -/
theorem runInitialized_gas_bounded (cfg : WasmConfig) (fuel : Nat) (config : SmallStep.Config NearState)
    (prepaid maxBurnt : Nat) (hlimits : ConfigHostInvariant (GasLimits prepaid maxBurnt) config) :
    let gas := (runInitialized cfg fuel config).1.store.wasm.host.gas
    gas.burnt ≤ gas.used ∧ gas.used ≤ prepaid ∧ gas.burnt ≤ maxBurnt := by
  let cost := match config.expr with
    | .running thread => activationGas cfg.regularOpCost thread.locals
    | _ => 0
  unfold runInitialized
  dsimp only
  cases hc : chargeWasm config cost with
  | mk paid error =>
    have hp := chargeWasm_hostInvariant (P := GasLimits prepaid maxBurnt)
      (by
        intro current n h
        have hl := chargeWasm_gas_limits current n
        exact ⟨hl.1.trans h.1, hl.2.trans h.2⟩) config cost hlimits
    have hb := chargeWasm_gas_bounded config cost
    rw [hc] at hp hb
    cases error with
    | some error =>
      exact ⟨Nat.le_add_right _ _, hb.2.trans (Nat.le_of_eq hp.2.1),
        hb.1.trans (Nat.le_of_eq hp.2.2)⟩
    | none =>
      have hfinal := runMetered_fixed_budget cfg fuel paid prepaid maxBurnt hp hb
      exact ⟨Nat.le_add_right _ _, hfinal.2, hfinal.1⟩

/-- Contract loading preserves the original limits and establishes bounded gas. -/
theorem loading_gas_bounds (cfg : RuntimeConfig) (ctx : VMContext) (storage : List (Bytes × Bytes))
    (codeSize : Nat) (host : NearState) (error : Option HostError)
    (hload : applyCharges (ctx.toNearState cfg storage)
      [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"] = (host, error)) :
    GasLimits ctx.prepaidGas (ctx.gasBurnLimit cfg) host ∧ host.gas.Bounded := by
  have hl := applyCharges_gas_limits (ctx.toNearState cfg storage)
    [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"]
  have hb := applyCharges_gas_bounded (ctx.toNearState cfg storage)
    [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"]
    (VMContext.toNearState_gas_bounded ctx cfg storage)
  rw [hload] at hl hb
  exact ⟨hl, hb⟩

/-- Every raw VM attempt fits the call's budgets. No assumption about the
contract, its outcome, imported-host behavior or interpreter fuel is required. -/
theorem runAttempt_gas_bounded (cfg : RuntimeConfig) (code : Module) (codeSize : Nat) (method : String)
    (ctx : VMContext) (storage : List (Bytes × Bytes)) (fuel : Nat) :
    (runAttempt cfg code codeSize method ctx storage fuel).GasBounded ctx.prepaidGas (ctx.gasBurnLimit cfg) := by
  unfold runAttempt
  dsimp only
  split
  · exact failedBefore_gas_bounded _ _ _ _ _ _ _ (Nat.zero_le _) (Nat.zero_le _)
  · cases hload : applyCharges (ctx.toNearState cfg storage)
      [.ext "contract_loading_bytes" codeSize, .ext "contract_loading_base"] with
    | mk host loadError =>
      have hg := loading_gas_bounds cfg ctx storage codeSize host loadError hload
      have hp : host.gas.burnt ≤ ctx.prepaidGas :=
        (Nat.le_add_right _ _).trans (hg.2.2.trans (Nat.le_of_eq hg.1.1))
      have hm : host.gas.burnt ≤ ctx.gasBurnLimit cfg := hg.2.1.trans (Nat.le_of_eq hg.1.2)
      dsimp only
      cases loadError with
      | some error => exact failedBefore_gas_bounded _ _ _ _ _ _ _ hp hm
      | none =>
        dsimp only
        have hmp : (if cfg.wasm.fixContractLoadingCost then host.gas.burnt else 0) ≤ ctx.prepaidGas := by
          split
          · exact hp
          · exact Nat.zero_le _
        have hmm : (if cfg.wasm.fixContractLoadingCost then host.gas.burnt else 0) ≤ ctx.gasBurnLimit cfg := by
          split
          · exact hm
          · exact Nat.zero_le _
        cases hexport : code.findExport method with
        | none => exact failedBefore_gas_bounded _ _ _ _ _ _ _ hmp hmm
        | some entry =>
          dsimp only
          cases hsig : code.funcSig? entry with
          | none => exact failedBefore_gas_bounded _ _ _ _ _ _ _ hmp hmm
          | some signature =>
            dsimp only
            split
            · exact failedBefore_gas_bounded _ _ _ _ _ _ _ hmp hmm
            · cases hresolve : resolveMetered cfg code with
              | error message => exact failedBefore_gas_bounded _ _ _ _ _ _ _ hp hm
              | ok env =>
                dsimp only
                split
                · exact failedBefore_gas_bounded _ _ _ _ _ _ _ hp hm
                · rename_i config hinit
                  have hl := initResolvedConfig_gasLimits hresolve hinit
                  have hlim : ConfigHostInvariant (GasLimits ctx.prepaidGas (ctx.gasBurnLimit cfg)) config := by
                    simpa only [hg.1.1, hg.1.2] using hl
                  have hf := runInitialized_gas_bounded cfg.wasm fuel config _ _ hlim
                  exact outcomeOfExecution_gas_bounded _ _ _ _ _ _ hf

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
  exact h.1.trans h.2.1

end Wasm.Near
