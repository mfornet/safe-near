import Bridge.Methods.FtBalanceOfProviderAdequacy
import Bridge.Methods.FtBalanceOfCopiedRun
import Bridge.Functions.BalanceOf297DeployedParser

/-! Actual-code parser providers, whole-method resource composition and receipt refinement.
The general provider and model-budget obligations remain explicit. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

noncomputable def providerMethodCost (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (parseGas outF : Nat) (e : NearState) : Nat :=
  11 * cfg.wasm.regularOpCost + providerBodyCost cfg.wasm e (inputHost e 0) S a parseGas outF

theorem provider_body_cost_erase (cfg : WasmConfig) (e : NearState) (S : WNear.State) (a : WNear.AccountId)
    (parseGas outF : Nat) :
    providerBodyCost cfg (erase e) (inputHost (erase e) 0) S a parseGas outF =
      providerBodyCost cfg e (inputHost e 0) S a parseGas outF := rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_absent_runs (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (bs : List UInt8) (parseGas outF : Nat) (st : Near.TrieOverlay.State) (bud : Nat)
    (hlen : bs.length < 2 ^ 24) (hpos : 0 < bs.length)
    (hProvider : DeployedParserProvider cfg bs a parseGas outF)
     :
    MethodRunsR cfg 297 (CopiedAbsentPre S a bs st bud) (providerMethodCost cfg S a parseGas outF) (copiedMethodPost a st) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 297)) (entryCost cfg.wasm (.next (startW cfg h 297))) =
      (.next { startW cfg h 297 with store := wStore cfg (charged h (11 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_297, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [providerMethodCost] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1)
      (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have hp : CopiedAbsentPre S a bs st bud (charged h (11 * cfg.wasm.regularOpCost)) :=
    ⟨hpre.input, hpre.inputLimit, hpre.value, hpre.accounting, hpre.keyLimit, hpre.canonical,
      hpre.link, hpre.proof, hpre.budget, hpre.accountLimit, hpre.absent, hpre.registerLimit, hpre.returnLimit⟩
  have hbody : (charged h (11 * cfg.wasm.regularOpCost)).gas.used +
      providerBodyCost cfg.wasm (charged h (11 * cfg.wasm.regularOpCost))
        (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) S a parseGas outF ≤ Cg := by
    rw [charged_gas_used, ← provider_body_cost_erase, erase_charged]
    simp only [providerMethodCost] at hcost
    omega
  have had := provider_absent_adequate cfg Cg a bs parseGas outF hlen hpos
    (charged h (11 * cfg.wasm.regularOpCost)) (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0)
    hp.input rfl hp.inputLimit S st hp.value hp.accounting hp.keyLimit hp.canonical hp.link bud hp.proof
    hp.budget hp.accountLimit hp.absent hp.registerLimit hp.returnLimit hbody
    (by simpa [charged] using hC1) (by simpa [charged] using hC2) (hProvider _)
  rw [← startW_thread297 cfg h] at had
  have hending := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := FtTotalSupplyMethod.runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hending
  obtain ⟨rfl, cs, hcs, hlk⟩ := hending
  have hrun := FtTotalSupplyMethod.done_of_values (FtTotalSupplyMethod.runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h1, st1, h2, hs1, hs2, heq, hu⟩ := endCells297_ends hcs hlk
  have heinput : erase (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) = erase (inputHost (erase h) 0) :=
    erase_inputHost (by rw [erase_charged, erase_erase]) 0
  have hs1' : StorageReadPost (inputHost (erase h) 0) WNear.stateKey 0 st h1 := by
    apply (storage_read_post_erase_source _ _ _ _ _).mp
    have hr := (storage_read_post_erase_source _ _ _ _ _).mpr hs1
    rwa [heinput] at hr
  exact ⟨σ.store, hrun, ⟨h1, st1, h2, hs1', hs2, heq⟩, hu⟩

end WNear.Binary.BalanceOf297AbsentCall
