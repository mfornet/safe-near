import Bridge.Methods.FtBalanceOfObjectAdequacy
import Bridge.Methods.FtBalanceOfCopiedRun

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open SerdeRead ParseStr
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

noncomputable def objectMethodCost (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (N : Nat) (e : NearState) : Nat :=
  11 * cfg.wasm.regularOpCost + objectBodyCost cfg.wasm e (inputHost e 0) S a bs rest N

theorem object_body_cost_erase (cfg : WasmConfig) (e : NearState) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (N : Nat) :
    objectBodyCost cfg (erase e) (inputHost (erase e) 0) S a bs rest N =
      objectBodyCost cfg e (inputHost e 0) S a bs rest N := rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_absent_runs (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (N : Nat) (st : Near.TrieOverlay.State) (bud : Nat)
    (hlen : bs.length < 2 ^ 24) (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
     :
    MethodRunsR cfg 297 (CopiedAbsentPre S a bs st bud) (objectMethodCost cfg S a bs rest N) (copiedMethodPost a st) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 297)) (entryCost cfg.wasm (.next (startW cfg h 297))) =
      (.next { startW cfg h 297 with store := wStore cfg (charged h (11 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_297, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [objectMethodCost] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1)
      (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have hp : CopiedAbsentPre S a bs st bud (charged h (11 * cfg.wasm.regularOpCost)) :=
    ⟨hpre.input, hpre.inputLimit, hpre.value, hpre.accounting, hpre.keyLimit, hpre.canonical,
      hpre.link, hpre.proof, hpre.budget, hpre.accountLimit, hpre.absent, hpre.registerLimit, hpre.returnLimit⟩
  have hbody : (charged h (11 * cfg.wasm.regularOpCost)).gas.used +
      objectBodyCost cfg.wasm (charged h (11 * cfg.wasm.regularOpCost))
        (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) S a bs rest N ≤ Cg := by
    rw [charged_gas_used, ← object_body_cost_erase, erase_charged]
    simp only [objectMethodCost] at hcost
    omega
  have had := object_absent_adequate cfg Cg a bs rest N hlen hnb ho hloop hend
    (charged h (11 * cfg.wasm.regularOpCost)) (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0)
    hp.input rfl hp.inputLimit S st hp.value hp.accounting hp.keyLimit hp.canonical hp.link bud hp.proof
    hp.budget hp.accountLimit hp.absent hp.registerLimit hp.returnLimit hbody
    (by simpa [charged] using hC1) (by simpa [charged] using hC2)
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
