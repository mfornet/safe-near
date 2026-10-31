import Bridge.Methods.FtBalanceOfCopiedRun
import Bridge.Methods.FtBalanceOfNoneAdequacy

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.FtTotalSupply (ReadNone)
open WNear.Binary.FtTotalSupplyMethod (trap_of_ending runInitialized_err runInitialized_finished endCellsNone_ends)
open WNear.Binary.BalanceOf297AbsentCall (entryCost_297 startW_thread297 storage_read_post_erase_source)

structure NonePre (bs : List UInt8) (st : Near.TrieOverlay.State) (e : NearState) : Prop where
  input : e.context.input = bs
  inputLimit : withinLimit e.config.maxRegisterLen bs.length = true
  read : ReadNone (inputHost e 0) st

def NoneDeployedParserProvider (cfg : RuntimeConfig) (bs : List UInt8) (a : WNear.AccountId)
    (parseGas outF : Nat) : Prop :=
  ∀ (h : NearState) [WasmGS NearState (WasmLogic.GF NearState)],
    BalanceOf297AbsentCall.ParserFamily (GF := WasmLogic.GF NearState) cfg.wasm execLimits 0 wInst id 0 0 0
      InitialState.g0.type bs a 1 parseGas outF (FromSliceSpec.codeCtx cfg h)

def noneProviderMethodCost (cfg : RuntimeConfig) (parseGas : Nat) (e : NearState) : Nat :=
  11 * cfg.wasm.regularOpCost + noneProviderBodyCost cfg.wasm e (inputHost e 0) parseGas

def noneMethodPost (st : Near.TrieOverlay.State) (e e' : NearState) : Prop :=
  ∃ h1, StorageReadPost (inputHost e 0) StateRead.stateKey 0 st h1 ∧
    e' = erase { h1 with lastError := some (.guestPanic FtTotalSupplyMethod.notInitMsg) }

theorem none_provider_body_cost_erase (cfg : WasmConfig) (e : NearState) (parseGas : Nat) :
    noneProviderBodyCost cfg (erase e) (inputHost (erase e) 0) parseGas =
      noneProviderBodyCost cfg e (inputHost e 0) parseGas := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- The whole method panics, with exact host and gas postconditions, conditional on its named provider. -/
theorem provider_none_runs (cfg : RuntimeConfig) (a : WNear.AccountId) (bs : List UInt8) (parseGas outF : Nat)
    (st : Near.TrieOverlay.State) (hlen : bs.length < 2 ^ 24) (hpos : 0 < bs.length)
    (hProvider : NoneDeployedParserProvider cfg bs a parseGas outF) :
    MethodPanicsR cfg 297 (NonePre bs st) (noneProviderMethodCost cfg parseGas) (noneMethodPost st) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 297)) (entryCost cfg.wasm (.next (startW cfg h 297))) =
      (.next { startW cfg h 297 with store := wStore cfg (charged h (11 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_297, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [noneProviderMethodCost] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1) (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have hr : ReadNone (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) st :=
    ⟨hpre.read.value, hpre.read.acc, hpre.read.keyLen, hpre.read.trie, hpre.read.zero,
      hpre.read.link, hpre.read.proof, hpre.read.logFits, hpre.read.readByte⟩
  have hbody : (charged h (11 * cfg.wasm.regularOpCost)).gas.used +
      noneProviderBodyCost cfg.wasm (charged h (11 * cfg.wasm.regularOpCost))
        (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) parseGas ≤ Cg := by
    rw [charged_gas_used, ← none_provider_body_cost_erase, erase_charged]
    simp only [noneProviderMethodCost] at hcost
    omega
  have had := provider_none_adequate cfg Cg a bs parseGas outF hlen hpos
    (charged h (11 * cfg.wasm.regularOpCost)) (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0)
    hpre.input rfl hpre.inputLimit st hr hbody (by simpa [charged] using hC1) (by simpa [charged] using hC2) (hProvider _)
  rw [← startW_thread297 cfg h] at had
  have hend := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hend
  obtain ⟨⟨t, rfl⟩, cs, hcs, hlk⟩ := hend
  have hrun := trap_of_ending (runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h1, hq, he, hu⟩ := endCellsNone_ends hcs hlk
  have heinput : erase (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) = erase (inputHost (erase h) 0) :=
    erase_inputHost (by rw [erase_charged, erase_erase]) 0
  have hq' : StorageReadPost (inputHost (erase h) 0) StateRead.stateKey 0 st h1 := by
    apply (storage_read_post_erase_source _ _ _ _ _).mp
    have hr := (storage_read_post_erase_source _ _ _ _ _).mpr hq
    rwa [heinput] at hr
  exact ⟨t, σ.store, hrun, ⟨h1, hq', he⟩, hu⟩
end WNear.Binary.BalanceOf297NoneCall
