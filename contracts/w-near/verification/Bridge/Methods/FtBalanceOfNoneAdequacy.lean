import Bridge.Functions.BalanceOf297NoneParser
import Bridge.Methods.Statics297NoneProvider

namespace WNear.Binary.BalanceOf297NoneCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.ReadRegister (iface_of_ifaceR)
open WNear.Binary.BorshFT (splitB stkSp)
open WNear.Binary.FtTotalSupply (stk4_word tsub)
open WNear.Binary.FtTotalSupply (ReadNone storageReadPost_fields logFits_of panicUtf8Use_of codeP staticsP)
open WNear.Binary.PanicStr (panicked notInit)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.StateReadNoneFree (post219NoneF f219_spec_noneF)
open Iris.Std Iris.ProgramLogic.Language.Notation
open WNear.Binary.FtTotalSupplyMethod (endCellsNone)

def noneProviderBodyCost (cfg : WasmConfig) (h0 h : NearState) (parseGas : Nat) : Nat :=
  475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + EnvInput.cost527 cfg h0 +
    (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost + parseGas +
      (400 * cfg.regularOpCost + (600 * cfg.regularOpCost + storageReadUse h StateRead.stateKey 5 + panicUtf8Use h 31)))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- Adequacy of the whole deployed uninitialized path, still conditional on the named parser family. -/
theorem provider_none_adequate (runtime : RuntimeConfig) (Cg : Nat) (a : WNear.AccountId) (bs : List UInt8)
    (parseGas outF : Nat) (hlen : bs.length < 2 ^ 24) (hpos : 0 < bs.length)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true)
    (st : Near.TrieOverlay.State) (hr : ReadNone h st)
    (hgas : h0.gas.used + noneProviderBodyCost runtime.wasm h0 h parseGas ≤ Cg)
    (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid)
    (hp : ∀ [WasmGS NearState (WasmLogic.GF NearState)], BalanceOf297AbsentCall.ParserFamily (GF := WasmLogic.GF NearState)
      runtime.wasm execLimits 0 wInst id 0 0 0 InitialState.g0.type bs a 1 parseGas outF (FromSliceSpec.codeCtx runtime h0)) :
    adequate .MaybeStuck (MCode.running runtime.wasm execLimits
      (entryThread ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body)) ⟨wStore runtime h0⟩
      (fun v σ' => (∃ r, v = .trap r) ∧ ∃ cs, endCellsNone Cg h st cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => ∃ r, v = .trap r)
    (fun _ cs => endCellsNone Cg h st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜∃ r, v = .trap r⌝ ∗ mcellsSat (fun cs => endCellsNone Cg h st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (InitialState.startRes297NoneProvider runtime h0).trans ?_
  iintro Hres
  iapply fupd_wp
  imod Hres with ⟨#HPanic, #HCd, #HC, #HIgn, #Hinst, Hg, HH, Hgas, HF, HS, HSP, V36, T44, ESC, UTF, HEX, Hkey, Hident⟩
  imodintro
  iapply mwp_entry runtime.wasm execLimits ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body Cg Ψ
  isplitr
  · iexact Hinst
  iapply provider_none_body_initial_resources runtime runtime.wasm execLimits 0 (by decide) Cg 0 a bs parseGas outF
    (FromSliceSpec.codeCtx runtime h0) hlen hpos h0 h hinput hafter hinputLimit st hr (entryPost Cg 0 Ψ) hp
  iunfold SerdeObjectNoEsc.parserStatics, FtTotalSupply.staticsP
  iframe HCd HC HPanic Hg HF HS V36 T44 ESC UTF HEX Hkey Hident HH HSP
  isplitl [Hgas]
  · iunfold credits
    iexists h0.gas, h0.gasProfile, h0.actionProfile
    iframe Hgas
    ipureintro
    simp only [noneProviderBodyCost, Nat.add_zero, Near.GasCounter.used] at hgas ⊢
    omega
  iintro %h1 %hq HT
  simp only [entryPost]
  iintro %r
  iunfold panicked at HT
  icases HT with ⟨%h', %he, Hh, %R, Hc⟩
  iunfold credits at Hc
  icases Hc with ⟨%g, %p, %a, Hg', %hg⟩
  isplitr
  · ipureintro; exact ⟨r, rfl⟩
  iexists [(Loc.host, Cell.host (erase h')), (gasLoc, gasCellOf g p a)]
  isplitr
  · ipureintro
    refine ⟨⟨h1, h', g, p, a, hq, ?_, rfl, by omega⟩, by simp only [List.map_cons, List.map_nil]; decide⟩
    rw [he, PanicStr.notInit_utf8String]
    rfl
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hh]
  · iunfold mhostPt at Hh
    iexact Hh
  iapply BigSepL.bigSepL_cons.2
  isplitl [Hg']
  · iunfold gasPt at Hg'
    iexact Hg'
  iapply BigSepL.bigSepL_nil.2
  iempintro

end WNear.Binary.BalanceOf297NoneCall
