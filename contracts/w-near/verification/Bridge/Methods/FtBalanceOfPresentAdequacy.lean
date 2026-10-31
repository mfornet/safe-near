import Bridge.Methods.FtBalanceOfPresentGas

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfPresent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
open WNear.Binary.FtTotalSupply (codeA vtab)
open WNear.Binary.SetupPanicHook (hookCells)
open WNear.Binary.SetBlockchainInterface (blockchainInterfaceCells)
open WNear.Binary.Interface (dataWord)
open WNear.Binary.EnvInput (inCode pre527 post527 ifaceI cost527 f527_spec)
open WNear.Binary.ReadRegister (RegOk optVecAt)
open WNear.Binary.VecFromElem (stk_split stk_join stk_addr grownLen)
open WNear.Binary.VecFromElem (stk_split stk_join stk_addr)
open WNear.Binary.SerdeFromTrait (code66)
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.ParseStr (borrowed roomRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
open WNear.Binary.ScratchGrow (growthPages)
open WNear.Binary.SerdeStruct78Esc (costArray)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_present_adequate (runtime : RuntimeConfig) (Cg : Nat) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8) (parseGas outF : Nat)
    (hlen : bs.length < 2 ^ 24)
    (hpos : 0 < bs.length)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true)
    (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true)
    (hgas : h0.gas.used + presentProviderBodyCost runtime.wasm h0 h S a lo hi parseGas outF ≤ Cg) (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid)
    (hp : ∀ [WasmGS NearState (WasmLogic.GF NearState)], PresentParserFamily (GF := WasmLogic.GF NearState) runtime.wasm execLimits 0 wInst id 0 0 0
      InitialState.g0.type bs a 1 parseGas outF (FromSliceSpec.codeCtx runtime h0))
    : adequate .MaybeStuck
      (MCode.running runtime.wasm execLimits
        (entryThread ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body))
      ⟨wStore runtime h0⟩
      (fun v σ' => v = .values [] ∧ ∃ cs, presentEndCells297 Cg h a lo hi st cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  simp only [presentProviderBodyCost] at hgas
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => v = .values [])
    (fun _ cs => presentEndCells297 Cg h a lo hi st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜v = .values []⌝ ∗ mcellsSat (fun cs => presentEndCells297 Cg h a lo hi st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (InitialState.startRes297Provider runtime h0).trans ?_
  iintro Hres
  iapply fupd_wp
  imod Hres with ⟨#HCd, #HC, #HIgn, #Hinst, Hg, HH, Hgas, HF, HS, HPanic, V36, T44, ESC, UTF, HEX, Hkey, Hident⟩
  imodintro
  iapply mwp_entry runtime.wasm execLimits ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body Cg Ψ
  isplitr
  · iexact Hinst
  iapply provider_present_body_initial_resources runtime runtime.wasm execLimits 0 (by decide) Cg 0 a lo hi bs parseGas outF (FromSliceSpec.codeCtx runtime h0)
    hlen hpos  h0 h hinput hafter hinputLimit S st hv hacc hlim
    hcanon hlink bud hproof hbudget hlimAccount hsome hreg hret (entryPost Cg 0 Ψ) hp
  iunfold SerdeObjectNoEsc.parserStatics
  iframe HCd HC HIgn Hg HF HS V36 T44 ESC UTF HEX Hkey Hident HH
  isplitl [Hgas]
  · iunfold credits
    iexists h0.gas, h0.gasProfile, h0.actionProfile
    iframe Hgas
    ipureintro
    simp only [Near.GasCounter.used] at hgas ⊢
    omega
  inext
  iintro %p %c ⟨C, HIP, Hlen, ESC, UTF, HEX, HFr, Hg, Hheap, HR⟩
  icases HR with ⟨%h1, %hs1, %st1, %h2, %hs2, HH⟩
  simp only [entryPost]
  isplitr
  · ipureintro; rfl
  iexists 0
  iframe C
  iintro C
  isplitr
  · ipureintro; rfl
  iunfold credits at C
  icases C with ⟨%g, %pr, %act, HG, %hg⟩
  iexists [(Loc.host, Cell.host (erase (h2.selectReturnValue ([34] ++ FmtDigits.decDigits (FmtU128.val lo hi) ++ [34])))), (gasLoc, gasCellOf g pr act)]
  isplitr
  · ipureintro
    exact ⟨⟨h1, st1, h2, g, pr, act, hs1, hs2, rfl, by omega⟩,
      by simp only [List.map_cons, List.map_nil]; decide⟩
  iapply BigSepL.bigSepL_cons.2
  isplitl [HH]
  · iunfold mhostPt at HH
    iexact HH
  iapply BigSepL.bigSepL_cons.2
  isplitl [HG]
  · iunfold gasPt at HG
    iexact HG
  iapply BigSepL.bigSepL_nil.2
  iempintro

end WNear.Binary.BalanceOf297PresentCall



namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.BalanceOf297AbsentCall (copiedKey entryCost_297 startW_thread297 storage_read_post_erase_source)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

def PresentDeployedParserProvider (cfg : RuntimeConfig) (bs : List UInt8) (a : WNear.AccountId)
    (parseGas outF : Nat) : Prop :=
  ∀ (h : NearState) [WasmGS NearState (WasmLogic.GF NearState)],
    PresentParserFamily (GF := WasmLogic.GF NearState) cfg.wasm execLimits 0 wInst id 0 0 0 InitialState.g0.type bs a 1 parseGas outF
      (FromSliceSpec.codeCtx cfg h)

structure PresentPre (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64) (bs : List UInt8)
    (st : Near.TrieOverlay.State) (bud : Nat) (e : NearState) : Prop where
  input : e.context.input = bs
  inputLimit : withinLimit e.config.maxRegisterLen bs.length = true
  value : e.storage WNear.stateKey = some (WNear.header S)
  accounting : e.storageAccounting = some st
  keyLimit : withinLimit e.config.maxStorageKeyLen 5 = true
  canonical : Canon st
  link : StorageLink e st
  proof : ProofBudget e st bud
  budget : readProofCost (contractKey e.context.currentAccountId WNear.stateKey) (e.storage WNear.stateKey) +
    readProofCost (contractKey e.context.currentAccountId (copiedKey a)) (e.storage (copiedKey a)) ≤ bud
  accountLimit : withinLimit e.config.maxStorageKeyLen (copiedKey a).length = true
  present : e.storage (copiedKey a) = some (u128Bytes lo hi)
  registerLimit : withinLimit e.config.maxRegisterLen 29 = true
  returnLimit : withinLimit e.config.maxReturnLen (resultLen lo hi).toNat = true

def presentMethodPost (a : WNear.AccountId) (lo hi : UInt64) (st : Near.TrieOverlay.State) (e e' : NearState) : Prop :=
  ∃ h1 st1 h2, StorageReadPost (inputHost e 0) WNear.stateKey 0 st h1 ∧
    StorageReadPost h1 (copiedKey a) 0 st1 h2 ∧ e' = erase (h2.selectReturnValue ([34] ++ FmtDigits.decDigits (FmtU128.val lo hi) ++ [34]))

noncomputable def presentProviderMethodCost (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64)
    (parseGas outF : Nat) (e : NearState) : Nat :=
  11 * cfg.wasm.regularOpCost + presentProviderBodyCost cfg.wasm e (inputHost e 0) S a lo hi parseGas outF

theorem present_provider_body_cost_erase (cfg : WasmConfig) (e : NearState) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64)
    (parseGas outF : Nat) :
    presentProviderBodyCost cfg (erase e) (inputHost (erase e) 0) S a lo hi parseGas outF =
      presentProviderBodyCost cfg e (inputHost e 0) S a lo hi parseGas outF := rfl

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem provider_present_runs (cfg : RuntimeConfig) (S : WNear.State) (a : WNear.AccountId) (lo hi : UInt64)
    (bs : List UInt8) (parseGas outF : Nat) (st : Near.TrieOverlay.State) (bud : Nat)
    (hlen : bs.length < 2 ^ 24) (hpos : 0 < bs.length)
    (hProvider : PresentDeployedParserProvider cfg bs a parseGas outF)
     :
    MethodRunsR cfg 297 (PresentPre S a lo hi bs st bud) (presentProviderMethodCost cfg S a lo hi parseGas outF) (presentMethodPost a lo hi st) := by
  intro fuel h Cg hpre hcost hC1 hC2 hfuel
  have hw : (wStore cfg h).host = h := rfl
  have hentry : chargeWasm (.next (startW cfg h 297)) (entryCost cfg.wasm (.next (startW cfg h 297))) =
      (.next { startW cfg h 297 with store := wStore cfg (charged h (11 * cfg.wasm.regularOpCost)) }, none) := by
    rw [entryCost_297, chargeWasm_ok (C := Cg)
      (by simp only [startW, StepResult.store, hw]; simp only [presentProviderMethodCost] at hcost; omega)
      (by simpa [startW, StepResult.store, hw] using hC1)
      (by simpa [startW, StepResult.store, hw] using hC2)]
    rfl
  have hp : PresentPre S a lo hi bs st bud (charged h (11 * cfg.wasm.regularOpCost)) :=
    ⟨hpre.input, hpre.inputLimit, hpre.value, hpre.accounting, hpre.keyLimit, hpre.canonical,
      hpre.link, hpre.proof, hpre.budget, hpre.accountLimit, hpre.present, hpre.registerLimit, hpre.returnLimit⟩
  have hbody : (charged h (11 * cfg.wasm.regularOpCost)).gas.used +
      presentProviderBodyCost cfg.wasm (charged h (11 * cfg.wasm.regularOpCost))
        (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) S a lo hi parseGas outF ≤ Cg := by
    rw [charged_gas_used, ← present_provider_body_cost_erase, erase_charged]
    simp only [presentProviderMethodCost] at hcost
    omega
  have had := provider_present_adequate cfg Cg a lo hi bs parseGas outF hlen hpos
    (charged h (11 * cfg.wasm.regularOpCost)) (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0)
    hp.input rfl hp.inputLimit S st hp.value hp.accounting hp.keyLimit hp.canonical hp.link bud hp.proof
    hp.budget hp.accountLimit hp.present hp.registerLimit hp.returnLimit hbody
    (by simpa [charged] using hC1) (by simpa [charged] using hC2) (hProvider _)
  rw [← startW_thread297 cfg h] at had
  have hending := runInitialized_ending_state cfg.wasm fuel _ _ _ hentry had
  obtain ⟨e, σ, hrc⟩ := FtTotalSupplyMethod.runInitialized_finished cfg.wasm fuel _ hfuel
  rw [hrc] at hending
  obtain ⟨rfl, cs, hcs, hlk⟩ := hending
  have hrun := FtTotalSupplyMethod.done_of_values (FtTotalSupplyMethod.runInitialized_err cfg.wasm fuel _) hfuel hrc
  obtain ⟨h1, st1, h2, hs1, hs2, heq, hu⟩ := presentEndCells297_ends hcs hlk
  have heinput : erase (inputHost (charged h (11 * cfg.wasm.regularOpCost)) 0) = erase (inputHost (erase h) 0) :=
    erase_inputHost (by rw [erase_charged, erase_erase]) 0
  have hs1' : StorageReadPost (inputHost (erase h) 0) WNear.stateKey 0 st h1 := by
    apply (storage_read_post_erase_source _ _ _ _ _).mp
    have hr := (storage_read_post_erase_source _ _ _ _ _).mpr hs1
    rwa [heinput] at hr
  exact ⟨σ.store, hrun, ⟨h1, st1, h2, hs1', hs2, heq⟩, hu⟩


end WNear.Binary.BalanceOf297PresentCall
