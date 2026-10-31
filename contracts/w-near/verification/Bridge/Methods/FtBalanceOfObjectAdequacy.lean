import Bridge.Methods.FtBalanceOfObjectInitial
import Bridge.Methods.FtBalanceOfInitialAdequacy

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std
open Iris.ProgramLogic.Language.Notation
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293)
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
noncomputable def objectBodyCost (cfg : WasmConfig) (h0 h : NearState) (S : WNear.State) (a : WNear.AccountId)
    (bs rest : List UInt8) (N : Nat) : Nat :=
  475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + EnvInput.cost527 cfg h0 +
    (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
      SerdeObjectNoEsc.parserCost cfg 1 bs rest N + parserSuccessCost cfg 2 h S a 0)))))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_absent_adequate (runtime : RuntimeConfig) (Cg : Nat) (a : WNear.AccountId) (bs jsonRest : List UInt8) (N : Nat)
    (hlen : bs.length < 2 ^ 24)
    (hnb : (0x5C : UInt8) ∉ bs) (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, jsonRest))
    (hend : bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) = bs.length)
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
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none)
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (hret : withinLimit h.config.maxReturnLen 3 = true)
    (hgas : h0.gas.used + objectBodyCost runtime.wasm h0 h S a bs jsonRest N ≤ Cg) (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid)
    : adequate .MaybeStuck
      (MCode.running runtime.wasm execLimits
        (entryThread ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body))
      ⟨wStore runtime h0⟩
      (fun v σ' => v = .values [] ∧ ∃ cs, endCells297 Cg h a st cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  simp only [objectBodyCost] at hgas
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => v = .values [])
    (fun _ cs => endCells297 Cg h a st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜v = .values []⌝ ∗ mcellsSat (fun cs => endCells297 Cg h a st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (InitialState.startRes297Obj runtime h0).trans ?_
  iintro Hres
  iapply fupd_wp
  imod Hres with ⟨#HC, #HIgn, #Hinst, Hg, HH, Hgas, HF, HS, HPanic, V36, T44, ESC, UTF, HEX, Hkey, Hident⟩
  imodintro
  iapply mwp_entry runtime.wasm execLimits ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body Cg Ψ
  isplitr
  · iexact Hinst
  iapply object_absent_body_initial_resources runtime runtime.wasm execLimits 0 (by decide) Cg 0 a bs jsonRest N
    hlen hnb ho hloop hend  h0 h hinput hafter hinputLimit S st hv hacc hlim
    hcanon hlink bud hproof hbudget hlimAccount hnone hreg hret (entryPost Cg 0 Ψ)
  iunfold SerdeObjectNoEsc.parserStatics
  iframe HC HIgn Hg HF HS V36 T44 ESC UTF HEX Hkey Hident HH
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
  iexists [(Loc.host, Cell.host (erase (h2.selectReturnValue [34, 48, 34]))), (gasLoc, gasCellOf g pr act)]
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

end WNear.Binary.BalanceOf297AbsentCall
