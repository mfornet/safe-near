import Bridge.Methods.FtBalanceOfInitialCompose
import Bridge.Methods.Relational

/-! Adequacy of the copied-array absent-account body from its initial store.
The entry-thread proof covers runs that end, after activation. The separate
activation charge, boundary/model budget and other inputs remain to be composed. -/
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

/-- The final observable host and gas cells of the copied-array absent-account run. -/
def endCells297 (Cg : Nat) (h : NearState) (a : WNear.AccountId) (st : Near.TrieOverlay.State)
    (cs : List (Loc × Cell NearState)) : Prop :=
  ∃ (h1 : NearState) (st1 : Near.TrieOverlay.State) (h2 : NearState)
      (g : Near.GasCounter) (p : Near.GasProfile) (act : List (String × Nat)),
    StorageReadPost h WNear.stateKey 0 st h1 ∧
    StorageReadPost h1 (WNear.accountsPrefix ++
      (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2 ∧
    cs = [(Loc.host, .host (erase (h2.selectReturnValue [34, 48, 34]))),
      (gasLoc, gasCellOf g p act)] ∧ g.used ≤ Cg

theorem endCells297_ends {Cg : Nat} {h : NearState} {a : WNear.AccountId}
    {st : Near.TrieOverlay.State} {σ' : MStore} {cs : List (Loc × Cell NearState)}
    (hc : endCells297 Cg h a st cs) (hl : ∀ p ∈ cs, mlookup σ' p.1 = some p.2) :
    ∃ h1 st1 h2, StorageReadPost h WNear.stateKey 0 st h1 ∧
      StorageReadPost h1 (WNear.accountsPrefix ++
        (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2 ∧
      erase σ'.store.host = erase (h2.selectReturnValue [34, 48, 34]) ∧ σ'.store.host.gas.used ≤ Cg := by
  obtain ⟨h1, st1, h2, g, p, act, hs1, hs2, rfl, hg⟩ := hc
  have hh := hl _ List.mem_cons_self
  have hg' := hl _ (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [mlookup, show Loc.host ≠ gasLoc by decide, ite_false, ite_true, Option.some.injEq,
    Cell.host.injEq] at hh hg'
  obtain ⟨hgg, -, -⟩ := gasCellOf_inj hg'
  exact ⟨h1, st1, h2, hs1, hs2, hh, hgg ▸ hg⟩

theorem f297_frame : funcs[297 - 48]! = f297 := by kernel_rfl

theorem startW_thread297 (cfg : RuntimeConfig) (h : NearState) :
    (startW cfg h 297).thread = entryThread ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body := by
  simp only [startW, wFrame, f297_frame, entryThread]
  rfl

theorem entryCost_297 (cfg : RuntimeConfig) (h : NearState) :
    entryCost cfg.wasm (.next (startW cfg h 297)) = 11 * cfg.wasm.regularOpCost := by
  have ht := startW_thread297 cfg h
  simp only [entryCost, Config.locals, ht, entryThread, activationGas]
  simp [ValType.default]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem array_absent_adequate (runtime : RuntimeConfig) (Cg : Nat) (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : Nat)
    (hlen : bs.length < 2 ^ 24)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length))]? = some 0x5D)
    (hk : k = bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, jsonRest))

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
    (hgas : h0.gas.used + (475 * runtime.wasm.regularOpCost + (3 * runtime.wasm.regularOpCost + (100 * runtime.wasm.regularOpCost + cost527 runtime.wasm h0 + (100 * runtime.wasm.regularOpCost + (100 * runtime.wasm.regularOpCost + (1000 * runtime.wasm.regularOpCost +
        (45 * runtime.wasm.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * runtime.wasm.regularOpCost +
          costArray runtime.wasm 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost runtime.wasm (copiedParserFree bs (j + 1) 1) h S a 0)))))) ≤ Cg) (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid)
    : adequate .MaybeStuck
      (MCode.running runtime.wasm execLimits
        (entryThread ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body))
      ⟨wStore runtime h0⟩
      (fun v σ' => v = .values [] ∧ ∃ cs, endCells297 Cg h a st cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  apply mwp_adequacy_cells (GF' := WasmLogic.GF NearState) _ _ (fun v => v = .values [])
    (fun _ cs => endCells297 Cg h a st cs)
  intro _
  let Ψ : Ending → IProp (WasmLogic.GF NearState) := fun v =>
    iprop(⌜v = .values []⌝ ∗ mcellsSat (fun cs => endCells297 Cg h a st cs))
  show _ ⊢ WP _ @ _; _ {{ Ψ }}
  refine (InitialState.startRes297 runtime h0).trans ?_
  iintro Hres
  iapply fupd_wp
  imod Hres with ⟨#HC, #Hinst, Hg, HH, Hgas, HF, HS, HPanic, V36, T44, ESC, UTF, HEX⟩
  imodintro
  iapply mwp_entry runtime.wasm execLimits ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body Cg Ψ
  isplitr
  · iexact Hinst
  iapply array_absent_body_initial_resources runtime runtime.wasm execLimits 0 (by decide) Cg 0 a bs jsonRest j k
    hlen ho hj hq he hk hend hmodel  h0 h hinput hafter hinputLimit S st hv hacc hlim
    hcanon hlink bud hproof hbudget hlimAccount hnone hreg hret (entryPost Cg 0 Ψ)
  iframe HC Hg HF HS V36 T44 ESC UTF HEX HH
  isplitl [Hgas]
  · iunfold credits
    iexists h0.gas, h0.gasProfile, h0.actionProfile
    iframe Hgas
    ipureintro
    simp only [Near.GasCounter.used] at hgas ⊢
    omega
  inext
  iintro %p %c ⟨C, HIP, Hlen, ESC, UTF, HEX, Hg, Hheap, HR⟩
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

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The existing copied-only contract, preserved as a checked specialization. -/
theorem copied_array_absent_adequate (runtime : RuntimeConfig) (Cg : Nat) (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : Nat)
    (hlen : bs.length < 2 ^ 24)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length))]? = some 0x5D)
    (hk : k = bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, jsonRest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
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
    (hgas : h0.gas.used + (475 * runtime.wasm.regularOpCost + (3 * runtime.wasm.regularOpCost + (100 * runtime.wasm.regularOpCost + cost527 runtime.wasm h0 + (100 * runtime.wasm.regularOpCost + (100 * runtime.wasm.regularOpCost + (1000 * runtime.wasm.regularOpCost +
        (45 * runtime.wasm.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * runtime.wasm.regularOpCost +
          costArray runtime.wasm 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost runtime.wasm (copiedParserFree bs (j + 1) 1) h S a 0)))))) ≤ Cg) (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid)
    : adequate .MaybeStuck
      (MCode.running runtime.wasm execLimits
        (entryThread ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ 0 f297.body))
      ⟨wStore runtime h0⟩
      (fun v σ' => v = .values [] ∧ ∃ cs, endCells297 Cg h a st cs ∧
        ∀ p ∈ cs, mlookup σ' p.1 = some p.2) := by
  exact array_absent_adequate runtime Cg a bs jsonRest j k hlen ho hj hq he hk hend hmodel h0 h hinput hafter hinputLimit S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg hret hgas hC1 hC2
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual initial entry thread, with observable host and gas consequences. Activation is charged separately. -/
theorem copied_array_absent_adequate_host (runtime : RuntimeConfig) (Cg : Nat) (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : Nat)
    (hlen : bs.length < 2 ^ 24)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length))]? = some 0x5D)
    (hk : k = bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, jsonRest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
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
    (hgas : h0.gas.used + (475 * runtime.wasm.regularOpCost + (3 * runtime.wasm.regularOpCost + (100 * runtime.wasm.regularOpCost + cost527 runtime.wasm h0 + (100 * runtime.wasm.regularOpCost + (100 * runtime.wasm.regularOpCost + (1000 * runtime.wasm.regularOpCost +
        (45 * runtime.wasm.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * runtime.wasm.regularOpCost +
          costArray runtime.wasm 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost runtime.wasm (copiedParserFree bs (j + 1) 1) h S a 0)))))) ≤ Cg) (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid)
    : adequate .MaybeStuck
      (MCode.running runtime.wasm execLimits
        (startW runtime h0 297).thread)
      ⟨wStore runtime h0⟩
      (fun v σ' => v = .values [] ∧ ∃ h1 st1 h2,
        StorageReadPost h WNear.stateKey 0 st h1 ∧
        StorageReadPost h1 (WNear.accountsPrefix ++
          (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2 ∧
        erase σ'.store.host = erase (h2.selectReturnValue [34, 48, 34]) ∧ σ'.store.host.gas.used ≤ Cg) := by
  rw [startW_thread297]
  have hcase := copied_array_absent_adequate runtime Cg a bs jsonRest j k
    hlen ho hj hq he hk hend hmodel hcopied h0 h hinput hafter hinputLimit S st hv hacc hlim
    hcanon hlink bud hproof hbudget hlimAccount hnone hreg hret hgas hC1 hC2
  refine ⟨?_, hcase.adequate_not_stuck⟩
  intro t2 σ2 v hv2
  obtain ⟨hr, cs, hcs, hl⟩ := hcase.adequate_result t2 σ2 v hv2
  exact ⟨hr, endCells297_ends hcs hl⟩

end WNear.Binary.BalanceOf297AbsentCall
