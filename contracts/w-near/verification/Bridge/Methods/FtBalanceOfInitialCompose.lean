import Bridge.Methods.Statics297

/-! The copied-array body with the exact initial frame and static resources. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
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

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The complete body from the initial instance code, frame and static resources. -/
theorem array_absent_body_initial_resources (runtime : RuntimeConfig) (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : Nat)
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
    (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    code297 runtime.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) 1) h S a R)))))) ∗
      0 ↦[wg] InitialState.g0 ∗ InitialState.frame297 0 ∗
      FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 InitialState.memLen ∗
      0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ mhostPt h0 ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        (∃ ip : UInt32, 0 ↦[i32][ ((1048416 : UInt32) + 24).toNat ] ip) ∗
        0 ↦[i32][ ((1048416 : UInt32) + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ 0 ↦[wg] InitialState.g0 ∗ (∃ hl, heapInv 0 2048 hl [] (((((copiedParserFree bs (j + 1) 1 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame 0 wInst (1048416 : UInt32) (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) ((1048416 : UInt32) + 40))) ⊢
    mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ [] f297.body Φ := by
  iintro ⟨HC, C, Hg, HF, HS, V36, T44, ESC, UTF, HEX, HH, HK⟩
  have hbody := array_absent_body_initial_memory cfg lim d 0 runtime.fees.numExtraBytesRecord wInst id 0 0 0
    (some 2048) Interface.wInst_ifaceMod hd Cg R InitialState.g0.type 1048416 0 0 0 123 a [] bs
    (List.replicate 12 0) (List.replicate 4 0) (List.replicate 12 0) jsonRest (List.replicate 8 0) j k
    (List.replicate 16 0) (List.replicate 24 0) (List.replicate 28 0) (List.replicate 4 0)
    (List.replicate 12 0) (List.replicate 8 0) (List.replicate 8 0) (List.replicate 8 0) 0 0 0 0
    (by decide) (by decide) (by decide) (by simp) (by simp) (by simp) (by simp)
    hlen ho hj hq he hk hend hmodel  (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) h0 h hinput hafter hinputLimit S st hv hacc hlim
    hcanon hlink bud hproof hbudget hlimAccount hnone hreg 1051836 hret Φ
  rw [show (⟨InitialState.g0.type, .i32 ((1048416 : UInt32) + 160)⟩ : GlobalInst) = InitialState.g0 by simp [InitialState.g0]] at hbody
  simp only [id] at hbody
  iapply hbody
  iunfold code297 at HC
  icases HC with ⟨HI, HP, HL, HR, HIF, HINST⟩
  iunfold code297Input at HI
  icases HI with ⟨HI0, HI1, HI2⟩
  iunfold code297Parser at HP
  icases HP with ⟨HP0, HP1, HP2, HP3, HP4, HP5, HP6⟩
  iunfold code297Lookup at HL
  icases HL with ⟨HL0, HL1, HL2, HL3, HL4, HL5⟩
  iunfold code297Return at HR
  icases HR with ⟨HR0, HR1, HR2, HR3, HR4, HR5, HR6, HR7⟩
  iunfold InitialState.frame297 at HF
  icases HF with ⟨STK, HEAD, OB, DEREF, B, D, VEC, CT, OPT, OT, ST, A, AC, DT, OUT, -⟩
  iunfold FtTotalSupply.statics at HS
  icases HS with ⟨HOOK, LK, T116, T106, BC, VTAB, VT, HEAP, KEY, TV⟩
  simp [id]
  iframe C Hg V36 T44 ESC UTF HEX HH HK HIF HINST HI0 HI1 HI2 HP0 HP1 HP2 HP3 HP4 HP5 HP6 HL0 HL1 HL2 HL3 HL4 HL5 HR0 HR1 HR2 HR3 HR4 HR5 HR6 HR7 STK HEAD OB DEREF B D VEC CT OPT OT ST A AC DT OUT HOOK LK T116 T106 BC VTAB VT HEAP KEY TV

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The existing copied-only contract, preserved as a checked specialization. -/
theorem copied_array_absent_body_initial_resources (runtime : RuntimeConfig) (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : Nat)
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
    (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    code297 runtime.fees.numExtraBytesRecord 0 wInst id 0 (some 2048) ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) 1) h S a R)))))) ∗
      0 ↦[wg] InitialState.g0 ∗ InitialState.frame297 0 ∗
      FtTotalSupply.statics 0 0 id 0 0 123 1051836 2048 InitialState.memLen ∗
      0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func 246 ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ mhostPt h0 ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        (∃ ip : UInt32, 0 ↦[i32][ ((1048416 : UInt32) + 24).toNat ] ip) ∗
        0 ↦[i32][ ((1048416 : UInt32) + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ 0 ↦[wg] InitialState.g0 ∗ (∃ hl, heapInv 0 2048 hl [] (((((copiedParserFree bs (j + 1) 1 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame 0 wInst (1048416 : UInt32) (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) ((1048416 : UInt32) + 40))) ⊢
    mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ [] f297.body Φ := by
  exact array_absent_body_initial_resources runtime cfg lim d hd Cg R a bs jsonRest j k hlen ho hj hq he hk hend hmodel h0 h hinput hafter hinputLimit S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg hret Φ
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- Derive all body resources from the instantiated store, funding gas from its own cell. -/
theorem copied_array_absent_body_initial_store (runtime : RuntimeConfig) (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (a : WNear.AccountId) (bs jsonRest : List UInt8) (j k : Nat)
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
    (hgas : h0.gas.used + (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) 1) h S a R)))))) ≤ Cg) (hC1 : Cg ≤ h0.gas.maxBurnt) (hC2 : Cg ≤ h0.gas.prepaid)
    (Φ : Post NearState GF) :
    ownCells (GF := GF) (mheapOf ⟨wStore runtime h0⟩) ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        (∃ ip : UInt32, 0 ↦[i32][ ((1048416 : UInt32) + 24).toNat ] ip) ∗
        0 ↦[i32][ ((1048416 : UInt32) + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ 0 ↦[wg] InitialState.g0 ∗ (∃ hl, heapInv 0 2048 hl [] (((((copiedParserFree bs (j + 1) 1 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame 0 wInst (1048416 : UInt32) (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) ((1048416 : UInt32) + 40))) ⊢
    |==> mwpi cfg lim d ⟨#[.i32 0, .i32 0, .i64 0, .i32 0], 0, wInst⟩ [] f297.body Φ := by
  refine (sep_mono_left (InitialState.startRes297 runtime h0)).trans ?_
  iintro ⟨Hres, HK⟩
  imod Hres with
    ⟨HC, Hinst, Hg, HH, Hgas, HF, HS, HPanic, V36, T44, ESC, UTF, HEX⟩
  imodintro
  iapply copied_array_absent_body_initial_resources runtime cfg lim d hd Cg R a bs jsonRest j k
    hlen ho hj hq he hk hend hmodel hcopied h0 h hinput hafter hinputLimit S st hv hacc hlim
    hcanon hlink bud hproof hbudget hlimAccount hnone hreg hret Φ
  iframe HC Hg HF HS V36 T44 ESC UTF HEX HH HK
  iunfold credits
  iexists h0.gas, h0.gasProfile, h0.actionProfile
  iframe Hgas
  ipureintro
  simp only [Near.GasCounter.used] at hgas ⊢
  omega

end Spec
end WNear.Binary.BalanceOf297AbsentCall
