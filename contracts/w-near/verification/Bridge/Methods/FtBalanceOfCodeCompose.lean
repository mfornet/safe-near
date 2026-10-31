import Bridge.Methods.Code297

/-! The complete copied-array body with instantiated code ownership. -/
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
/-- The copied-array absent-account body with its code obtained from the actual function-cell list. -/
theorem copied_array_absent_body_store_code (runtime : RuntimeConfig) (cfg : WasmConfig) (lim : ExecLimits) (d : Nat)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (j k : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 < 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length))]? = some 0x5D)
    (hk : k = bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, jsonRest))
    (hcopied : ¬ borrowed (bs.drop (j + 1)))
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
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
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    (([∗list] p ∈ InitialState.funcCells runtime h0, p.1 ↦ₛ□ p.2) ∗
      (0 ↪[inst] wInst : IProp GF) ∗ 0 ↪[wmlimit] some 2048) ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg 1 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) 1) h S a R)))))) ∗
      0 ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ stk 0 (s.toNat - 592) 592 ∗
      hookCells 0 0 hookOld 0 ∗ 0 ↦[i32][ 1055020 ] 116 ∗
      0 ↦[wt][ 116 ] Ref.func (id 565) ∗ 0 ↦[wt][ 106 ] Ref.func (id 564) ∗
      blockchainInterfaceCells 0 0 0 0 k3 ∗ vtab 0 0 id ∗
      0 ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ 0 ↦[wt][ 44 ] Ref.func (id 246) ∗
      vt 0 1057464 idx 0 (id 578) ∗ 0 ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv 0 2048 InitialState.memLen live 1 ∗ 0 ↦[wms][ (s + 88).toNat ] oldOpt ∗
      0 ↦[wms][ (s + 100).toNat ] optTail ∗
      0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      0 ↦[wms][ (s + 104).toNat ] stateTail ∗
      0 ↦[wms][ (s + 128).toNat ] oldA ∗ 0 ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      0 ↦[wms][ (s + 140).toNat ] destTail ∗
      0 ↦[wms][ (s + 32).toNat ] oldB ∗ 0 ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      0 ↦[wms][ (s + 24).toNat ] derefOut ∗
      0 ↦[wms][ (s + 48).toNat ] oldVec ∗ 0 ↦[wms][ (s + 60).toNat ] contractTail ∗
      0 ↦[wms][ (s + 8).toNat ] ob ∗
      tvData 0 0 ptr0 (id 759) (id 353) ∗
      0 ↦[wms][ (s + 144).toNat ] out ∗ 0 ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        (∃ ip : UInt32, 0 ↦[i32][ (s + 24).toNat ] ip) ∗
        0 ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        0 ↦[wms][ 1062392 ] ParseStr.escTable ∗ 0 ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        0 ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ 0 ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv 0 2048 hl live (((((copiedParserFree bs (j + 1) 1 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame 0 wInst s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], 0, wInst⟩ [] f297.body Φ := by
  refine (sep_mono_left (InitialState.code297_of runtime h0)).trans ?_
  have hbody := copied_array_absent_body_initial_memory cfg lim d 0 runtime.fees.numExtraBytesRecord wInst id 0 0 0
    (some 2048) Interface.wInst_ifaceMod hd Cg R gt s x1 x2 x3 idx a live bs oldOpt optTail oldVec jsonRest derefOut j k
    ob stateTail contractTail destTail out head oldA oldB oldC oldD hookOld k3 hs hal hframe hopt hoptTail holdVec hderef
    hlen ho hj hq he hk hend hmodel hcopied hob hstateTail hcontractTail hdestTail hA hB hout hhead h0 h hinput hafter
    hinputLimit S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ
  simpa only [code297, code297Input, code297Parser, code297Lookup, code297Return, sep_assoc.to_eq, id] using hbody
end Spec
end WNear.Binary.BalanceOf297AbsentCall
