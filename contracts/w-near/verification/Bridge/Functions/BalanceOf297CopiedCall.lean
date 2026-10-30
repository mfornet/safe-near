import Bridge.Functions.BalanceOf297CopiedParser
import Bridge.Functions.BalanceOf297ParserPublicCompose

/-! Compose the decoded parser success handoff with state read and absent balance cleanup. -/
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
theorem copied_parser_call_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail parserOut jsonRest : List UInt8) (j k : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hparserOut : parserOut.length = 16)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length))]? = some 0x5D)
    (hk : k = bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, jsonRest))
    (hcopied : ¬ borrowed (bs.drop (j + 1))) (hparserRoom : roomRun 2048 len 0 [] (bs.drop (j + 1)))
    (halloc : roomFor (len + growthPages 0 0 (appendChunks (bs.drop (j + 1)) []) * 65536)
      2048 (UInt32.ofNat a.val.toUTF8.toList.length))
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hroom : HeapRoomK (copiedParserPages bs (j + 1) a + 6) len 2048)
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none)
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg F 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) F) h S a R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[wms][ (s + 88).toNat ] parserOut ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 48).toNat + 8 ] UInt32.ofNat bs.length ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((copiedParserFree bs (j + 1) F + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [.i32 (s + 88), .i32 ip, .i32 (UInt32.ofNat bs.length)] ((f297.body.drop 35).take 115) Φ := by
  iintro ⟨#HC66, #H169, #H646, #F644, #F66, #F65, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, HparserOut, Hbs, Htail, Hesc, Hutf, Hhex, HstateTail,
    A0, A8, HdestTail, B0, B8, I0, I4, I8, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 35).take 115 = [.call 65] ++ (f297.body.drop 36).take 114 := by rfl
  rw [hseg]
  iapply mwpi_seq
  icases stk_split n (s.toNat - 592) 144 448 $$ Hstk with ⟨Hlo, Hstk⟩
  ihave Hstk := stk_addr (show s.toNat - 592 + 144 = s.toNat - 448 by omega) $$ Hstk
  have hn := hm.mem
  have ha65 := hm.funcs 65 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  mcall (f65_arr_copied_room cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt
    s (s + 88) ip idx parserOut bs a jsonRest j k len F ((ip.toNat, ic.toNat) :: live)
    hparserOut (by simp [UInt32.toNat_add]; omega) hlen hptr (by omega) ho hj hq he hk hend hmodel
    hcopied hparserRoom halloc hroom) using [Hg Hstk Hvt Hinv HparserOut Hbs Hesc Hutf Hhex]
    with (unfold parserSuccessCost; mstep_norm_full; omega)
  · iframe Hg Hstk Hvt Hinv HparserOut Hbs Hesc Hutf Hhex
  icases HQ with ⟨%hrs, Hg, Hstk, Hvt, Hbs, Hesc, Hutf, Hhex, %len', %hroom', Hparser⟩
  subst hrs
  ihave Hstk := stk_addr (show s.toNat - 448 = s.toNat - 592 + 144 by omega) $$ Hstk
  ihave Hstk := stk_join n (s.toNat - 592) 144 448 $$ [Hlo Hstk]
  · iframe Hlo Hstk
  ihave Hinput := BorshFT.joinB (n := n) (a := ip.toNat) (b := ip.toNat + bs.length) bs tail rfl $$ [Hbs Htail]
  · iframe Hbs Htail
  ihave Hblock : block n ip.toNat ic.toNat $$ [Hinput]
  · iunfold block
    iexists bs ++ tail
    iframe Hinput
    ipureintro; simp [hinput]
  iapply (parser_fixed_through_cleanup cfg lim d inst e mi A n g ta mx hm (by omega) Cg R gt s x1 x2 x3
    ip ic (UInt32.ofNat bs.length) idx len' a live (copiedParserFree bs (j + 1) F)
    ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic hob hstateTail
    hcontractTail hdestTail hA hB hout hhead h S st hv hroom' hacc hlim hcanon hlink bud hproof hbudget
    hlimAccount hnone hreg ptr0 hret Φ)
  unfold parserSuccessCost at *
  iframe HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi Hg HI Hstk Hvt
    Hstatekey Hhost Hparser HstateTail A0 A8 HdestTail B0 B8 I0 I4 I8 HcontractTail Hblock Hob HD Hout Hhead
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro %p %c Hpost
  icases Hpost with ⟨Hc, Hg, Hinv, Hhost⟩
  ispecialize HΦ $$ %p %c
  iapply HΦ $$ [Hc Hesc Hutf Hhex Hg Hinv Hhost]
  iframe Hc Hesc Hutf Hhex Hg Hinv Hhost
end Spec
end WNear.Binary.BalanceOf297AbsentCall
