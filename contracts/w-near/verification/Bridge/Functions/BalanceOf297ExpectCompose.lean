import Bridge.Functions.BalanceOf297InputExpect
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
theorem array_expect_deref_parser_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail optTail oldVec jsonRest derefOut : List UInt8) (j k : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (ho : bs[wsLen bs]? = some 0x5B)
    (hj : j = wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) (hq : bs[j]? = some 0x22)
    (he : bs[bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length))]? = some 0x5D)
    (hk : k = bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) + 1)
    (hend : k + wsLen (bs.drop k) = bs.length)
    (hmodel : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, jsonRest))
     (hparserRoom : roomRun 2048 len 0 [] (bs.drop (j + 1)))
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
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg F 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) F) h S a R))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗
      n ↦[i32][ (s + 88).toNat ] ip ∗ n ↦[i32][ (s + 88).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 88).toNat + 8 ] UInt32.ofNat bs.length ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] oldVec ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        n ↦[i32][ (s + 24).toNat ] ip ∗ n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((copiedParserFree bs (j + 1) F + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 13).take 137) Φ := by
  iintro ⟨#HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, O0, O4, O8, HoptTail, Hbs, Htail, Hesc, Hutf, Hhex, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 13).take 137 =
      (f297.body.drop 13).take 8 ++ (f297.body.drop 21).take 129 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (input_expect cfg lim d inst mi A n hm.mem (hm.funcs 157 (by decide)) (by omega) Cg
    (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
      (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
        costArray cfg F 0 bs a.val.toUTF8.toList jsonRest j)) +
      parserSuccessCost cfg (copiedParserFree bs (j + 1) F) h S a R))
    s x1 x2 x3 ip ic (UInt32.ofNat bs.length) oldVec holdVec hip hframe)
  iframe Hi F157 Hc Hvec O0 O4 O8
  inext
  iintro ⟨Hc, O0, O4, O8, V0, V4, V8⟩
  ihave OptTail := AllocNewCell.memBytes_addr (show (s + 100).toNat = (s + 88).toNat + 12 by
    simp [UInt32.toNat_add]; have := s.toNat_lt; omega) $$ HoptTail
  ihave Opt := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 4)
    (bytes32 ip) (bytes32 ic) (by simp) $$ [O0 O4]
  · iframe O0 O4
  ihave Opt := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 8)
    (bytes32 ip ++ bytes32 ic) (bytes32 (UInt32.ofNat bs.length)) (by simp [bytes32_length]) $$ [Opt O8]
  · iframe Opt O8
  ihave Opt := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 12)
    ((bytes32 ip ++ bytes32 ic) ++ bytes32 (UInt32.ofNat bs.length)) optTail (by simp [bytes32_length]) $$ [Opt OptTail]
  · iframe Opt OptTail
  ihave Vec := BorshFT.joinB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 4)
    (bytes32 ip) (bytes32 ic) (by simp) $$ [V0 V4]
  · iframe V0 V4
  ihave Vec := BorshFT.joinB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 8)
    (bytes32 ip ++ bytes32 ic) (bytes32 (UInt32.ofNat bs.length)) (by simp [bytes32_length]) $$ [Vec V8]
  · iframe Vec V8
  simp only [Post.mseq_normal]
  iapply (array_deref_parser_through_cleanup cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    ip ic idx len a live F bs tail (((bytes32 ip ++ bytes32 ic) ++ bytes32 (UInt32.ofNat bs.length)) ++ optTail)
    jsonRest derefOut j k ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic
    hinput (by simp [bytes32_length, hoptTail]) hderef hlen hptr ho hj hq he hk hend hmodel  hparserRoom
    halloc hob hstateTail hcontractTail hdestTail hA hB hout hhead h S st hv hroom hacc hlim hcanon hlink bud
    hproof hbudget hlimAccount hnone hreg ptr0 hret Φ)
  simp only [List.append_assoc] at *
  iframe HC66 H169 H646 F644 F66 F65 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi
    Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv Opt Hbs Htail Hesc Hutf Hhex HstateTail A0 A8 HdestTail B0 B8
    Hderef Vec HcontractTail Hob HD Hout Hhead HΦ

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The existing copied-only contract, preserved as a checked specialization. -/
theorem expect_deref_parser_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail optTail oldVec jsonRest derefOut : List UInt8) (j k : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
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
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (45 * cfg.regularOpCost + ((700 + 96 * wsLen (bs.drop k)) * cfg.regularOpCost +
          costArray cfg F 0 bs a.val.toUTF8.toList jsonRest j)) +
        parserSuccessCost cfg (copiedParserFree bs (j + 1) F) h S a R))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗
      n ↦[i32][ (s + 88).toNat ] ip ∗ n ↦[i32][ (s + 88).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 88).toNat + 8 ] UInt32.ofNat bs.length ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] oldVec ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        n ↦[i32][ (s + 24).toNat ] ip ∗ n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((copiedParserFree bs (j + 1) F + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 13).take 137) Φ := by
  exact array_expect_deref_parser_through_cleanup cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3 ip ic idx len a live F bs tail optTail oldVec jsonRest derefOut j k ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic hip hinput hoptTail holdVec hderef hlen hptr ho hj hq he hk hend hmodel hparserRoom halloc hob hstateTail hcontractTail hdestTail hA hB hout hhead h S st hv hroom hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ
end Spec
end WNear.Binary.BalanceOf297AbsentCall
