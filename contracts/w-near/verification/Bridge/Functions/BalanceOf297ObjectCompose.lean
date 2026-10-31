import Bridge.Functions.BalanceOf297ParserFamily
import Bridge.Functions.BalanceOf297ObjectParser
import Bridge.Functions.BalanceOf297CopiedBody

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

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
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_parser_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail parserOut : List UInt8) (jsonRest : List UInt8) (N : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hparserOut : parserOut.length = 16)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S))
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hnone : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = none)
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (hnb : (0x5C : UInt8) ∉ bs)
    (hL : len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, jsonRest))
    (hend : bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) = bs.length) :
    (SerdeObjectNoEsc.parserCode n inst mi A) ∗      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (1000 * cfg.regularOpCost +
        (SerdeObjectNoEsc.parserCost cfg F bs jsonRest N) +
        parserSuccessCost cfg (max F 1 + 1) h S a R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[wms][ (s + 88).toNat ] parserOut ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ (SerdeObjectNoEsc.parserStatics n) ∗
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
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ (SerdeObjectNoEsc.parserStatics n) ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live ((((((max F 1 + 1) + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [.i32 (s + 88), .i32 ip, .i32 (UInt32.ofNat bs.length)] ((f297.body.drop 35).take 115) Φ := by
  have hp := SerdeObjectNoEsc.parser_contract (GF := GF) cfg lim (d + 1) inst mi A n g ta Cg hm gt
    s (s + 88) ip idx parserOut bs jsonRest a N len F ((ip.toNat, ic.toNat) :: live)
    (by omega) hparserOut (by simp [UInt32.toNat_add]; omega) hlen hptr (by omega) hal hnb hL ho hloop hend
  exact parser_provider_through_cleanup cfg lim d inst e mi A n g ta mx hm (by omega) Cg R gt s x1 x2 x3
    ip ic idx len a live F bs tail parserOut (SerdeObjectNoEsc.parserCost cfg F bs jsonRest N) (max F 1 + 1)
    (SerdeObjectNoEsc.parserCode n inst mi A) (SerdeObjectNoEsc.parserStatics n)
    ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic hinput hparserOut
    hob hstateTail hcontractTail hdestTail hA hB hout hhead h S st hv hacc hlim hcanon hlink bud hproof hbudget
    hlimAccount hnone hreg ptr0 hret Φ hp

end WNear.Binary.BalanceOf297AbsentCall

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
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_deref_parser_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail parserOut jsonRest derefOut : List UInt8) (N : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hparserOut : parserOut.length = 16) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (hnb : (0x5C : UInt8) ∉ bs)
    (hL : len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, jsonRest))
    (hend : bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) = bs.length)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
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
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (SerdeObjectNoEsc.parserCost cfg F bs jsonRest N) +
        parserSuccessCost cfg ((max F 1 + 1)) h S a R)) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[wms][ (s + 88).toNat ] parserOut ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[wms][ (s + 24).toNat ] derefOut ∗
      n ↦[wms][ (s + 48).toNat ] (bytes32 ip ++ (bytes32 ic ++ bytes32 (UInt32.ofNat bs.length))) ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗
        n ↦[i32][ (s + 24).toNat ] ip ∗ n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live ((((((max F 1 + 1) + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 21).take 129) Φ := by
  iintro ⟨#HC66, #H169, #H646, #F644, #F66, #F65, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, HparserOut, Hbs, Htail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 21).take 129 =
      (f297.body.drop 21).take 14 ++ (f297.body.drop 35).take 115 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (deref_and_parser_setup cfg lim d inst mi A n hm.mem (hm.funcs 779 (by decide)) (by omega) Cg
    (1000 * cfg.regularOpCost +
      (SerdeObjectNoEsc.parserCost cfg F bs jsonRest N) +
      parserSuccessCost cfg ((max F 1 + 1)) h S a R)
    s x1 x2 x3 ip ic (UInt32.ofNat bs.length) derefOut hderef hframe)
  iframe Hi F779 Hc Hderef Hvec
  inext
  iintro ⟨Hc, P, L, Hvec⟩
  icases BorshFT.splitB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 4)
    (bytes32 ip) (bytes32 ic ++ bytes32 (UInt32.ofNat bs.length)) (by simp) $$ Hvec with ⟨I0, Irest⟩
  icases BorshFT.split64' (n := n) (a := (s + 48).toNat + 4) (b := (s + 48).toNat + 8)
    ic (UInt32.ofNat bs.length) (by omega) $$ Irest with ⟨I4, I8⟩
  simp only [Post.mseq_normal]
  iapply (object_parser_through_cleanup cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    ip ic idx len a live F bs tail parserOut jsonRest N ob stateTail contractTail destTail out head oldA oldB oldC oldD
    hs hal hframe hic hinput hparserOut hob hstateTail hcontractTail hdestTail hA hB hout hhead
    h S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ
    hlen hptr hnb hL ho hloop hend)
  iunfold SerdeObjectNoEsc.parserCode
  iframe HC66 H169 H646 F644 F66 F65 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi HIgn
    Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv HparserOut Hbs Htail Hesc Hutf Hhex HFr HstateTail A0 A8 HdestTail B0 B8
    I0 I4 I8 HcontractTail Hob HD Hout Hhead
  inext
  iintro %p %c Hpost
  icases Hpost with ⟨Hc, Hesc, Hutf, Hhex, HFr, Hg, Hinv, Hhost⟩
  ispecialize HΦ $$ %p %c
  iapply HΦ $$ [Hc P L Hesc Hutf Hhex HFr Hg Hinv Hhost]
  iframe Hc P L Hesc Hutf Hhex HFr Hg Hinv Hhost

end WNear.Binary.BalanceOf297AbsentCall

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
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_expect_deref_parser_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat)
    (bs tail optTail oldVec jsonRest derefOut : List UInt8) (N : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0) (hip : ip ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24) (hptr : ip.toNat + bs.length < 2 ^ 32)
    (hnb : (0x5C : UInt8) ∉ bs)
    (hL : len = InitialState.memLen ∨ len = VecFromElem.grownLen InitialState.memLen (UInt32.ofNat bs.length))
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, jsonRest))
    (hend : bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) = bs.length)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
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
    code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (SerdeObjectNoEsc.parserCost cfg F bs jsonRest N) +
        parserSuccessCost cfg ((max F 1 + 1)) h S a R))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗
      n ↦[i32][ (s + 88).toNat ] ip ∗ n ↦[i32][ (s + 88).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 88).toNat + 8 ] UInt32.ofNat bs.length ∗ n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live ((((((max F 1 + 1) + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 13).take 137) Φ := by
  iintro ⟨#HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, O0, O4, O8, HoptTail, Hbs, Htail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 13).take 137 =
      (f297.body.drop 13).take 8 ++ (f297.body.drop 21).take 129 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (input_expect cfg lim d inst mi A n hm.mem (hm.funcs 157 (by decide)) (by omega) Cg
    (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
      (SerdeObjectNoEsc.parserCost cfg F bs jsonRest N) +
      parserSuccessCost cfg ((max F 1 + 1)) h S a R))
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
  iapply (object_deref_parser_through_cleanup cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    ip ic idx len a live F bs tail (((bytes32 ip ++ bytes32 ic) ++ bytes32 (UInt32.ofNat bs.length)) ++ optTail)
    jsonRest derefOut N ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic
    hinput (by simp [bytes32_length, hoptTail]) hderef hlen hptr hnb hL ho hloop hend hob hstateTail hcontractTail hdestTail hA hB hout hhead h S st hv hacc hlim hcanon hlink bud
    hproof hbudget hlimAccount hnone hreg ptr0 hret Φ)
  simp only [List.append_assoc] at *
  iframe HC66 H169 H646 F644 F66 F65 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi HIgn
    Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv Opt Hbs Htail Hesc Hutf Hhex HFr HstateTail A0 A8 HdestTail B0 B8
    Hderef Vec HcontractTail Hob HD Hout Hhead HΦ

end WNear.Binary.BalanceOf297AbsentCall

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
theorem object_input_parser_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (N : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24)
    (hnb : (0x5C : UInt8) ∉ bs) (hbase : len = InitialState.memLen)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, jsonRest))
    (hend : bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) = bs.length)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : RegOk 2048 len (some bs))
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
    inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (SerdeObjectNoEsc.parserCost cfg 1 bs jsonRest N) +
        parserSuccessCost cfg (2) h S a R)))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
      n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        (∃ ip : UInt32, n ↦[i32][ (s + 24).toNat ] ip) ∗
        n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((2 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [.i32 (s + 88)] ((f297.body.drop 12).take 138) Φ := by
  iintro ⟨#Hin, #F527, #HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 12).take 138 = [.call 527] ++ (f297.body.drop 13).take 137 := by rfl
  rw [hseg]
  iapply mwpi_seq
  icases stk_split n (s.toNat - 592) 432 160 $$ Hstk with ⟨Hlo, Hstk⟩
  ihave Hstk := stk_addr (show s.toNat - 592 + 432 = s.toNat - 160 by omega) $$ Hstk
  have hn := hm.mem
  have ha527 := hm.funcs 527 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have S527 := f527_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
    s (s + 88) (by omega) hal (by simp [UInt32.toNat_add]; omega) idx 2048 len live oldOpt hopt h0
    (by simpa [hinput] using hinputLimit) (by simpa [hinput] using hok)
  mcall S527 using [Hg HI Hstk Hvt Hinv Hopt Hhost] with (mstep_norm_full; omega)
  · iunfold pre527
    iframe Hg HI Hstk Hvt Hinv Hopt Hhost
    ipureintro; rfl
  iunfold post527 at HQ
  rw [hinput, hafter]
  icases HQ with ⟨%hrs, Hg, HI, Hstk, Hvt, Hopt, Hhost⟩
  subst hrs
  iunfold optVecAt at Hopt
  icases Hopt with ⟨%ip, O0, O4, O8, %len', %⟨hip, hstep⟩, Hinv, Hbs⟩
  iunfold ifaceI at HI
  icases HI with ⟨HI, Hslot⟩
  ihave Hstk := stk_addr (show s.toNat - 160 = s.toNat - 592 + 432 by omega) $$ Hstk
  ihave Hstk := stk_join n (s.toNat - 592) 432 160 $$ [Hlo Hstk]
  · iframe Hlo Hstk
  have hpos : 0 < bs.length := hok.1
  have hnlen : (UInt32.ofNat bs.length).toNat = bs.length := by
    simp only [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hic : UInt32.ofNat bs.length ≠ 0 := by
    intro hz
    have hz' := congrArg UInt32.toNat hz
    rw [hnlen] at hz'
    simp at hz'
    simp [hz'] at hpos
  ihave Hinv := AllocZeroed.heapInv_bound n 2048 len' _ 1 $$ Hinv
  icases Hinv with ⟨%⟨hbound, hlen32⟩, Hinv⟩
  have hptr : ip.toNat + bs.length < 2 ^ 32 := by
    have hx := hbound ip.toNat bs.length (by simp)
    omega
  have hL' : len' = InitialState.memLen ∨ len' = grownLen InitialState.memLen (UInt32.ofNat bs.length) := by
    simpa only [hbase] using hstep
  ihave Htail : n ↦[wms][ ip.toNat + bs.length ] ([] : List UInt8) $$ []
  · iapply ScratchGrow.memBytes_nil
  have Hnext := object_expect_deref_parser_through_cleanup cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    ip (UInt32.ofNat bs.length) idx len' a live 1 bs [] optTail oldVec jsonRest derefOut N
    ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic hip
    (by simp [hnlen]) hoptTail holdVec hderef hlen hptr hnb hL' ho hloop hend hob hstateTail hcontractTail hdestTail hA hB hout hhead
    h S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ
  simp only [Nat.max_self, Nat.reduceAdd] at Hnext
  iapply Hnext
  unfold cost527 at *
  simp only [hnlen]
  iframe HC66 H169 H646 F644 F66 F65 F157 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456
    Hdrop F68 HIC Hi HIgn Hg HI Hstk Hvt Hstatekey Hhost Hinv O0 O4 O8 HoptTail Hbs Htail Hesc Hutf Hhex HFr
    HstateTail A0 A8 HdestTail B0 B8 Hderef Hvec HcontractTail Hob HD Hout Hhead
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro %p %c Hpost
  icases Hpost with ⟨Hc, P, L, Hesc, Hutf, Hhex, HFr, Hg, Hinv, Hhost⟩
  ispecialize HΦ $$ %p %c
  iapply HΦ $$ [Hc P L Hesc Hutf Hhex HFr Hg Hinv Hhost]
  iframe Hc L Hesc Hutf Hhex HFr Hg Hinv Hhost
  iexists ip
  iexact P

end WNear.Binary.BalanceOf297AbsentCall

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
theorem object_input_setup_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (N : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24)
    (hnb : (0x5C : UInt8) ∉ bs) (hbase : len = InitialState.memLen)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, jsonRest))
    (hend : bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) = bs.length)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : RegOk 2048 len (some bs))
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
    inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (SerdeObjectNoEsc.parserCost cfg 1 bs jsonRest N) +
        parserSuccessCost cfg (2) h S a R))))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceI n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
      n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        (∃ ip : UInt32, n ↦[i32][ (s + 24).toNat ] ip) ∗
        n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((2 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 9).take 141) Φ := by
  iintro ⟨#Hin, #F527, #HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 9).take 141 =
      [.local_get 0, .i32_const 88, .i32_binop .add] ++ (f297.body.drop 12).take 138 := by rfl
  rw [hseg]
  iapply mwpi_seq
  mstep; mstep; mstep
  iapply (object_input_parser_through_cleanup cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    idx len a live bs oldOpt optTail oldVec jsonRest derefOut N ob stateTail contractTail destTail out head
    oldA oldB oldC oldD hs hal hframe hopt hoptTail holdVec hderef hlen hnb hbase ho hloop hend hob hstateTail hcontractTail hdestTail hA hB hout hhead h0 h hinput hafter hinputLimit hok
    S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ)
  iframe Hin F527 HC66 H169 H646 F644 F66 F65 F157 HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456
    Hdrop F68 HIC Hi HIgn Hc Hg HI Hstk Hvt Hstatekey Hhost Hinv Hopt HoptTail Hesc Hutf Hhex HFr HstateTail
    A0 A8 HdestTail B0 B8 Hderef Hvec HcontractTail Hob HD Hout Hhead HΦ

end WNear.Binary.BalanceOf297AbsentCall

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
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem object_absent_body (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 46 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat))
    (bs oldOpt optTail oldVec jsonRest derefOut : List UInt8) (N : Nat)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD hookOld k3 : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 < 2 ^ 32)
    (hopt : oldOpt.length = 12) (hoptTail : optTail.length = 4) (holdVec : oldVec.length = 12) (hderef : derefOut.length = 8)
    (hlen : bs.length < 2 ^ 24)
    (hnb : (0x5C : UInt8) ∉ bs) (hbase : len = InitialState.memLen)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : WNear.SerdeStructModel.objLoop "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      WNear.IgnoreShallow.ign1R N none (bs.drop (wsLen bs + 1)) = some (some a, jsonRest))
    (hend : bs.length - jsonRest.length + wsLen (bs.drop (bs.length - jsonRest.length)) = bs.length)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h0 h : NearState) (hinput : h0.context.input = bs) (hafter : inputHost h0 0 = h)
    (hinputLimit : withinLimit h0.config.maxRegisterLen bs.length = true) (hok : RegOk 2048 len (some bs))
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
    codeA inst mi A ∗ inCode e inst mi A n 2048 mx ∗ A 527 ↪[wf] FuncInst.wasm types[0]! inst f527 ∗ code66 n 2048 inst mi A ∗ SerdeAccountId.code169 n 2048 inst mi A ∗ ParseStr.code646 n 2048 inst mi A ∗
      A 644 ↪[wf] FuncInst.wasm types[31]! inst f644 ∗ A 66 ↪[wf] FuncInst.wasm types[14]! inst f66 ∗
      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗ SerdeIgnValue.code81 inst mi A ∗
      credits Cg (475 * cfg.regularOpCost + (3 * cfg.regularOpCost + (100 * cfg.regularOpCost + cost527 cfg h0 + (100 * cfg.regularOpCost + (100 * cfg.regularOpCost + (1000 * cfg.regularOpCost +
        (SerdeObjectNoEsc.parserCost cfg 1 bs jsonRest N) +
        parserSuccessCost cfg (2) h S a R)))))) ∗
      g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ stk n (s.toNat - 592) 592 ∗
      hookCells n 0 hookOld 0 ∗ n ↦[i32][ 1055020 ] 116 ∗
      ta ↦[wt][ 116 ] Ref.func (A 565) ∗ ta ↦[wt][ 106 ] Ref.func (A 564) ∗
      blockchainInterfaceCells n 0 0 0 k3 ∗ vtab n ta A ∗
      n ↦[wms][ 1050188 + 36 ] dataWord (1050188 + 36) ∗ ta ↦[wt][ 44 ] Ref.func (A 246) ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h0 ∗
      heapInv n 2048 len live 1 ∗ n ↦[wms][ (s + 88).toNat ] oldOpt ∗
      n ↦[wms][ (s + 100).toNat ] optTail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗
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
        (∃ ip : UInt32, n ↦[i32][ (s + 24).toNat ] ip) ∗
        n ↦[i32][ (s + 24).toNat + 4 ] UInt32.ofNat bs.length ∗
        n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ SerdeObjectNoEsc.parserStatics n ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((2 + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d ⟨#[.i32 0, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩ [] f297.body Φ := by
  iintro ⟨#HA, #Hin, #F527, #HC66, #H169, #H646, #F644, #F66, #F65, #F157, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, #HIgn, Hc, Hg, Hstk, Hhook, Hsetupkey, T116, T106,
    HB, HV, V36, T44, Hvt, Hstatekey, Hhost, Hinv, Hopt, HoptTail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, Hderef, Hvec, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hf := SerdeObjectNoEsc.parser_family (GF := GF) cfg lim inst mi A n g ta hm gt bs jsonRest a N 1 hnb ho hloop hend
  have hp := provider_absent_body (GF := GF) cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    idx len a live bs oldOpt optTail oldVec derefOut (SerdeObjectNoEsc.parserCost cfg 1 bs jsonRest N) 2
    (SerdeObjectNoEsc.parserCode n inst mi A) ob stateTail contractTail destTail out head oldA oldB oldC oldD hookOld k3
    hs hal hframe hopt hoptTail holdVec hderef hlen hbase hob hstateTail hcontractTail hdestTail hA hB hout hhead
    h0 h hinput hafter hinputLimit hok S st hv hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ hf
  iapply hp
  isplitr
  · iunfold SerdeObjectNoEsc.parserCode
    iframe HC66 H169 H646 Hdrop HIgn F644 F66 Hi
  iframe HA Hin F527 HC66 H169 H646 F644 F66 F65 F157 HSC F219 F155 F951 HC F293 HTV
    F96 F158 F779 F545 F456 Hdrop F68 HIC Hi HIgn Hc Hg Hstk Hhook Hsetupkey T116 T106
    HB HV V36 T44 Hvt Hstatekey Hhost Hinv Hopt HoptTail Hesc Hutf Hhex HFr HstateTail
    A0 A8 HdestTail B0 B8 Hderef Hvec HcontractTail Hob HD Hout Hhead HΦ

end WNear.Binary.BalanceOf297AbsentCall
