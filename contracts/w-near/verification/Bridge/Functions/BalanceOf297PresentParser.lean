import Bridge.Functions.BalanceOf297PresentState

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (parser_handoff cost219F)
open WNear.Binary.BalanceOfPresent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem parser_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (p c L ip ic il idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (lo hi : UInt64)
    (key rest ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hic : ic ≠ 0) (hL : L.toNat + 4 ≤ 120) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hroom : HeapRoomK 7 len maxP)
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 L ++ key)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 L ++ key)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 L ++ key)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n maxP mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (400 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost219F cfg (F + 1) h S +
        (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + cost399 cfg ((F + 1) + 1) 1 L h (WNear.accountsPrefix ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
          (17 * cfg.regularOpCost + cost96F cfg (((F + 1) + 1) + 4) lo hi +
            (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R)))))))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] p ∗
      n ↦[i32][ (s + 88).toNat + 8 ] c ∗ n ↦[i32][ (s + 88).toNat + 12 ] L ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 48).toNat + 8 ] il ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      block n ip.toNat ic.toNat ∗ heapInv n maxP len ((ip.toNat, ic.toNat) :: (p.toNat, c.toNat) :: live) F ∗
      n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ p.toNat + key.length ] rest ∗ n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n maxP hl live (((((F + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 L ++ key)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s L (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 36).take 114) Φ := by
  iintro ⟨#HSC, #F219, #F155, #F951, #HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456,
    #Hdrop, #F68, #HIC, #Hi, Hc, Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Tag, P, C, L0, HstateTail,
    A0, A8, HdestTail, B0, B8, I0, I4, I8, HcontractTail, Hb, Hinv, Hkey, Hrest, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 36).take 114 =
      (f297.body.drop 36).take 32 ++ (f297.body.drop 68).take 82 := by rfl
  rw [hseg]
  have hframeEq : ∀ a b c, frame inst mi s a b c = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s a b c := fun _ _ _ => rfl
  simp only [hframeEq]
  iapply mwpi_seq
  iapply (parser_handoff cfg lim d inst mi A n g ta hm (by omega) Cg
    (800 * cfg.regularOpCost + cost219F cfg (F + 1) h S +
      (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + cost399 cfg ((F + 1) + 1) 1 L h
        (WNear.accountsPrefix ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
        (17 * cfg.regularOpCost + cost96F cfg (((F + 1) + 1) + 4) lo hi +
          (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R)))))))
    s x1 x2 x3 p c L ip ic il maxP len F live oldA oldB oldC oldD hA hB hic hframe (by omega))
  iframe Hdrop F68 Hc Tag P C L0 A0 A8 B0 B8 I0 I4 I8 Hb Hinv
  inext
  iintro ⟨Hc, Tag, PC, L0, A0, A8, B0, B8, I0, I4, I8, Hinv⟩
  ihave StateTail := AllocNewCell.memBytes_addr (show (s + 104).toNat = (s + 88).toNat + 16 by
    simp [UInt32.toNat_add]; omega) $$ HstateTail
  ihave DestTail := AllocNewCell.memBytes_addr (show (s + 140).toNat = (s + 128).toNat + 12 by
    simp [UInt32.toNat_add]; omega) $$ HdestTail
  ihave ContractTail := AllocNewCell.memBytes_addr (show (s + 60).toNat = (s + 48).toNat + 12 by
    simp [UInt32.toNat_add]; omega) $$ HcontractTail
  ihave State0 := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 4)
    (bytes32 0) (bytes32 p ++ bytes32 c) (by simp) $$ [Tag PC]
  · iframe Tag PC
  ihave State0 := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 12)
    (bytes32 0 ++ (bytes32 p ++ bytes32 c)) (bytes32 L) (by simp [bytes32_length]) $$ [State0 L0]
  · iframe State0 L0
  ihave State0 := BorshFT.joinB (n := n) (a := (s + 88).toNat) (b := (s + 88).toNat + 16)
    (bytes32 0 ++ (bytes32 p ++ bytes32 c) ++ bytes32 L) stateTail (by simp [bytes32_length]) $$ [State0 StateTail]
  · iframe State0 StateTail
  ihave Dest0 := BorshFT.joinB (n := n) (a := (s + 128).toNat) (b := (s + 128).toNat + 8)
    (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32_length]) $$ [A0 A8]
  · iframe A0 A8
  ihave Dest0 := BorshFT.joinB (n := n) (a := (s + 128).toNat) (b := (s + 128).toNat + 12)
    ((bytes32 p ++ bytes32 c) ++ bytes32 L) destTail (by simp [bytes32_length]) $$ [Dest0 DestTail]
  · iframe Dest0 DestTail
  ihave Source := BorshFT.joinB (n := n) (a := (s + 32).toNat) (b := (s + 32).toNat + 8)
    (bytes32 p ++ bytes32 c) (bytes32 L) (by simp [bytes32_length]) $$ [B0 B8]
  · iframe B0 B8
  ihave Input0 := BorshFT.joinB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 4)
    (bytes32 ip) (bytes32 ic) (by simp) $$ [I0 I4]
  · iframe I0 I4
  ihave Input0 := BorshFT.joinB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 8)
    (bytes32 ip ++ bytes32 ic) (bytes32 il) (by simp [bytes32_length]) $$ [Input0 I8]
  · iframe Input0 I8
  ihave Input0 := BorshFT.joinB (n := n) (a := (s + 48).toNat) (b := (s + 48).toNat + 12)
    ((bytes32 ip ++ bytes32 ic) ++ bytes32 il) contractTail (by simp [bytes32_length]) $$ [Input0 ContractTail]
  · iframe Input0 ContractTail
  ihave HP : pre219F n g ta A gt s (s + 88) idx maxP len ((p.toNat, c.toNat) :: live) (F + 1)
      ((bytes32 0 ++ (bytes32 p ++ bytes32 c) ++ bytes32 L) ++ stateTail) h [.i32 (s + 88)] $$
      [Hg HI Hstk Hvt Hinv State0 Hstatekey Hhost]
  · iunfold pre219F
    iframe Hg HI Hstk Hvt Hinv State0 Hstatekey Hhost
    ipureintro; rfl
  simp only [Post.mseq_normal]
  rw [← hframeEq]
  iapply (state_through_cleanup_present_seven_growsF cfg lim d inst e mi A n g ta mx hm hd Cg R gt s L
    (VecFromElem.pair64 p c) p c L idx maxP len live (F + 1) (by unfold VecWithCap.okG; omega) lo hi
    key rest ob ((bytes32 0 ++ (bytes32 p ++ bytes32 c) ++ bytes32 L) ++ stateTail)
    (((bytes32 ip ++ bytes32 ic) ++ bytes32 il) ++ contractTail)
    (((bytes32 p ++ bytes32 c) ++ bytes32 L) ++ destTail) out head hs hal hframe hkey hrest hc hL hp
    hob (by simp [bytes32_length, hstateTail]) (by simp [bytes32_length, hcontractTail])
    (by simp [bytes32_length, hdestTail]) hout hhead h S st hv hroom hacc hlim hcanon hlink bud hproof hbudget
    hlimAccount hsome hreg ptr0 hret Φ)
  simp only [List.append_assoc] at *
  iframe HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi Hc HP Input0 Source
    Hkey Hrest Hob Dest0 HD Hout Hhead HΦ
end Spec
end WNear.Binary.BalanceOf297PresentCall

/-! Compose the decoded parser success handoff with state read and absent balance cleanup. -/
namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (okAtFixed parser_fixed_resources cost219F)
open WNear.Binary.BalanceOfPresent (code293)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem parser_fixed_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic il idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat) (lo hi : UInt64)
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
    (hob : ob.length = 16) (hstateTail : stateTail.length = 24) (hcontractTail : contractTail.length = 28)
    (hdestTail : destTail.length = 4) (hA : oldA.length = 8) (hB : oldB.length = 8) (hout : out.length = 12) (hhead : head.length = 8)
    (h : NearState) (S : WNear.State) (st : Near.TrieOverlay.State)
    (hv : h.storage WNear.stateKey = some (WNear.header S)) (hroom : HeapRoomK 7 len 2048)
    (hacc : h.storageAccounting = some st) (hlim : withinLimit h.config.maxStorageKeyLen 5 = true)
    (hcanon : Canon st) (hlink : StorageLink h st) (bud : Nat) (hproof : ProofBudget h st bud)
    (hbudget : readProofCost (contractKey h.context.currentAccountId WNear.stateKey) (h.storage WNear.stateKey) +
      readProofCost (contractKey h.context.currentAccountId (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)))
        (h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList))) ≤ bud)
    (hlimAccount : withinLimit h.config.maxStorageKeyLen (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)).length = true)
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF) :
    stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (400 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost219F cfg (F + 1) h S +
        (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + cost399 cfg ((F + 1) + 1) 1 (UInt32.ofNat a.val.utf8ByteSize) h (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (u128Bytes lo hi) +
          (17 * cfg.regularOpCost + cost96F cfg (((F + 1) + 1) + 4) lo hi +
            (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R)))))))) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      okAtFixed n (s + 88) a ((ip.toNat, ic.toNat) :: live) len F ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 48).toNat + 8 ] il ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      block n ip.toNat ic.toNat ∗ n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((F + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 36).take 114) Φ := by
  iintro ⟨#HSC, #F219, #F155, #F951, #HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456,
    #Hdrop, #F68, #HIC, #Hi, Hc, Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Hparser, HstateTail,
    A0, A8, HdestTail, B0, B8, I0, I4, I8, HcontractTail, Hb, Hob, HD, Hout, Hhead, HΦ⟩
  ihave Hparser := parser_fixed_resources n (s + 88) a ip ic live len F $$ Hparser
  icases Hparser with ⟨%p, %c, %rest, %⟨hc, hkey, hrest, hL, hp⟩, Tag, P, C, L0, Hkey, Hrest, Hinv⟩
  iapply (parser_through_cleanup_present cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    p c (UInt32.ofNat a.val.utf8ByteSize) ip ic il idx 2048 len live F lo hi
    a.val.toUTF8.toList rest ob stateTail contractTail destTail out head oldA oldB oldC oldD
    hs hal hframe hkey hrest hc hic hL hp hob hstateTail hcontractTail hdestTail hA hB hout hhead
    h S st hv hroom hacc hlim hcanon hlink bud hproof hbudget hlimAccount hsome hreg ptr0 hret Φ)
  iframe HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi Hc Hg HI Hstk Hvt
    Hstatekey Hhost Tag P C L0 HstateTail A0 A8 HdestTail B0 B8 I0 I4 I8 HcontractTail Hb Hinv Hkey Hrest
    Hob HD Hout Hhead
  inext
  ispecialize HΦ $$ %p %c
  iexact HΦ
end Spec
end WNear.Binary.BalanceOf297PresentCall

/-! Escape-free object refinement: checked parser, linear resources and caller composition.
The completed receipt case is limited explicitly to 4 MiB and shallow ignored values. -/

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.StateReadLenF (stateCodeF pre219F)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.BalanceOf297AbsentCall (okAtFixed cost219F)
open WNear.Binary.BalanceOfPresent (code293)
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
noncomputable def presentParserSuccessCost (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State)
    (a : WNear.AccountId) (lo hi : UInt64) (R : Nat) : Nat :=
  400 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost219F cfg (F + 1) h S +
    (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost +
      cost399 cfg ((F + 1) + 1) 1 (UInt32.ofNat a.val.utf8ByteSize) h
        (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) (u128Bytes lo hi) +
      (17 * cfg.regularOpCost + cost96F cfg (((F + 1) + 1) + 4) lo hi +
        (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R)))))))

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The exact successful parser call consumed by balance execution, including retained resources and heap room. -/
def PresentParserCallContract (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta Cg : Nat) (gt : GlobalType) (sp out ptr idx : UInt32)
    (ob bs : List UInt8) (a : WNear.AccountId) (len : Nat) (live : List (Nat × Nat))
    (F parseGas outF : Nat) (Cd Fr : IProp GF) : Prop :=
  Cd ⊢ MFunSpec cfg lim d types[31]! inst mi f65 Cg
    (fun args => iprop(⌜args = [.i32 out, .i32 ptr, .i32 (UInt32.ofNat bs.length)]⌝ ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗ vt n 1057464 idx ta (A 578) ∗
      heapInv n 2048 len live F ∗ n ↦[wms][ out.toNat ] ob ∗ n ↦[wms][ ptr.toNat ] bs ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr))
    (fun _ => parseGas)
    (fun _ rs => iprop(⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 448) 448 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ ptr.toNat ] bs ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ∗
      ∃ hl', ⌜HeapRoomK 7 hl' 2048⌝ ∗ okAtFixed n out a live hl' outF))

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem parser_provider_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 39 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic idx : UInt32) (len : Nat) (a : WNear.AccountId) (live : List (Nat × Nat)) (F : Nat) (lo hi : UInt64)
    (bs tail parserOut : List UInt8) (parseGas outF : Nat) (Cd Fr : IProp GF) [Persistent Cd]
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
    (hinput : bs.length + tail.length = ic.toNat) (_hparserOut : parserOut.length = 16)
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
    (hsome : h.storage (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) = some (u128Bytes lo hi))
    (hreg : withinLimit h.config.maxRegisterLen 29 = true)
    (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF)
    (hParser : PresentParserCallContract cfg lim (d + 1) inst mi A n g ta Cg gt s (s + 88) ip idx
      parserOut bs a len ((ip.toNat, ic.toNat) :: live) F parseGas outF Cd Fr) :
    Cd ∗      A 65 ↪[wf] FuncInst.wasm types[31]! inst f65 ∗ stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (1000 * cfg.regularOpCost +
        parseGas +
        presentParserSuccessCost cfg outF h S a lo hi R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      heapInv n 2048 len ((ip.toNat, ic.toNat) :: live) F ∗ n ↦[wms][ (s + 88).toNat ] parserOut ∗
      n ↦[wms][ ip.toNat ] bs ∗ n ↦[wms][ ip.toNat + bs.length ] tail ∗
      n ↦[wms][ 1062392 ] ParseStr.escTable ∗ n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗
      n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ∗
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
        n ↦[wms][ 1062712 ] SerdeEsc.hexTable ∗ Fr ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((outF + 1) + 1) + 4) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [.i32 (s + 88), .i32 ip, .i32 (UInt32.ofNat bs.length)] ((f297.body.drop 35).take 115) Φ := by
  iintro ⟨#HCd, #F65, #HSC, #F219, #F155, #F951, #HC, #F293, #HTV,
    #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi, Hc, Hg, HI, Hstk, Hvt,
    Hstatekey, Hhost, Hinv, HparserOut, Hbs, Htail, Hesc, Hutf, Hhex, HFr, HstateTail,
    A0, A8, HdestTail, B0, B8, I0, I4, I8, HcontractTail, Hob, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 35).take 115 = [.call 65] ++ (f297.body.drop 36).take 114 := by rfl
  rw [hseg]
  iapply mwpi_seq
  icases stk_split n (s.toNat - 592) 144 448 $$ Hstk with ⟨Hlo, Hstk⟩
  ihave Hstk := stk_addr (show s.toNat - 592 + 144 = s.toNat - 448 by omega) $$ Hstk
  have hn := hm.mem
  have ha65 := hm.funcs 65 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have hs65 := hParser
  unfold PresentParserCallContract at hs65
  ihave #S65 := hs65 $$ HCd
  mcall S65 using [Hg Hstk Hvt Hinv HparserOut Hbs Hesc Hutf Hhex HFr]
    with (unfold presentParserSuccessCost; mstep_norm_full; omega)
  · iframe Hg Hstk Hvt Hinv HparserOut Hbs Hesc Hutf Hhex HFr
  icases HQ with ⟨%hrs, Hg, Hstk, Hvt, Hbs, Hesc, Hutf, Hhex, HFr, %len', %hroom', Hparser⟩
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
  iapply (parser_fixed_through_cleanup_present cfg lim d inst e mi A n g ta mx hm (by omega) Cg R gt s x1 x2 x3
    ip ic (UInt32.ofNat bs.length) idx len' a live outF lo hi
    ob stateTail contractTail destTail out head oldA oldB oldC oldD hs hal hframe hic hob hstateTail
    hcontractTail hdestTail hA hB hout hhead h S st hv hroom' hacc hlim hcanon hlink bud hproof hbudget
    hlimAccount hsome hreg ptr0 hret Φ)
  unfold presentParserSuccessCost at *
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
  iapply HΦ $$ [Hc Hesc Hutf Hhex HFr Hg Hinv Hhost]
  simp only [List.cons_append, List.nil_append]
  iframe Hc Hesc Hutf Hhex HFr Hg Hinv Hhost

end Spec

end WNear.Binary.BalanceOf297PresentCall
