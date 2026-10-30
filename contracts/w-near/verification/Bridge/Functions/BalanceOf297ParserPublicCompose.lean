import Bridge.Functions.BalanceOf297ParserFixedCompose

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
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
/-- Gas reserved for the checked success-to-cleanup path, at the actual free-list bound. -/
noncomputable def parserSuccessCost (cfg : WasmConfig) (F : Nat) (h : NearState) (S : WNear.State)
    (a : WNear.AccountId) (R : Nat) : Nat :=
  400 * cfg.regularOpCost + (800 * cfg.regularOpCost + cost219F cfg (F + 1) h S +
    (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost +
      cost399None cfg ((F + 1) + 1) 1 (UInt32.ofNat a.val.utf8ByteSize) h
        (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) +
      (17 * cfg.regularOpCost + cost96F cfg (((F + 1) + 1) + 3) 0 0 +
        (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h 3 + (660 * cfg.regularOpCost + R)))))))

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
/-- Unresolved resource fact at the actual heap hidden by the public parser result.
It must return the same owned parser result and prove six-growth room and a gas upper bound. -/
def ParserPostBudget (cfg : WasmConfig) (n : Nat) (out : UInt32) (a : WNear.AccountId)
    (live : List (Nat × Nat)) (h : NearState) (S : WNear.State) (R K : Nat) : IProp GF :=
  iprop(∀ len F, okAtFixed n out a live len F -∗
    ⌜HeapRoomK 6 len 2048 ∧ parserSuccessCost cfg F h S a R ≤ K⌝ ∗ okAtFixed n out a live len F)

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
theorem parser_result_through_cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst e : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R K : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (ip ic il idx : UInt32) (a : WNear.AccountId) (live : List (Nat × Nat))
    (ob stateTail contractTail destTail out head oldA oldB : List UInt8) (oldC oldD : UInt32) (hs : 592 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hic : ic ≠ 0)
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
    stateCodeF e inst mi A n 2048 mx ∗ A 219 ↪[wf] FuncInst.wasm types[0]! inst f219 ∗
      A 155 ↪[wf] FuncInst.wasm types[14]! inst f155 ∗ A 951 ↪[wf] FuncInst.wasm types[15]! inst f951 ∗
      code293 e n 2048 inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n 2048 inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg K ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ ifaceR n ta A ∗ stk n (s.toNat - 592) 592 ∗
      vt n 1057464 idx ta (A 578) ∗ n ↦[wms][ 1049788 ] StateRead.stateKey ∗ mhostPt h ∗
      FromSliceSpec.okAt n (s + 88) a ((ip.toNat, ic.toNat) :: live) ∗
      ParserPostBudget cfg n (s + 88) a ((ip.toNat, ic.toNat) :: live) h S R K ∗
      n ↦[wms][ (s + 104).toNat ] stateTail ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 140).toNat ] destTail ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 48).toNat + 8 ] il ∗ n ↦[wms][ (s + 60).toNat ] contractTail ∗
      block n ip.toNat ic.toNat ∗ n ↦[wms][ (s + 8).toNat ] ob ∗
      tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ F : Nat, ∀ p : UInt32, ∀ c : UInt32, credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗ (∃ hl, heapInv n 2048 hl live (((((F + 1) + 1) + 3) + 1 + 1) + 1)) ∗
        (∃ h1, ⌜StorageReadPost h WNear.stateKey 0 st h1⌝ ∗
          ∃ st1 h2, ⌜StorageReadPost h1 (WNear.accountsPrefix ++ (bytes32 (UInt32.ofNat a.val.utf8ByteSize) ++ a.val.toUTF8.toList)) 0 st1 h2⌝ ∗
            mhostPt (h2.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s (UInt32.ofNat a.val.utf8ByteSize) (VecFromElem.pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 36).take 114) Φ := by
  iintro ⟨#HSC, #F219, #F155, #F951, #HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456,
    #Hdrop, #F68, #HIC, #Hi, Hc, Hg, HI, Hstk, Hvt, Hstatekey, Hhost, Hparser, HbudgetReady, HstateTail,
    A0, A8, HdestTail, B0, B8, I0, I4, I8, HcontractTail, Hb, Hob, HD, Hout, Hhead, HΦ⟩
  ihave Hparser := okAt_expose n (s + 88) a ((ip.toNat, ic.toNat) :: live) $$ Hparser
  icases Hparser with ⟨%len, %F, Hparser⟩
  iunfold ParserPostBudget at HbudgetReady
  ispecialize HbudgetReady $$ %len %F Hparser
  icases HbudgetReady with ⟨%⟨hroom, hcost⟩, Hparser⟩
  iapply (parser_fixed_through_cleanup cfg lim d inst e mi A n g ta mx hm hd Cg R gt s x1 x2 x3
    ip ic il idx len a live F ob stateTail contractTail destTail out head oldA oldB oldC oldD
    hs hal hframe hic hob hstateTail hcontractTail hdestTail hA hB hout hhead h S st hv hroom
    hacc hlim hcanon hlink bud hproof hbudget hlimAccount hnone hreg ptr0 hret Φ)
  iframe HSC F219 F155 F951 HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi Hg HI Hstk Hvt
    Hstatekey Hhost Hparser HstateTail A0 A8 HdestTail B0 B8 I0 I4 I8 HcontractTail Hb Hob HD Hout Hhead
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    exact hcost
  inext
  iintro %p %c Hpost
  ispecialize HΦ $$ %F %p %c Hpost
  iexact HΦ
end Spec
end WNear.Binary.BalanceOf297AbsentCall
