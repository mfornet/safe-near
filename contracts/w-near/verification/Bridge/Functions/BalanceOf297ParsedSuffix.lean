import Bridge.Functions.BalanceOf297ArgumentCopy

/-! Connect the parsed string descriptor to the checked absent-balance suffix. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293 pre293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- From a parsed account string through the absent-account result and epilogue. -/
theorem parsed_account_through_cleanup_absent (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (pre key rest ob dest tail out head padding old : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8) (hold : old.length = 12) (hpadding : pre.length + padding.length = pc.toNat) (hpc : pc ≠ 0)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 4 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hnone : h.storage (pre ++ (bytes32 L ++ key)) = none) (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen 3 = true) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 3) 0 0 +
          (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h 3 + (660 * cfg.regularOpCost + R)))))) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 32) p c L
        idx maxP len ((pp.toNat, pc.toNat) :: live) F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 32)] ∗
      n ↦[wms][ (s + 88).toNat ] old ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      n ↦[wms][ pp.toNat + pre.length ] padding ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗
        (∃ hl', heapInv n maxP hl' live (((F + 3) + 1 + 1) + 1)) ∗
        (∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗
          mhostPt (h'.selectReturnValue [34, 48, 34])) -∗
        Φ.normal [] (frame inst mi s x1 x2 (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 (s + 40)) [] ((f297.body.drop 79).take 71) Φ := by
  iintro ⟨#HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi,
    Hc, HP, Hold, Hextra, Htail, Hdest, HD, Hout, Hhead, Hpad, HΦ⟩
  have hseg : (f297.body.drop 79).take 71 =
      (f297.body.drop 79).take 12 ++ (f297.body.drop 91).take 59 := by rfl
  rw [hseg]
  iunfold pre293 at HP
  icases HP with ⟨%hargs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hsrc, Hkey, Hrest, Hob, Hhost⟩
  iapply mwpi_seq
  iapply (argument_copy cfg lim d inst mi n hm.mem Cg
    (2112 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)) +
      (17 * cfg.regularOpCost + cost96F cfg (F + 3) 0 0 +
        (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h 3 + (660 * cfg.regularOpCost + R)))))
    s x1 x2 p c L old hold hframe)
  iframe Hc Hsrc Hold
  inext
  iintro ⟨Hc, Hsrc, Harg⟩
  ihave HP : pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
      idx maxP len ((pp.toNat, pc.toNat) :: live) F pre key rest ob h
      [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] $$ [Hg Hs HI Hvt Hinv Hm Hp Harg Hkey Hrest Hob Hhost]
  · iunfold pre293
    iframe Hg Hs HI Hvt Hinv Hm Hp Harg Hkey Hrest Hob Hhost
    ipureintro; rfl
  simp only [Post.mseq_normal]
  iapply (call_through_cleanup_absent cfg lim d inst mi e A n g ta mx hm hd Cg R gt s x1 x2 (s + 40)
    pp pc pl p c L idx maxP len live F hF pre key rest ob dest tail out head padding hs hal hframe hob hdest htail
    hout hhead hpadding hpc hpre hkey hrest hc hL hpl hl0 hpp hp hroom h st hacc hlim hb hz hlink hproof hbud hnone ptr0 hret Φ)
  iframe HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi Hc HP Hextra Htail Hdest HD Hout Hhead Hpad HΦ

end Spec
end WNear.Binary.BalanceOf297AbsentCall
