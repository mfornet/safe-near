import Bridge.Functions.BalanceOf297Return
import Bridge.Functions.FtTotalSupply

/-! The absent-balance path through the host value-return call. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode slot)
open WNear.Binary.VecFromElem (stk stk_split stk_addr)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293 pre293)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.ReadRegister (ifaceR iface_of_ifaceR)
open WNear.Binary.ToVec
open WNear.Binary.U128From (u128Bytes)
open WNear.Binary.BorshFT (stkSp stkA splitB)
open WNear.Binary.FtTotalSupply (stk4_word storageReadPost_config)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual absent-balance path through `value_return` of the JSON string for zero. -/
theorem call_through_value_return_absent (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (pre key rest ob dest tail out head : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8)
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
      ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (2112 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 3) 0 0 +
          (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h 3 + R)))) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ rs, (credits Cg R ∗ stk n (s.toNat - 416) 384 ∗ stk n (s.toNat - 16) 8 ∗
        slot n ta 12 38 (A 240) ∗ prefixAt n ((s + 48) + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
        n ↦[wms][ (s + 8).toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) ∗
        n ↦[wms][ (s + 128).toNat ] u128Bytes 0 0 ∗ tvData n ta ptr0 (A 759) (A 353) ∗
        vt n 1057464 idx ta (A 578) ∗ n ↦[i32][ (s + 88).toNat ] 0 ∗
        ∃ q : UInt32, ∃ rest' : List UInt8, ⌜rest'.length = 125⌝ ∗
          n ↦[wms][ (s + 88).toNat + 4 ] (bytes32 q ++ bytes32 128 ++ bytes32 3) ∗
          n ↦[wms][ (s + 144).toNat ] (bytes32 q ++ bytes32 128 ++ bytes32 3) ∗
          n ↦[wms][ s.toNat ] (bytes32 q ++ bytes32 3) ∗ n ↦[wms][ q.toNat + 3 ] rest' ∗
          (∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) ((F + 3) + 1)) ∗
          ∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗
            ValueReturn.post n g ta A ⟨gt, .i32 s⟩ s q 3 [34, 48, 34] h' [.i32 q, .i32 3] rs) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 47) Φ := by
  iintro ⟨#HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456, #HIC, #Hi,
    Hc, HP, Hextra, Htail, Hdest, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 91).take 47 =
      (f297.body.drop 91).take 37 ++ (f297.body.drop 128).take 10 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_copy_format_and_expect_absent cfg lim d inst mi e A n g ta mx hm hd Cg
    (306 * cfg.regularOpCost + valueReturnUse h 3 + R) gt s x1 x2 x3 pp pc pl p c L idx maxP len live F hF
    pre key rest ob dest tail out hs hal hframe hob hdest htail hout hpre hkey hrest hc hL hpl hl0 hpp hp
    hroom h st hacc hlim hb hz hlink hproof hbud hnone ptr0)
  iframe HC F293 HTV F96 F158 Hi Hc HP Hextra Htail Hdest HD Hout
  inext
  iintro %rs Hpost
  icases Hpost with ⟨Hc, %hrs, Hg, Hs, HI, Hm, Hp, Hsrc, Hhost, Hdest, HD, Hvt,
    %q, %rest', %hrest', O0, PL, Hv, Hq, %hl, Hinv⟩
  subst hrs
  icases Hhost with ⟨%h', %hread, Hhost⟩
  have hconfig := storageReadPost_config hread
  have hret' : withinLimit h'.config.maxReturnLen 3 = true := by rw [hconfig.1]; exact hret
  have hcost : valueReturnUse h' 3 = valueReturnUse h 3 := hconfig.2 3
  simp only [show (0 + WNear.Binary.FmtString.kOf (WNear.Binary.FmtU128.val 0 0) + 2 : UInt32) = 3 by simp [FmtString.kOf, FmtU128.val, FmtDigits.decDigits, FmtDigits.digit],
    show WNear.Binary.FmtDigits.decDigits (WNear.Binary.FmtU128.val 0 0) = [48] by simp [FmtU128.val, FmtDigits.decDigits, FmtDigits.digit]] at *
  have hrest125 : rest'.length = 125 := by simpa [FmtString.kOf, FmtU128.val, FmtDigits.decDigits, FmtDigits.digit] using hrest'
  ihave Hq := splitB (n := n) (a := q.toNat) (b := q.toNat + 3) (([34] ++ [48] ++ [34]) : List UInt8) rest' (by simp) $$ Hq
  icases Hq with ⟨Hbytes, Hrest⟩
  icases stkSp 384 32 rfl $$ Hs with ⟨Hs, Hscratch⟩
  ihave Hscratch := stkA (b := s.toNat - 32) (by omega) $$ Hscratch
  icases stkSp 16 16 rfl $$ Hscratch with ⟨H16, Hscratch⟩
  icases stkSp 8 8 rfl $$ Hscratch with ⟨Hmid, H8⟩
  icases stkSp 4 4 rfl $$ H8 with ⟨H8, H12⟩
  icases stkSp 4 12 rfl $$ H16 with ⟨H0, H16⟩
  icases stkSp 4 8 rfl $$ H16 with ⟨H4, H16⟩
  icases stkSp 4 4 rfl $$ H16 with ⟨H8a, H12a⟩
  icases stk4_word $$ H8 with ⟨%s8, H8⟩
  icases stk4_word $$ H12 with ⟨%s12, H12⟩
  icases stk4_word $$ H0 with ⟨%w0, H0⟩
  icases stk4_word $$ H4 with ⟨%w4, H4⟩
  icases stk4_word $$ H8a with ⟨%w8, H8a⟩
  icases stk4_word $$ H12a with ⟨%w12, H12a⟩
  ihave HI := iface_of_ifaceR n ta A $$ HI
  icases HI with ⟨HI, HS12⟩
  have hsp1 : (s - 16).toNat = s.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hsp2 : (s - 16 - 16).toNat = s.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le]
    · rw [hsp1]; simp; omega
    · simp [UInt32.le_iff_toNat_le, hsp1]; omega
  ihave Hmid := stkA (b := s.toNat - 16) (by omega) $$ Hmid
  simp only [List.cons_append, List.nil_append]
  ihave HP : ValueReturn.pre n g ta A ⟨gt, .i32 s⟩ s q 3 [34,48,34] s8 s12 w0 w4 w8 w12 h'
      [.i32 q, .i32 3] $$ [Hg HI H8 H12 H0 H4 H8a H12a Hbytes Hhost]
  · iunfold ValueReturn.pre, WNear.Binary.RegisterLen.frame4
    ihave H8 := memBytes_addr (b := (s - 16).toNat + 8) (by simp [hsp1]; omega) $$ H8
    ihave H12 := memBytes_addr (b := (s - 16).toNat + 12) (by simp [hsp1]; omega) $$ H12
    ihave H0 := memBytes_addr (b := (s - 16 - 16).toNat) (by simp [hsp2]) $$ H0
    ihave H4 := memBytes_addr (b := (s - 16 - 16).toNat + 4) (by simp [hsp2]) $$ H4
    ihave H8a := memBytes_addr (b := (s - 16 - 16).toNat + 8) (by simp [hsp2]) $$ H8a
    ihave H12a := memBytes_addr (b := (s - 16 - 16).toNat + 12) (by simp [hsp2]) $$ H12a
    iframe Hg HI H8 H12 H0 H4 H8a H12a Hbytes Hhost
    ipureintro; rfl
  simp only [Post.mseq_normal]
  iapply (return_vec cfg lim d inst e mi A n g ta mx hm (by omega) Cg R gt s x1 x2 x3 q 3 [34,48,34] head
    (by rfl) hhead (by omega) hal hframe h' hret' (by decide) s8 s12 w0 w4 w8 w12 Φ)
  iframe F779 F545 F456 HIC Hi Hhead Hv HP
  isplitl [Hc]
  · simp only [UInt32.reduceToNat, hcost]
    iexact Hc
  inext
  iintro %rs Hret
  icases Hret with ⟨Hc, Hhead, Hv, Hpost⟩
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Hs Hmid HS12 Hm Hp Hsrc Hdest HD Hvt O0 PL Hv Hhead Hrest Hinv Hpost]
  iframe Hc Hs Hmid HS12 Hm Hp Hsrc Hdest HD Hvt O0 PL Hv Hhead Hrest Hinv Hpost
  isplitr; · ipureintro; exact hrest125
  ipureintro; exact hread

end Spec
end WNear.Binary.BalanceOf297AbsentCall
