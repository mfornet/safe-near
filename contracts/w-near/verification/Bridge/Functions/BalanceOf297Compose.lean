import Bridge.Functions.BalanceOf297Format
import Bridge.Functions.FtTotalSupply

/-! Compose the absent lookup, zero copy, and JSON serialization in function 297. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_join stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_step)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293 pre293 post293)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.ReadRegister (ifaceR)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.ToVec
open WNear.Binary.U128From (u128Bytes)

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual absent-account call, copy and serializer, with four heap-growth slots. -/
theorem call_copy_and_format_absent (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (pre key rest ob dest tail : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4)
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
    (hnone : h.storage (pre ++ (bytes32 L ++ key)) = none) (ptr0 : UInt32) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗ inst ↪[inst] mi ∗
      credits Cg (2112 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 3) 0 0 + R)) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      ▷ (∀ rs, (credits Cg R ∗ ⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
        ifaceR n ta A ∗ prefixAt n ((s + 48) + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
        n ↦[wms][ (s + 8).toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) ∗
        (∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗ mhostPt h') ∗
        n ↦[wms][ (s + 128).toNat ] u128Bytes 0 0 ∗ tvData n ta ptr0 (A 759) (A 353) ∗
        vt n 1057464 idx ta (A 578) ∗
        ∃ q : UInt32, ∃ rest' : List UInt8, ⌜rest'.length = 128 - ((kOf (val 0 0)).toNat + 2)⌝ ∗
          n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] q ∗
          n ↦[i32][ (s + 88).toNat + 8 ] 128 ∗ n ↦[i32][ (s + 88).toNat + 12 ] (0 + kOf (val 0 0) + 2) ∗
          n ↦[wms][ q.toNat ] (([34] ++ decDigits (val 0 0) ++ [34]) ++ rest') ∗
          ∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) ((F + 3) + 1)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 29) Φ := by
  iintro ⟨#HC, #F293, #HTV, #F96, #Hi, Hc, HP, Hextra, Htail, Hdest, HD, HΦ⟩
  have hroom2 : HeapRoomK 2 len maxP := by
    unfold HeapRoomK at hroom ⊢
    rcases hroom with ⟨a,b,c,d⟩
    exact ⟨a,b,by omega,by omega⟩
  have hseg : (f297.body.drop 91).take 29 =
      (f297.body.drop 91).take 22 ++ (f297.body.drop 113).take 7 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_and_copy_absent cfg lim d inst mi e A n g ta mx hm (by omega) Cg
    (17 * cfg.regularOpCost + cost96F cfg (F + 3) 0 0 + R) gt s x1 x2 x3
    pp pc pl p c L idx maxP len live F hF pre key rest ob dest (by omega) hal hframe hob hdest
    hpre hkey hrest hc hL hpl hl0 hpp hp hroom2 h st hacc hlim hb hz hlink hproof hbud hnone)
  iframe HC F293 Hc HP Hdest
  inext
  iintro %rs ⟨Hc, HQ, Hdest⟩
  iunfold post293 at HQ
  icases HQ with ⟨%hrs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hv, Hsrc, Hhost⟩
  subst hrs
  icases Hinv with ⟨%len', %hlen, Hinv⟩
  have hr1 : roomFor len' maxP 128 := roomFor_ofK 128 (by decide) hroom hlen (by omega)
  have hr2 : ∀ l, l = len' ∨ l = grownLen len' 128 → roomFor l maxP (newCap 0 (kOf (val 0 0))) := by
    intro l hl
    apply roomFor_ofK _ (by have := FtTotalSupply.newCap_le (val 0 0); omega) hroom (lenIn_step 128 (by decide) hlen hl) (by omega)
  ihave Hs := stk_addr (show s.toNat - 384 = s.toNat - 416 + 32 by omega) $$ Hs
  ihave Hs := stk_join n (s.toNat - 416) 32 384 $$ [Hextra Hs]
  · iframe Hextra Hs
  ihave Htail := memBytes_addr (show (s + 100).toNat = (s + 88).toNat + 12 by
    simp [UInt32.toNat_add]; have := s.toNat_lt; omega) $$ Htail
  ihave Ho := U128From.memBytes_join n (s + 88).toNat 12 (bytes32 p ++ (bytes32 c ++ bytes32 L)) tail
    (by simp [bytes32_length]) $$ [Hv Htail]
  · iframe Hv Htail
  have hobuf : (bytes32 p ++ (bytes32 c ++ bytes32 L) ++ tail).length = 16 := by simp [bytes32_length, htail]
  simp only [Post.mseq_normal]
  iapply (format_zero cfg lim d inst mi A n g ta hm hd Cg R gt s x1 x2 x3 ptr0 idx
    (bytes32 p ++ (bytes32 c ++ bytes32 L) ++ tail) maxP len' live hs hframe hobuf hr1 hr2 (F + 3) (by unfold okG at *; omega) Φ)
  iframe HTV F96 Hi Hc Hg Hs Ho HD Hvt Hinv
  isplitl [Hdest]
  · unfold u128Bytes
    iexact Hdest
  inext
  iintro %rs Hfmt
  icases Hfmt with ⟨Hc, %hrs, Hg, Hs, Hdest, HD, Hvt, %q, %rest, %hrest, O0, O4, O8, O12, Hq, %hl, Hinv⟩
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Hg Hs HI Hm Hp Hsrc Hhost Hdest HD Hvt O0 O4 O8 O12 Hq Hinv]
  iframe Hc Hg Hs HI Hm Hp Hsrc Hhost Hdest HD Hvt O0 O4 O8 O12 Hq Hinv
  isplitr; · ipureintro; exact hrs
  ipureintro; exact hrest

end Spec
end WNear.Binary.BalanceOf297AbsentCall
