import Bridge.Functions.BalanceOfPresent

namespace WNear.Binary.BalanceOf297PresentCall

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.BalanceOfPresent (code293 pre293 post293)

/-- Actual argument setup and the call to function 293 in the decoded function 297. -/
def callCode : List Instr :=
  [.local_get 0, .i32_const 8, .i32_binop .add,
   .local_get 0, .i32_const 48, .i32_binop .add,
   .local_get 0, .i32_const 88, .i32_binop .add, .call 293]

theorem callCode_eq : (f297.body.drop 91).take 10 = callCode := by rfl

/-- Function 297's locals at this point: the remaining locals are preserved. -/
def frame (inst : Nat) (mi : ModuleInst) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32) : Frame :=
  ⟨#[.i32 s, .i32 x1, .i64 x2, .i32 x3], inst, mi⟩

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual 297 call segment composes the present token-balance proof. -/
theorem call_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 20 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (pre key rest b0 b1 ob : List UInt8) (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hs : 384 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 3 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (b0 ++ b1)) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      credits Cg (2100 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (b0 ++ b1) + R) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      ▷ (∀ rs, credits Cg R -∗ post293 n g ta A gt s (s + 8) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre b0 b1 (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)
        [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] rs -∗ Φ.normal rs (frame inst mi s x1 x2 x3))
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 10) Φ := by
  iintro ⟨#Hcode, #F293, Hc, HP, HΦ⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold code293 at Hcode
    icases Hcode with ⟨#H415, -⟩
    iunfold BalanceOfPresent.code415 at H415
    icases H415 with ⟨-, #Hd, -⟩
    iunfold DropVec.dropCode at Hd
    icases Hd with ⟨#H, -⟩
    iexact H
  have ha293 := hm.funcs 293 (by decide)
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := s.toNat_lt
  unfold cost399
  generalize hK395 : LookupMapBorsh.cost395 cfg F L = K395
  generalize hK510 : LookupMapLeaves.cost510 cfg F pl (0 + 4 + L) = K510
  generalize hKr : storageReadUse h (pre ++ (bytes32 L ++ key)) (pl + (0 + 4 + L)).toNat = Kr
  generalize hKread : StorageReadWrapF.costSF cfg F h (b0 ++ b1) = Kread
  rw [callCode_eq]
  simp only [callCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  ihave #S293 := BalanceOfPresent.f293_some (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi e A n g ta mx hm (by omega) Cg gt
      s (s + 8) (s + 48) pp pc pl (s + 88) p c L idx maxP len live F hF pre key rest b0 b1 ob hb0 hb1
      hs hal hob (by simp [UInt32.toNat_add]; omega) hpre hkey hrest hc hL hpl hl0 hpp
      (by simp [UInt32.toNat_add]; omega) hp hroom h st hacc hlim hb hz hlink hproof hbud hreg hsome $$ Hcode
  mcall S293 using [HP] with (simp only [cost399, hK395, hK510, hKr, hKread]; mstep_norm_full; omega)
  · iexact HP
  simp only [cost399, hK395, hK510, hKr, hKread]
  mcredits R
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc]
  · iexact Hc
  · iexact HQ

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.BalanceOfPresent (code293 pre293 post293)

/-- Actual instructions immediately after the call to function 293. -/
def copyCode : List Instr :=
  [.local_get 0, .local_get 0, .i32_const 8, .i32_binop .add,
   .i32_const 8, .i32_binop .add, .load .i64 none ⟨3, 0⟩, .store .i64 none ⟨3, 136⟩,
   .local_get 0, .local_get 0, .load .i64 none ⟨3, 8⟩, .store .i64 none ⟨3, 128⟩]

theorem copyCode_eq : (f297.body.drop 101).take 12 = copyCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Copy the present result to the exact 16-byte formatting input, preserving the source and frame. -/
theorem copy_value (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (n : Nat) (hn : mi.memAddrs[0]? = some n) (Cg R : Nat) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (b0 b1 : List UInt8) (hb0 : b0.length = 8) (hb1 : b1.length = 8) (ob : List UInt8) (hob : ob.length = 16) (Φ : Post NearState GF) :
    credits Cg (12 * cfg.regularOpCost + R) ∗
      n ↦[wms][ (s + 8).toNat ] (b0 ++ b1) ∗
      n ↦[wms][ (s + 128).toNat ] ob ∗
      ▷ (credits Cg R ∗
        n ↦[wms][ (s + 8).toNat ] (b0 ++ b1) ∗
        n ↦[wms][ (s + 128).toNat ] (b0 ++ b1) -∗
        Φ.normal [] (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 101).take 12) Φ := by
  iintro ⟨Hc, Hsrc, Hdst, HΦ⟩
  have hlt := s.toNat_lt
  rw [copyCode_eq]
  simp only [copyCode, frame]
  ihave Hsrc := BorshFT.splitB (n := n) (a := (s + 8).toNat) (b := (s + 8).toNat + 8)
    b0 b1 (by omega) $$ Hsrc
  icases Hsrc with ⟨S0, S8⟩
  ihave S8 := memBytes_addr (show (s + 8).toNat + 8 = (s + 16).toNat by simp [UInt32.toNat_add]; omega) $$ S8
  ihave Hdst := U128From.memBytes_split n (s + 128).toNat 8 ob (by omega) $$ Hdst
  icases Hdst with ⟨D0, D8⟩
  ihave D8 := memBytes_addr (show (s + 128).toNat + 8 = (s + 136).toNat by simp [UInt32.toNat_add]; omega) $$ D8
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [S8] with (first | (simp [hb1, loadWidth, NumType.byteWidth]) | exact List.ne_nil_of_length_pos (by omega))
  mstep [D8] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep
  mstep [S0] with (first | (simp [hb0, loadWidth, NumType.byteWidth]) | exact List.ne_nil_of_length_pos (by omega))
  mstep [D0] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mcredits R
  rw [BorshLeaves.storeBytes_i64_decode b0 hb0, BorshLeaves.storeBytes_i64_decode b1 hb1]
  ihave S8 := memBytes_addr (show (s + 16).toNat = (s + 8).toNat + 8 by simp [UInt32.toNat_add]; omega) $$ S8
  ihave Hsrc := BorshFT.joinB (n := n) (a := (s + 8).toNat) (b := (s + 8).toNat + 8)
    b0 b1 (by omega) $$ [S0 S8]
  · iframe S0 S8
  ihave D8 := memBytes_addr (show (s + 136).toNat = (s + 128).toNat + 8 by simp [UInt32.toNat_add]; omega) $$ D8
  ihave Hdst := BorshFT.joinB (n := n) (a := (s + 128).toNat) (b := (s + 128).toNat + 8)
    b0 b1 (by omega) $$ [D0 D8]
  · iframe D0 D8
  iapply HΦ $$ [Hc Hsrc Hdst]
  iframe Hc Hsrc Hdst

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- Compose the actual call and its following value-copy instructions. -/
theorem call_and_copy_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 20 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (pre key rest b0 b1 ob dest : List UInt8) (hb0 : b0.length = 8) (hb1 : b1.length = 8) (hs : 384 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 3 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (b0 ++ b1)) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      credits Cg (2112 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (b0 ++ b1) + R) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗
      ▷ (∀ rs, (credits Cg R ∗ post293 n g ta A gt s (s + 8) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre b0 b1 (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)
        [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] rs ∗
        n ↦[wms][ (s + 128).toNat ] (b0 ++ b1)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3))
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 22) Φ := by
  iintro ⟨#HC, #F293, Hc, HP, Hdest, HΦ⟩
  have hn := hm.mem
  have hseg : (f297.body.drop 91).take 22 =
      (f297.body.drop 91).take 10 ++ (f297.body.drop 101).take 12 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_present cfg lim d inst mi e A n g ta mx hm hd Cg (12 * cfg.regularOpCost + R) gt s x1 x2 x3
    pp pc pl p c L idx maxP len live F hF pre key rest b0 b1 ob hb0 hb1 hs hal hframe hob hpre hkey hrest hc hL hpl hl0 hpp hp
    hroom h st hacc hlim hb hz hlink hproof hbud hreg hsome)
  iframe HC F293 HP
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro %rs Hc HQ
  iunfold post293 at HQ
  icases HQ with ⟨%hrs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hv, Hsrc, Hhost⟩
  subst hrs
  simp only [Post.mseq_normal]
  iapply (copy_value cfg lim d inst mi n hn Cg R s x1 x2 x3 hframe b0 b1 hb0 hb1 dest hdest Φ)
  iframe Hc Hsrc Hdest
  inext
  iintro ⟨Hc, Hsrc, Hdest⟩
  ihave Hpost : post293 n g ta A gt s (s + 8) ((s + 48) + 24) pp pc pl (s + 88) p c L
      idx maxP len live F pre b0 b1 (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)
      [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] [] $$ [Hg Hs HI Hvt Hinv Hm Hp Hv Hsrc Hhost]
  · iunfold post293
    iframe Hg Hs HI Hvt Hinv Hm Hp Hv Hsrc Hhost
    ipureintro; rfl
  ispecialize HΦ $$ %([] : List Value)
  iapply HΦ $$ [Hc Hpost Hdest]
  iframe Hc Hpost Hdest

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk roomFor grownLen)
open WNear.Binary.FmtGrow (newCap)
open WNear.Binary.AllocFirstFit (vt)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.ToVec
open WNear.Binary.U128From (u128Bytes)

/-- Actual instructions setting up and calling the U128 JSON serializer. -/
def formatCode : List Instr :=
  [.local_get 0, .i32_const 88, .i32_binop .add,
   .local_get 0, .i32_const 128, .i32_binop .add, .call 96]

theorem formatCode_eq : (f297.body.drop 113).take 7 = formatCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The actual call to function 96 serializes the copied account balance. -/
theorem format_value (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s x1 : UInt32) (x2 lo hi : UInt64) (x3 ptr0 aidx : UInt32)
    (ob : List UInt8) (maxP hl : Nat) (live : List (Nat × Nat))
    (hs : 416 ≤ s.toNat) (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16)
    (hr1 : roomFor hl maxP 128)
    (hr2 : ∀ hl1, hl1 = hl ∨ hl1 = grownLen hl 128 → roomFor hl1 maxP (newCap 0 (kOf (val lo hi))))
    (F : Nat) (hF : okG F) (Φ : Post NearState GF) :
    tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      inst ↪[inst] mi ∗ credits Cg (17 * cfg.regularOpCost + cost96F cfg F lo hi + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
      n ↦[wms][ (s + 88).toNat ] ob ∗ n ↦[wms][ (s + 128).toNat ] u128Bytes lo hi ∗
      tvData n ta ptr0 (A 759) (A 353) ∗ vt n 1057464 aidx ta (A 578) ∗ heapInv n maxP hl live F ∗
      ▷ (∀ rs, (credits Cg R ∗ ⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
        n ↦[wms][ (s + 128).toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗
        vt n 1057464 aidx ta (A 578) ∗
        ∃ q : UInt32, ∃ rest : List UInt8, ⌜rest.length = 128 - ((kOf (val lo hi)).toNat + 2)⌝ ∗
          n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] q ∗
          n ↦[i32][ (s + 88).toNat + 8 ] 128 ∗ n ↦[i32][ (s + 88).toNat + 12 ] (0 + kOf (val lo hi) + 2) ∗
          n ↦[wms][ q.toNat ] (([34] ++ decDigits (val lo hi) ++ [34]) ++ rest) ∗
          ∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) (F + 1)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 113).take 7) Φ := by
  iintro ⟨#Hcode, #H96, #Hi, Hc, Hg, Hs, Ho, Hv, HD, Hvt, Hh, HΦ⟩
  have ha96 := hm.funcs 96 (by decide)
  have t14 : types[14]!.params.length = 2 := by rfl
  have hlt := s.toNat_lt
  ihave #S96 := ToVec.f96_spec (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi A n g ta hm (by omega)
    Cg gt s (s + 88) (s + 128) ptr0 aidx ob maxP hl live lo hi hs hob
    (by simp [UInt32.toNat_add]; omega) (by simp [UInt32.toNat_add]; omega) hr1 hr2 F hF $$ Hcode
  rw [formatCode_eq]
  simp only [formatCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall S96 using [Hg Hs Ho Hv HD Hvt Hh]
  · iframe Hg Hs Ho Hv HD Hvt Hh
  mcredits R
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc HQ]
  iframe Hc HQ

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_join stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_step)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.BalanceOfPresent (code293 pre293 post293)
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
/-- The actual present-account call, copy and serializer, with five heap-growth slots. -/
theorem call_copy_and_format_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (lo hi : UInt64)
    (pre key rest ob dest tail : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 5 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (u128Bytes lo hi)) (ptr0 : UInt32) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗ inst ↪[inst] mi ∗
      credits Cg (2112 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 4) lo hi + R)) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      ▷ (∀ rs, (credits Cg R ∗ ⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
        ifaceR n ta A ∗ prefixAt n ((s + 48) + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
        n ↦[wms][ (s + 8).toNat ] u128Bytes lo hi ∗
        (∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗ mhostPt h') ∗
        n ↦[wms][ (s + 128).toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗
        vt n 1057464 idx ta (A 578) ∗
        ∃ q : UInt32, ∃ rest' : List UInt8, ⌜rest'.length = 128 - ((kOf (val lo hi)).toNat + 2)⌝ ∗
          n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] q ∗
          n ↦[i32][ (s + 88).toNat + 8 ] 128 ∗ n ↦[i32][ (s + 88).toNat + 12 ] (0 + kOf (val lo hi) + 2) ∗
          n ↦[wms][ q.toNat ] (([34] ++ decDigits (val lo hi) ++ [34]) ++ rest') ∗
          ∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) ((F + 4) + 1)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 29) Φ := by
  iintro ⟨#HC, #F293, #HTV, #F96, #Hi, Hc, HP, Hextra, Htail, Hdest, HD, HΦ⟩
  have hroom3 : HeapRoomK 3 len maxP := by
    unfold HeapRoomK at hroom ⊢
    rcases hroom with ⟨a,b,c,d⟩
    exact ⟨a,b,by omega,by omega⟩
  have hseg : (f297.body.drop 91).take 29 =
      (f297.body.drop 91).take 22 ++ (f297.body.drop 113).take 7 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_and_copy_present cfg lim d inst mi e A n g ta mx hm (by omega) Cg
    (17 * cfg.regularOpCost + cost96F cfg (F + 4) lo hi + R) gt s x1 x2 x3
    pp pc pl p c L idx maxP len live F hF pre key rest (storeBytes (.i64 lo) 8) (storeBytes (.i64 hi) 8) ob dest (by rfl) (by rfl) (by omega) hal hframe hob hdest
    hpre hkey hrest hc hL hpl hl0 hpp hp hroom3 h st hacc hlim hb hz hlink hproof hbud hreg hsome)
  dsimp only [u128Bytes]
  iframe HC F293 Hc HP Hdest
  inext
  iintro %rs ⟨Hc, HQ, Hdest⟩
  iunfold post293 at HQ
  icases HQ with ⟨%hrs, Hg, Hs, HI, Hvt, Hinv, Hm, Hp, Hv, Hsrc, Hhost⟩
  subst hrs
  icases Hinv with ⟨%len', %hlen, Hinv⟩
  have hr1 : roomFor len' maxP 128 := roomFor_ofK 128 (by decide) hroom hlen (by omega)
  have hr2 : ∀ l, l = len' ∨ l = grownLen len' 128 → roomFor l maxP (newCap 0 (kOf (val lo hi))) := by
    intro l hl
    apply roomFor_ofK _ (by have := FtTotalSupply.newCap_le (val lo hi); omega) hroom (lenIn_step 128 (by decide) hlen hl) (by omega)
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
  iapply (format_value cfg lim d inst mi A n g ta hm hd Cg R gt s x1 x2 lo hi x3 ptr0 idx
    (bytes32 p ++ (bytes32 c ++ bytes32 L) ++ tail) maxP len' live hs hframe hobuf hr1 hr2 (F + 4) (by unfold okG at *; omega) Φ)
  iframe HTV F96 Hi Hc Hg Hs Ho HD Hvt Hinv
  isplitl [Hdest]
  · unfold u128Bytes
    iexact Hdest
  inext
  iintro %rs Hfmt
  icases Hfmt with ⟨Hc, %hrs, Hg, Hs, Hdest, HD, Hvt, %q, %rest, %hrest, O0, O4, O8, O12, Hq, %hl, Hinv⟩
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Hg Hs HI Hm Hp Hsrc Hhost Hdest HD Hvt O0 O4 O8 O12 Hq Hinv]
  dsimp only [u128Bytes]
  iframe Hc Hg Hs HI Hm Hp Hsrc Hhost Hdest HD Hvt O0 O4 O8 O12 Hq Hinv
  isplitr; · ipureintro; exact hrs
  ipureintro; exact hrest

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open WNear.Binary.BalanceOf297AbsentCall (expect_ok)
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_join stk_addr roomFor grownLen)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK LenIn roomFor_ofK lenIn_step)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.BalanceOfPresent (code293 pre293 post293)
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
/-- The present-account path through the successful serializer result extraction. -/
theorem call_copy_format_and_expect_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (lo hi : UInt64)
    (pre key rest ob dest tail out : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4) (hout : out.length = 12)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 5 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (u128Bytes lo hi)) (ptr0 : UInt32) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ inst ↪[inst] mi ∗
      credits Cg (2112 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 4) lo hi + (44 * cfg.regularOpCost + R))) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗
      ▷ (∀ rs, (credits Cg R ∗ ⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 416) 416 ∗
        ifaceR n ta A ∗ prefixAt n ((s + 48) + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
        n ↦[wms][ (s + 8).toNat ] u128Bytes lo hi ∗
        (∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗ mhostPt h') ∗
        n ↦[wms][ (s + 128).toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗
        vt n 1057464 idx ta (A 578) ∗
        ∃ q : UInt32, ∃ rest' : List UInt8, ⌜rest'.length = 128 - ((kOf (val lo hi)).toNat + 2)⌝ ∗
          n ↦[i32][ (s + 88).toNat ] 0 ∗
          n ↦[wms][ (s + 88).toNat + 4 ] (bytes32 q ++ bytes32 128 ++ bytes32 (0 + kOf (val lo hi) + 2)) ∗
          n ↦[wms][ (s + 144).toNat ] (bytes32 q ++ bytes32 128 ++ bytes32 (0 + kOf (val lo hi) + 2)) ∗
          n ↦[wms][ q.toNat ] (([34] ++ decDigits (val lo hi) ++ [34]) ++ rest') ∗
          ∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) ((F + 4) + 1)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 37) Φ := by
  iintro ⟨#HC, #F293, #HTV, #F96, #F158, #Hi, Hc, HP, Hextra, Htail, Hdest, HD, Hout, HΦ⟩
  have hseg : (f297.body.drop 91).take 37 =
      (f297.body.drop 91).take 29 ++ (f297.body.drop 120).take 8 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_copy_and_format_present cfg lim d inst mi e A n g ta mx hm hd Cg
    (44 * cfg.regularOpCost + R) gt s x1 x2 x3 pp pc pl p c L idx maxP len live F hF lo hi
    pre key rest ob dest tail hs hal hframe hob hdest htail hpre hkey hrest hc hL hpl hl0 hpp hp
    hroom h st hacc hlim hb hz hlink hproof hbud hreg hsome ptr0)
  iframe HC F293 HTV F96 Hi Hc HP Hextra Htail Hdest HD
  inext
  iintro %rs Hpost
  icases Hpost with ⟨Hc, %hrs, Hg, Hs, HI, Hm, Hp, Hsrc, Hhost, Hdest, HD, Hvt,
    %q, %rest', %hrest', O0, O4, O8, O12, Hq, %hl, Hinv⟩
  subst hrs
  simp only [Post.mseq_normal]
  rw [show frame inst mi s x1 x2 x3 = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3 from rfl]
  iapply (expect_ok cfg lim d inst mi A n g ta hm (by omega) Cg R gt s x1 x2 x3 q
    (0 + kOf (val lo hi) + 2) out hout hframe Φ)
  iframe F158 Hi Hc Hg O0 O4 O8 O12 Hout
  inext
  iintro %rs Hexpect
  icases Hexpect with ⟨Hc, %hrs, Hg, O0, PL, Hout⟩
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Hg Hs HI Hm Hp Hsrc Hhost Hdest HD Hvt O0 PL Hout Hq Hinv]
  iframe Hc Hg Hs HI Hm Hp Hsrc Hhost Hdest HD Hvt O0 PL Hout Hq Hinv
  isplitr; · ipureintro; exact hrs
  ipureintro; exact hrest'

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open Wasm Wasm.Near
open WNear.Binary.FmtString WNear.Binary.FmtU128 WNear.Binary.FmtDigits

def resultLen (lo hi : UInt64) : UInt32 := 0 + kOf (val lo hi) + 2

theorem resultLen_def (lo hi : UInt64) : 0 + kOf (val lo hi) + 2 = resultLen lo hi := rfl

theorem resultLen_toNat (lo hi : UInt64) :
    (resultLen lo hi).toNat = (decDigits (val lo hi)).length + 2 := by
  have hk := kOf_toNat lo hi
  have hb := decDigits_le lo hi
  simp only [resultLen, UInt32.toNat_add, UInt32.toNat_zero, UInt32.reduceToNat]
  omega

theorem resultLen_pos (lo hi : UInt64) : 0 < (resultLen lo hi).toNat := by
  rw [resultLen_toNat]
  omega

theorem resultBytes_length (lo hi : UInt64) :
    (([34] ++ decDigits (val lo hi) ++ [34]) : List UInt8).length = (resultLen lo hi).toNat := by
  simp only [List.length_append, List.length_cons, List.length_nil, resultLen_toNat]
  omega

end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open WNear.Binary.BalanceOf297AbsentCall (return_vec)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtDigits (decDigits)
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode slot)
open WNear.Binary.VecFromElem (stk stk_split stk_addr)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.BalanceOfPresent (code293 pre293)
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
/-- The actual present-balance path through `value_return` of the serialized balance. -/
theorem call_through_value_return_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (lo hi : UInt64)
    (pre key rest ob dest tail out head : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 5 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (u128Bytes lo hi)) (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (2112 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 4) lo hi +
          (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + R)))) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      ▷ (∀ rs, (credits Cg R ∗ stk n (s.toNat - 416) 384 ∗ stk n (s.toNat - 16) 8 ∗
        slot n ta 12 38 (A 240) ∗ prefixAt n ((s + 48) + 24) pp pc pl ∗ n ↦[wms][ pp.toNat ] pre ∗
        n ↦[wms][ (s + 8).toNat ] u128Bytes lo hi ∗
        n ↦[wms][ (s + 128).toNat ] u128Bytes lo hi ∗ tvData n ta ptr0 (A 759) (A 353) ∗
        vt n 1057464 idx ta (A 578) ∗ n ↦[i32][ (s + 88).toNat ] 0 ∗
        ∃ q : UInt32, ∃ rest' : List UInt8, ⌜rest'.length = 128 - (resultLen lo hi).toNat⌝ ∗
          n ↦[wms][ (s + 88).toNat + 4 ] (bytes32 q ++ bytes32 128 ++ bytes32 (resultLen lo hi)) ∗
          n ↦[wms][ (s + 144).toNat ] (bytes32 q ++ bytes32 128 ++ bytes32 (resultLen lo hi)) ∗
          n ↦[wms][ s.toNat ] (bytes32 q ++ bytes32 (resultLen lo hi)) ∗ n ↦[wms][ q.toNat + (resultLen lo hi).toNat ] rest' ∗
          (∃ hl', heapInv n maxP hl' ((q.toNat, 128) :: live) ((F + 4) + 1)) ∗
          ∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗
            ValueReturn.post n g ta A ⟨gt, .i32 s⟩ s q (resultLen lo hi) ([34] ++ decDigits (val lo hi) ++ [34]) h' [.i32 q, .i32 (resultLen lo hi)] rs) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 47) Φ := by
  iintro ⟨#HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456, #HIC, #Hi,
    Hc, HP, Hextra, Htail, Hdest, HD, Hout, Hhead, HΦ⟩
  have hseg : (f297.body.drop 91).take 47 =
      (f297.body.drop 91).take 37 ++ (f297.body.drop 128).take 10 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_copy_format_and_expect_present cfg lim d inst mi e A n g ta mx hm hd Cg
    (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + R) gt s x1 x2 x3 pp pc pl p c L idx maxP len live F hF lo hi
    pre key rest ob dest tail out hs hal hframe hob hdest htail hout hpre hkey hrest hc hL hpl hl0 hpp hp
    hroom h st hacc hlim hb hz hlink hproof hbud hreg hsome ptr0)
  iframe HC F293 HTV F96 F158 Hi Hc HP Hextra Htail Hdest HD Hout
  inext
  iintro %rs Hpost
  icases Hpost with ⟨Hc, %hrs, Hg, Hs, HI, Hm, Hp, Hsrc, Hhost, Hdest, HD, Hvt,
    %q, %rest', %hrest', O0, PL, Hv, Hq, %hl, Hinv⟩
  subst hrs
  icases Hhost with ⟨%h', %hread, Hhost⟩
  have hconfig := storageReadPost_config hread
  have hret' : withinLimit h'.config.maxReturnLen (resultLen lo hi).toNat = true := by rw [hconfig.1]; exact hret
  have hcost : valueReturnUse h' (resultLen lo hi).toNat = valueReturnUse h (resultLen lo hi).toNat := hconfig.2 (resultLen lo hi).toNat
  simp only [resultLen_def] at *
  have hrestLen : rest'.length = 128 - (resultLen lo hi).toNat := by
    rw [resultLen_toNat]
    simpa only [FmtString.kOf_toNat] using hrest'
  ihave Hq := splitB (n := n) (a := q.toNat) (b := q.toNat + (resultLen lo hi).toNat)
    (([34] ++ decDigits (val lo hi) ++ [34]) : List UInt8) rest' (by rw [resultBytes_length]) $$ Hq
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
  ihave HP : ValueReturn.pre n g ta A ⟨gt, .i32 s⟩ s q (resultLen lo hi) ([34] ++ decDigits (val lo hi) ++ [34]) s8 s12 w0 w4 w8 w12 h'
      [.i32 q, .i32 (resultLen lo hi)] $$ [Hg HI H8 H12 H0 H4 H8a H12a Hbytes Hhost]
  · iunfold ValueReturn.pre, WNear.Binary.RegisterLen.frame4
    ihave H8 := memBytes_addr (b := (s - 16).toNat + 8) (by simp [hsp1]; omega) $$ H8
    ihave H12 := memBytes_addr (b := (s - 16).toNat + 12) (by simp [hsp1]; omega) $$ H12
    ihave H0 := memBytes_addr (b := (s - 16 - 16).toNat) (by simp [hsp2]) $$ H0
    ihave H4 := memBytes_addr (b := (s - 16 - 16).toNat + 4) (by simp [hsp2]) $$ H4
    ihave H8a := memBytes_addr (b := (s - 16 - 16).toNat + 8) (by simp [hsp2]) $$ H8a
    ihave H12a := memBytes_addr (b := (s - 16 - 16).toNat + 12) (by simp [hsp2]) $$ H12a
    simp only [List.cons_append, List.nil_append]
    iframe Hg HI H8 H12 H0 H4 H8a H12a Hbytes Hhost
  simp only [Post.mseq_normal]
  rw [show frame inst mi s x1 x2 x3 = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3 from rfl]
  iapply (return_vec cfg lim d inst e mi A n g ta mx hm (by omega) Cg R gt s x1 x2 x3 q (resultLen lo hi) ([34] ++ decDigits (val lo hi) ++ [34]) head
    (resultBytes_length lo hi) hhead (by omega) hal hframe h' hret' (resultLen_pos lo hi) s8 s12 w0 w4 w8 w12 Φ)
  iframe F779 F545 F456 HIC Hi Hhead Hv HP
  isplitl [Hc]
  · simp only [hcost]
    iexact Hc
  inext
  iintro %rs Hret
  icases Hret with ⟨Hc, Hhead, Hv, Hpost⟩
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Hs Hmid HS12 Hm Hp Hsrc Hdest HD Hvt O0 PL Hv Hhead Hrest Hinv Hpost]
  simp only [List.cons_append, List.nil_append]
  iframe Hc Hs Hmid HS12 Hm Hp Hsrc Hdest HD Hvt O0 PL Hv Hhead Hrest Hinv Hpost
  isplitr; · ipureintro; exact hrestLen
  ipureintro; exact hread

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open WNear.Binary.BalanceOf297AbsentCall (cleanup)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.U128From (u128Bytes)
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.BalanceOfPresent (code293 pre293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.LookupMapLeaves (prefixAt)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ToVec
open WNear.Binary.BorshFT (joinB)
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual present-account path through host return and final cleanup. -/
theorem call_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (lo hi : UInt64)
    (pre key rest ob dest tail out head padding : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8) (hpadding : pre.length + padding.length = pc.toNat) (hpc : pc ≠ 0)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 5 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (u128Bytes lo hi)) (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (2112 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 4) lo hi +
          (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R))))) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len ((pp.toNat, pc.toNat) :: live) F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      n ↦[wms][ pp.toNat + pre.length ] padding ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗
        (∃ hl', heapInv n maxP hl' live (((F + 4) + 1 + 1) + 1)) ∗
        (∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗
          mhostPt (h'.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
        Φ.normal [] (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 59) Φ := by
  iintro ⟨#HC, #F293, #HTV, #F96, #F158, #F779, #F545, #F456, #Hdrop, #F68, #HIC, #Hi,
    Hc, HP, Hextra, Htail, Hdest, HD, Hout, Hhead, Hpad, HΦ⟩
  have hseg : (f297.body.drop 91).take 59 =
      (f297.body.drop 91).take 47 ++ (f297.body.drop 138).take 12 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_through_value_return_present cfg lim d inst mi e A n g ta mx hm hd Cg
    (660 * cfg.regularOpCost + R) gt s x1 x2 x3 pp pc pl p c L idx maxP len
    ((pp.toNat, pc.toNat) :: live) F hF lo hi pre key rest ob dest tail out head hs hal hframe hob hdest htail hout hhead
    hpre hkey hrest hc hL hpl hl0 hpp hp hroom h st hacc hlim hb hz hlink hproof hbud hreg hsome ptr0 hret)
  iframe HC F293 HTV F96 F158 F779 F545 F456 HIC Hi Hc HP Hextra Htail Hdest HD Hout Hhead
  inext
  iintro %rs Hpost
  icases Hpost with ⟨Hc, Hs, Hmid, Hslot, Hm, Hp, Hsrc, Hdest, HD, Hvt, O0,
    %q, %rest', %hrest', PL, Hv, Hhead, Hrest, ⟨%hl, Hinv⟩, %h', %hread, Hret⟩
  iunfold ValueReturn.post at Hret
  icases Hret with ⟨%hrs, Hg, HI, W8, W12, Hframe, Hbytes, Hhost⟩
  subst hrs
  ihave Hq := joinB (n := n) (a := q.toNat) (b := q.toNat + (resultLen lo hi).toNat) (([34] ++ decDigits (val lo hi) ++ [34]) : List UInt8) rest' (by rw [resultBytes_length]) $$ [Hbytes Hrest]
  · iframe Hbytes Hrest
  ihave Hb := joinB (n := n) (a := pp.toNat) (b := pp.toNat + pre.length) pre padding rfl $$ [Hp Hpad]
  · iframe Hp Hpad
  iunfold prefixAt at Hm
  ihave Hm := memBytes_addr (show ((s + 48) + 24).toNat = (s + 72).toNat by
    simp [UInt32.toNat_add]) $$ Hm
  have hLbound : (resultLen lo hi).toNat ≤ 128 := by
    rw [resultLen_toNat]
    have hb := FmtString.decDigits_le lo hi
    omega
  have hqb : ((([34] ++ decDigits (val lo hi) ++ [34]) : List UInt8) ++ rest').length = 128 := by
    rw [List.length_append, resultBytes_length]
    omega
  have hpb : (pre ++ padding).length = pc.toNat := by simpa using hpadding
  simp only [Post.mseq_normal, List.append_assoc]
  rw [show frame inst mi s x1 x2 x3 = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 x3 from rfl]
  iapply (cleanup cfg lim d inst mi A n g ta hm (by omega) Cg R gt s x1 x2 x3 q (resultLen lo hi) pp pc pl maxP hl
    ((F + 4) + 1) live (([34] ++ decDigits (val lo hi) ++ [34]) ++ rest') (pre ++ padding) hqb hpb hpc hframe Φ)
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  iframe Hdrop F68 Hc Hg Hv Hm Hq Hb Hinv
  inext
  iintro ⟨Hc, Hg, V0, V4, V8, P0, P4, P8, Hinv⟩
  iapply HΦ $$ [Hc Hg Hinv Hhost]
  iframe Hc Hg Hinv Hhost
  ipureintro; exact hread

end Spec
end WNear.Binary.BalanceOf297PresentCall

namespace WNear.Binary.BalanceOf297PresentCall
open WNear.Binary.BalanceOf297AbsentCall (argument_copy)
open WNear.Binary.FmtString (kOf)
open WNear.Binary.FmtU128 (val)
open WNear.Binary.FmtDigits (decDigits)
open WNear.Binary.U128From (u128Bytes)
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod ifaceCode)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399)
open WNear.Binary.BalanceOfPresent (code293 pre293)
open WNear.Binary.AllocInv (heapInv)
open WNear.Binary.DropVec (dropCode)
open WNear.Binary.ToVec
open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- From a parsed account string through the present-account result and epilogue. -/
theorem parsed_account_through_cleanup_present (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 28 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F) (lo hi : UInt64)
    (pre key rest ob dest tail out head padding old : List UInt8) (hs : 416 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16) (htail : tail.length = 4) (hout : out.length = 12) (hhead : head.length = 8) (hold : old.length = 12) (hpadding : pre.length + padding.length = pc.toNat) (hpc : pc ≠ 0)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 5 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hreg : withinLimit h.config.maxRegisterLen 16 = true)
    (hsome : h.storage (pre ++ (bytes32 L ++ key)) = some (u128Bytes lo hi)) (ptr0 : UInt32) (hret : withinLimit h.config.maxReturnLen (resultLen lo hi).toNat = true) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      tvCode n maxP inst mi A ∗ A 96 ↪[wf] FuncInst.wasm types[14]! inst f96 ∗
      A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      A 545 ↪[wf] FuncInst.wasm types[14]! inst f545 ∗ A 456 ↪[wf] FuncInst.wasm types[14]! inst f456 ∗
      dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗ ifaceCode e inst mi A n mx ∗ inst ↪[inst] mi ∗
      credits Cg (12 * cfg.regularOpCost + (2112 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
        (17 * cfg.regularOpCost + cost96F cfg (F + 4) lo hi +
          (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R)))))) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 32) p c L
        idx maxP len ((pp.toNat, pc.toNat) :: live) F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 32)] ∗
      n ↦[wms][ (s + 88).toNat ] old ∗
      stk n (s.toNat - 416) 32 ∗ n ↦[wms][ (s + 100).toNat ] tail ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗ tvData n ta ptr0 (A 759) (A 353) ∗
      n ↦[wms][ (s + 144).toNat ] out ∗ n ↦[wms][ s.toNat ] head ∗
      n ↦[wms][ pp.toNat + pre.length ] padding ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗
        (∃ hl', heapInv n maxP hl' live (((F + 4) + 1 + 1) + 1)) ∗
        (∃ h', ⌜StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st h'⌝ ∗
          mhostPt (h'.selectReturnValue ([34] ++ decDigits (val lo hi) ++ [34]))) -∗
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
  have hframeEq : frame inst mi s x1 x2 (s + 40) = WNear.Binary.BalanceOf297AbsentCall.frame inst mi s x1 x2 (s + 40) := rfl
  rw [hframeEq]
  iapply (argument_copy cfg lim d inst mi n hm.mem Cg
    (2112 * cfg.regularOpCost + cost399 cfg F pl L h (pre ++ (bytes32 L ++ key)) (u128Bytes lo hi) +
      (17 * cfg.regularOpCost + cost96F cfg (F + 4) lo hi +
        (44 * cfg.regularOpCost + (306 * cfg.regularOpCost + valueReturnUse h (resultLen lo hi).toNat + (660 * cfg.regularOpCost + R)))))
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
  rw [← hframeEq]
  iapply (call_through_cleanup_present cfg lim d inst mi e A n g ta mx hm hd Cg R gt s x1 x2 (s + 40)
    pp pc pl p c L idx maxP len live F hF lo hi pre key rest ob dest tail out head padding hs hal hframe hob hdest htail
    hout hhead hpadding hpc hpre hkey hrest hc hL hpl hl0 hpp hp hroom h st hacc hlim hb hz hlink hproof hbud hreg hsome ptr0 hret Φ)
  iframe HC F293 HTV F96 F158 F779 F545 F456 Hdrop F68 HIC Hi Hc HP Hextra Htail Hdest HD Hout Hhead Hpad HΦ

end Spec
end WNear.Binary.BalanceOf297PresentCall

/-! Compose state loading with the parsed present-account suffix. -/
