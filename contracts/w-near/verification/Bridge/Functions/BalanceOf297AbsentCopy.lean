import Bridge.Functions.BalanceOf297AbsentCall
import Bridge.Functions.FtTotalSupplyGetter

/-! Copy the absent-account result to the formatting input in function 297. -/

namespace WNear.Binary.BalanceOf297AbsentCall

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecWithCap (okG)
open WNear.Binary.LookupMapOps (HeapRoomK)
open WNear.Binary.LookupMapGet (cost399None)
open WNear.Binary.BalanceOfAbsent (code293 pre293 post293)

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
/-- Copy the zero result to the exact 16-byte formatting input, preserving the source and frame. -/
theorem copy_zero (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (n : Nat) (hn : mi.memAddrs[0]? = some n) (Cg R : Nat) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (ob : List UInt8) (hob : ob.length = 16) (Φ : Post NearState GF) :
    credits Cg (12 * cfg.regularOpCost + R) ∗
      n ↦[wms][ (s + 8).toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) ∗
      n ↦[wms][ (s + 128).toNat ] ob ∗
      ▷ (credits Cg R ∗
        n ↦[wms][ (s + 8).toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) ∗
        n ↦[wms][ (s + 128).toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8) -∗
        Φ.normal [] (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 101).take 12) Φ := by
  iintro ⟨Hc, Hsrc, Hdst, HΦ⟩
  have hlt := s.toNat_lt
  rw [copyCode_eq]
  simp only [copyCode, frame]
  ihave Hsrc := BorshFT.splitB (n := n) (a := (s + 8).toNat) (b := (s + 8).toNat + 8)
    (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8) (by rfl) $$ Hsrc
  icases Hsrc with ⟨S0, S8⟩
  ihave S8 := memBytes_addr (show (s + 8).toNat + 8 = (s + 16).toNat by simp [UInt32.toNat_add]; omega) $$ S8
  ihave Hdst := U128From.memBytes_split n (s + 128).toNat 8 ob (by omega) $$ Hdst
  icases Hdst with ⟨D0, D8⟩
  ihave D8 := memBytes_addr (show (s + 128).toNat + 8 = (s + 136).toNat by simp [UInt32.toNat_add]; omega) $$ D8
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [S8] with (simp [loadWidth, NumType.byteWidth])
  mstep [D8] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mstep; mstep
  mstep [S0] with (simp [loadWidth, NumType.byteWidth])
  mstep [D0] with (first | exact List.ne_nil_of_length_pos (by simp; omega) | (simp [storeWidth, NumType.byteWidth]; omega) | rfl)
  mcredits R
  have hz : UInt64.ofNat (Memory.decodeLE (storeBytes (.i64 0) 8)) = 0 := by decide
  simp only [hz]
  ihave S8 := memBytes_addr (show (s + 16).toNat = (s + 8).toNat + 8 by simp [UInt32.toNat_add]; omega) $$ S8
  ihave Hsrc := BorshFT.joinB (n := n) (a := (s + 8).toNat) (b := (s + 8).toNat + 8)
    (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8) (by rfl) $$ [S0 S8]
  · iframe S0 S8
  ihave D8 := memBytes_addr (show (s + 136).toNat = (s + 128).toNat + 8 by simp [UInt32.toNat_add]; omega) $$ D8
  ihave Hdst := BorshFT.joinB (n := n) (a := (s + 128).toNat) (b := (s + 128).toNat + 8)
    (storeBytes (.i64 0) 8) (storeBytes (.i64 0) 8) (by rfl) $$ [D0 D8]
  · iframe D0 D8
  iapply HΦ $$ [Hc Hsrc Hdst]
  iframe Hc Hsrc Hdst

open Near.TrieAccounting Near.TrieConstruction Near.TrieOverlay in
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- Compose the actual call and its following zero-copy instructions. -/
theorem call_and_copy_absent (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (e : Nat) (A : Nat → Nat) (n g ta : Nat) (mx : Option Nat) (hm : IfaceMod mi A n g ta)
    (hd : d + 20 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 : UInt32)
    (pp pc pl p c L : UInt32) (idx : UInt32) (maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) (hF : okG F)
    (pre key rest ob dest : List UInt8) (hs : 384 ≤ s.toNat) (hal : s.toNat % 8 = 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (hob : ob.length = 16) (hdest : dest.length = 16)
    (hpre : pre.length = pl.toNat) (hkey : key.length = L.toNat) (hrest : key.length + rest.length = c.toNat)
    (hc : c ≠ 0) (hL : L.toNat + 4 ≤ 120) (hpl : pl.toNat ≤ 4) (hl0 : 0 < pl.toNat)
    (hpp : pp.toNat + pl.toNat ≤ 2 ^ 32) (hp : p.toNat + c.toNat ≤ 2 ^ 32)
    (hroom : HeapRoomK 2 len maxP) (h : NearState) (st : Near.TrieOverlay.State) {bud : Nat}
    (hacc : h.storageAccounting = some st)
    (hlim : withinLimit h.config.maxStorageKeyLen (pre ++ (bytes32 L ++ key)).length = true)
    (hb : build st.entries = .ok st.base) (hz : zeroHash ∉ st.base.witness.map Prod.fst)
    (hlink : h.storage (pre ++ (bytes32 L ++ key)) =
      viewVal st (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))))
    (hproof : ProofBudget h st bud)
    (hbud : readProofCost (contractKey h.context.currentAccountId (pre ++ (bytes32 L ++ key))) (h.storage (pre ++ (bytes32 L ++ key))) ≤ bud)
    (hnone : h.storage (pre ++ (bytes32 L ++ key)) = none) (Φ : Post NearState GF) :
    code293 e n maxP inst mi A mx ∗ A 293 ↪[wf] FuncInst.wasm types[31]! inst f293 ∗
      credits Cg (2112 * cfg.regularOpCost + cost399None cfg F pl L h (pre ++ (bytes32 L ++ key)) + R) ∗
      pre293 n g ta A gt s (s + 8) (s + 48) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre key rest ob h [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] ∗
      n ↦[wms][ (s + 128).toNat ] dest ∗
      ▷ (∀ rs, (credits Cg R ∗ post293 n g ta A gt s (s + 8) ((s + 48) + 24) pp pc pl (s + 88) p c L
        idx maxP len live F pre (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)
        [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] rs ∗
        n ↦[wms][ (s + 128).toNat ] (storeBytes (.i64 0) 8 ++ storeBytes (.i64 0) 8)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3))
      ⊢ mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 91).take 22) Φ := by
  iintro ⟨#HC, #F293, Hc, HP, Hdest, HΦ⟩
  have hn := hm.mem
  have hseg : (f297.body.drop 91).take 22 =
      (f297.body.drop 91).take 10 ++ (f297.body.drop 101).take 12 := by rfl
  rw [hseg]
  iapply mwpi_seq
  iapply (call_absent cfg lim d inst mi e A n g ta mx hm hd Cg (12 * cfg.regularOpCost + R) gt s x1 x2 x3
    pp pc pl p c L idx maxP len live F hF pre key rest ob hs hal hframe hob hpre hkey hrest hc hL hpl hl0 hpp hp
    hroom h st hacc hlim hb hz hlink hproof hbud hnone)
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
  iapply (copy_zero cfg lim d inst mi n hn Cg R s x1 x2 x3 hframe dest hdest Φ)
  iframe Hc Hsrc Hdest
  inext
  iintro ⟨Hc, Hsrc, Hdest⟩
  ihave Hpost : post293 n g ta A gt s (s + 8) ((s + 48) + 24) pp pc pl (s + 88) p c L
      idx maxP len live F pre (StorageReadPost h (pre ++ (bytes32 L ++ key)) 0 st)
      [.i32 (s + 8), .i32 (s + 48), .i32 (s + 88)] [] $$ [Hg Hs HI Hvt Hinv Hm Hp Hv Hsrc Hhost]
  · iunfold post293
    iframe Hg Hs HI Hvt Hinv Hm Hp Hv Hsrc Hhost
    ipureintro; rfl
  ispecialize HΦ $$ %([] : List Value)
  iapply HΦ $$ [Hc Hpost Hdest]
  iframe Hc Hpost Hdest

end Spec
end WNear.Binary.BalanceOf297AbsentCall
