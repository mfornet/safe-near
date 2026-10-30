import Bridge.Functions.BalanceOf297ComposeReturn
import Bridge.Functions.DropVec

/-! Free the returned vector and prefix, then restore function 297's stack pointer. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.AllocInv (heapInv block)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.BorshFT (splitB split64')

def cleanupCode : List Instr :=
  [.local_get 0, .i32_const 144, .i32_binop .add, .call 68,
   .local_get 0, .i32_const 72, .i32_binop .add, .call 68,
   .local_get 0, .i32_const 160, .i32_binop .add, .global_set 0]

theorem cleanupCode_eq : (f297.body.drop 138).take 12 = cleanupCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Actual final instructions free both owned vectors and restore the stack global. -/
theorem cleanup (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg R : Nat) (gt : GlobalType)
    (s x1 : UInt32) (x2 : UInt64) (x3 q len pp pc pl : UInt32) (maxP hl F : Nat) (live : List (Nat × Nat))
    (qb pb : List UInt8) (hqb : qb.length = 128) (hpb : pb.length = pc.toNat) (hc : pc ≠ 0)
    (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : Post NearState GF) :
    dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (660 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      n ↦[wms][ (s + 144).toNat ] (bytes32 q ++ (bytes32 128 ++ bytes32 len)) ∗
      n ↦[wms][ (s + 72).toNat ] (bytes32 pp ++ (bytes32 pc ++ bytes32 pl)) ∗
      n ↦[wms][ q.toNat ] qb ∗ n ↦[wms][ pp.toNat ] pb ∗
      heapInv n maxP hl ((q.toNat, 128) :: (pp.toNat, pc.toNat) :: live) F ∗
      ▷ (credits Cg R ∗ g ↦[wg] ⟨gt, .i32 (s + 160)⟩ ∗
        n ↦[i32][ (s + 144).toNat ] q ∗ n ↦[i32][ (s + 144).toNat + 4 ] 128 ∗
        n ↦[i32][ (s + 144).toNat + 8 ] len ∗ n ↦[i32][ (s + 72).toNat ] pp ∗
        n ↦[i32][ (s + 72).toNat + 4 ] pc ∗ n ↦[i32][ (s + 72).toNat + 8 ] pl ∗
        heapInv n maxP hl live ((F + 1) + 1) -∗ Φ.normal [] (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 138).take 12) Φ := by
  iintro ⟨#Hcode, #F68, Hc, Hg, Hv, Hp, Hq, Hb, Hinv, HΦ⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hcode; icases Hcode with ⟨#Hi, -⟩; iexact Hi
  have hg := hm.glob
  have ha68 := hm.funcs 68 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have hlt := s.toNat_lt
  icases splitB (n := n) (a := (s + 144).toNat) (b := (s + 144).toNat + 4)
    (bytes32 q) (bytes32 128 ++ bytes32 len) (by simp) $$ Hv with ⟨V0, Vrest⟩
  icases split64' (n := n) (a := (s + 144).toNat + 4) (b := (s + 144).toNat + 8) 128 len (by omega)
    $$ Vrest with ⟨V4, V8⟩
  icases splitB (n := n) (a := (s + 72).toNat) (b := (s + 72).toNat + 4)
    (bytes32 pp) (bytes32 pc ++ bytes32 pl) (by simp) $$ Hp with ⟨P0, Prest⟩
  icases split64' (n := n) (a := (s + 72).toNat + 4) (b := (s + 72).toNat + 8) pc pl (by omega)
    $$ Prest with ⟨P4, P8⟩
  rw [cleanupCode_eq]
  simp only [cleanupCode, frame]
  mstep; mstep; mstep
  mcall (DropVec.f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
    ((q.toNat, 128) :: (pp.toNat, pc.toNat) :: live) F (s + 144) q 128 len (by decide)
    (by simp [UInt32.toNat_add]; omega)) using [V0 V4 V8 Hinv Hq]
  · iunfold pre747
    iframe V0 V4 V8 Hinv
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; simp
    iunfold block
    iexists qb
    iframe Hq
    ipureintro; exact hqb
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, V0, V4, V8, Hinv⟩
  subst hrs
  mstep; mstep; mstep
  have hlive : ((q.toNat, 128) :: (pp.toNat, pc.toNat) :: live).erase (q.toNat, 128) = (pp.toNat, pc.toNat) :: live := by simp
  rw [hlive]
  mcall (DropVec.f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
    ((pp.toNat, pc.toNat) :: live) (F + 1) (s + 72) pp pc pl hc
    (by simp [UInt32.toNat_add]; omega)) using [P0 P4 P8 Hinv Hb]
  · iunfold pre747
    iframe P0 P4 P8 Hinv
    isplitr; · ipureintro; rfl
    isplitr; · ipureintro; simp
    iunfold block
    iexists pb
    iframe Hb
    ipureintro; exact hpb
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, P0, P4, P8, Hinv⟩
  subst hrs
  mstep; mstep; mstep; mstep [Hg]
  mcredits R
  have hlive2 : ((pp.toNat, pc.toNat) :: live).erase (pp.toNat, pc.toNat) = live := by simp
  rw [hlive2]
  iapply HΦ $$ [Hc Hg V0 V4 V8 P0 P4 P8 Hinv]
  iframe Hc Hg V0 V4 V8 P0 P4 P8 Hinv

end Spec
end WNear.Binary.BalanceOf297AbsentCall
