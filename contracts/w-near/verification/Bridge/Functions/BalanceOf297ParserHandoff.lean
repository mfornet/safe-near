import Bridge.Functions.BalanceOf297RoomF
import Bridge.Functions.FromSliceSpec

/-! Transfer the successful parser result into function 297's balance argument. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.DropVec (dropCode pre747 post747)
open WNear.Binary.AllocInv (heapInv block heapInv_perm)
open WNear.Binary.AllocNewCell (memBytes_addr)
open WNear.Binary.BorshFT (join64' split64')
open WNear.Binary.VecFromElem (pair64 storeBytes_pair64 ofNat_decode_pair)

def parserHandoffCode : List Instr :=
  [.block .empty [.local_get 0, .load .i32 none ⟨2, 88⟩, .i32_const 1, .i32_relop .ne, .br_if 0,
    .local_get 0, .local_get 0, .load .i32 none ⟨2, 92⟩, .store .i32 none ⟨2, 128⟩,
    .i32_const 1050760, .i32_const 38, .local_get 0, .i32_const 128, .i32_binop .add,
    .i32_const 1049036, .i32_const 1050984, .call 881, .unreachable],
   .local_get 0, .i32_const 128, .i32_binop .add, .i32_const 8, .i32_binop .add,
   .local_get 0, .i32_const 100, .i32_binop .add, .load .i32 none ⟨2, 0⟩, .local_tee 1,
   .store .i32 none ⟨2, 0⟩, .local_get 0, .local_get 0, .load .i64 none ⟨2, 92⟩,
   .local_tee 2, .store .i64 none ⟨3, 128⟩, .local_get 0, .i32_const 32, .i32_binop .add,
   .i32_const 8, .i32_binop .add, .local_tee 3, .local_get 1, .store .i32 none ⟨2, 0⟩,
   .local_get 0, .local_get 2, .store .i64 none ⟨3, 32⟩, .local_get 0, .i32_const 48,
   .i32_binop .add, .call 68]

theorem parserHandoffCode_eq : (f297.body.drop 36).take 32 = parserHandoffCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 32000000 in
/-- The actual success branch copies the parsed descriptor and frees the input vector. -/
theorem parser_handoff (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg R : Nat)
    (s x1 : UInt32) (x2 : UInt64) (x3 p c L ip ic il : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (oldA oldB : List UInt8) (oldC oldD : UInt32) (hA : oldA.length = 8) (hB : oldB.length = 8)
    (hc : ic ≠ 0) (hs : s.toNat + 160 ≤ 2 ^ 32) (hal : s.toNat % 8 = 0)
    (Φ : Post NearState GF) :
    dropCode inst mi A ∗ A 68 ↪[wf] FuncInst.wasm types[0]! inst f68 ∗
      credits Cg (400 * cfg.regularOpCost + R) ∗
      n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] p ∗
      n ↦[i32][ (s + 88).toNat + 8 ] c ∗ n ↦[i32][ (s + 88).toNat + 12 ] L ∗
      n ↦[wms][ (s + 128).toNat ] oldA ∗ n ↦[i32][ (s + 128).toNat + 8 ] oldC ∗
      n ↦[wms][ (s + 32).toNat ] oldB ∗ n ↦[i32][ (s + 32).toNat + 8 ] oldD ∗
      n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 48).toNat + 8 ] il ∗ block n ip.toNat ic.toNat ∗
      heapInv n maxP hl ((ip.toNat, ic.toNat) :: (p.toNat, c.toNat) :: live) F ∗
      ▷ (credits Cg R ∗ n ↦[i32][ (s + 88).toNat ] 0 ∗
        n ↦[wms][ (s + 88).toNat + 4 ] (bytes32 p ++ bytes32 c) ∗ n ↦[i32][ (s + 88).toNat + 12 ] L ∗
        n ↦[wms][ (s + 128).toNat ] (bytes32 p ++ bytes32 c) ∗ n ↦[i32][ (s + 128).toNat + 8 ] L ∗
        n ↦[wms][ (s + 32).toNat ] (bytes32 p ++ bytes32 c) ∗ n ↦[i32][ (s + 32).toNat + 8 ] L ∗
        n ↦[i32][ (s + 48).toNat ] ip ∗ n ↦[i32][ (s + 48).toNat + 4 ] ic ∗
        n ↦[i32][ (s + 48).toNat + 8 ] il ∗
        heapInv n maxP hl ((p.toNat, c.toNat) :: live) (F + 1) -∗
        Φ.normal [] (frame inst mi s L (pair64 p c) (s + 40))) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 36).take 32) Φ := by
  iintro ⟨#Hcode, #F68, Hc, Tag, P, C, L0, A0, A8, B0, B8, I0, I4, I8, Hb, Hinv, HΦ⟩
  ihave #Hi : inst ↪[inst] mi $$ []
  · iunfold dropCode at Hcode; icases Hcode with ⟨#Hi, -⟩; iexact Hi
  have hn := hm.mem
  have ha68 := hm.funcs 68 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  have hlt := s.toNat_lt
  ihave PC := join64' (a := (s + 88).toNat + 4) (b := (s + 88).toNat + 8) p c (by omega) $$ [P C]
  · iframe P C
  rw [parserHandoffCode_eq]
  simp only [parserHandoffCode, frame]
  mstep
  mstep; mstep [Tag]; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep [L0]; mstep; mstep [A8]
  mstep; mstep; mstep [PC]; mstep; mstep [A0]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep [B8]
  mstep; mstep; mstep [B0]
  rw [ofNat_decode_pair, storeBytes_pair64]
  mstep; mstep; mstep
  mcall (DropVec.f68_spec cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm (by omega) Cg maxP hl
    ((ip.toNat, ic.toNat) :: (p.toNat, c.toNat) :: live) F (s + 48) ip ic il hc
    (by simp [UInt32.toNat_add]; omega)) using [I0 I4 I8 Hinv Hb] with (mstep_norm_full; omega)
  · iunfold pre747
    iframe I0 I4 I8 Hinv Hb
    isplitr; · ipureintro; rfl
    ipureintro; simp
  iunfold post747 at HQ
  icases HQ with ⟨%hrs, I0, I4, I8, Hinv⟩
  subst hrs
  mcredits R
  simp only [List.erase_cons_head]
  rw [show s + 32 + 8 = s + 40 by rw [UInt32.add_assoc]; rfl]
  iapply HΦ $$ [Hc Tag PC L0 A0 A8 B0 B8 I0 I4 I8 Hinv]
  iframe Hc Tag PC L0 A0 A8 B0 B8 I0 I4 I8 Hinv
end Spec
end WNear.Binary.BalanceOf297AbsentCall
