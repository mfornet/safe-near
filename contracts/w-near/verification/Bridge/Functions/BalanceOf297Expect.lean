import Bridge.Functions.BalanceOf297Compose
import Bridge.Functions.ResultExpect

/-! Unwrap the successful serialization in the actual balance export. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.AllocNewCell (memBytes_addr)

def expectCode : List Instr :=
  [.local_get 0, .i32_const 144, .i32_binop .add,
   .local_get 0, .i32_const 88, .i32_binop .add, .i32_const 1050984, .call 158]

theorem expectCode_eq : (f297.body.drop 120).take 8 = expectCode := by rfl

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Actual function-297 expect call for a successful serialized vector. -/
theorem expect_ok (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s x1 : UInt32) (x2 : UInt64) (x3 q L : UInt32)
    (ob : List UInt8) (hob : ob.length = 12) (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : Post NearState GF) :
    A 158 ↪[wf] FuncInst.wasm types[31]! inst f158 ∗ inst ↪[inst] mi ∗
      credits Cg (44 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
      n ↦[i32][ (s + 88).toNat ] 0 ∗ n ↦[i32][ (s + 88).toNat + 4 ] q ∗
      n ↦[i32][ (s + 88).toNat + 8 ] 128 ∗ n ↦[i32][ (s + 88).toNat + 12 ] L ∗
      n ↦[wms][ (s + 144).toNat ] ob ∗
      ▷ (∀ rs, (credits Cg R ∗ ⌜rs = []⌝ ∗ g ↦[wg] ⟨gt, .i32 s⟩ ∗
        n ↦[i32][ (s + 88).toNat ] 0 ∗
        n ↦[wms][ (s + 88).toNat + 4 ] (bytes32 q ++ bytes32 128 ++ bytes32 L) ∗
        n ↦[wms][ (s + 144).toNat ] (bytes32 q ++ bytes32 128 ++ bytes32 L)) -∗
        Φ.normal rs (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 120).take 8) Φ := by
  iintro ⟨#F158, #Hi, Hc, Hg, O0, O4, O8, O12, Ho, HΦ⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha158 := hm.funcs 158 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have hlt := s.toNat_lt
  ihave PL := BorshFT.joinB (a := (s + 88).toNat + 4) (b := (s + 88).toNat + 8)
    (bytes32 q) (bytes32 128) (by simp) $$ [O4 O8]
  · iframe O4 O8
  ihave PL := BorshFT.joinB (a := (s + 88).toNat + 4) (b := (s + 88).toNat + 12)
    (bytes32 q ++ bytes32 128) (bytes32 L) (by simp) $$ [PL O12]
  · iframe PL O12
  rw [expectCode_eq]
  simp only [expectCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (ResultExpect.f158_spec cfg lim (d + 1) types[31]! rfl inst mi n g hn hg Cg ⟨gt, .i32 s⟩
    s (s + 144) (s + 88) 1050984 rfl (by simp [UInt32.toNat_add]; omega) (by simp [UInt32.toNat_add]; omega)
    (bytes32 0) (bytes32 q ++ bytes32 128 ++ bytes32 L) ob (by simp) (by simp) hob (by simp [decodeLE_bytes32]))
    using [Hg O0 PL Ho]
  · iunfold ResultExpect.pre
    iframe Hg O0 PL Ho
    ipureintro; rfl
  iunfold ResultExpect.post at HQ
  icases HQ with ⟨%hrs, Hg, O0, PL, Ho⟩
  mcredits R
  ispecialize HΦ $$ %rs
  iapply HΦ $$ [Hc Hg O0 PL Ho]
  iframe Hc Hg O0 PL Ho
  ipureintro; exact hrs

end Spec
end WNear.Binary.BalanceOf297AbsentCall
