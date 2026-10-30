import Bridge.Functions.BalanceOf297DerefCompose
import Bridge.Functions.ArgsLeaves

/-! Copy a present input vector out of the input option in function 297. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.ArgsLeaves (pre157 post157)

def inputExpectCode : List Instr :=
  [.local_get 0, .i32_const 48, .i32_binop .add, .local_get 0,
   .i32_const 88, .i32_binop .add, .i32_const 1050984, .call 157]

theorem inputExpectCode_eq : (f297.body.drop 13).take 8 = inputExpectCode := by rfl
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- The actual input `expect` call copies a non-null vector descriptor. -/
theorem input_expect (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n : Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[157]? = some (A 157))
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat) (s x1 : UInt32) (x2 : UInt64) (x3 ip ic il : UInt32)
    (old : List UInt8) (hold : old.length = 12) (hp : ip ≠ 0) (hframe : s.toNat + 160 ≤ 2 ^ 32)
    (Φ : Post NearState GF) :
    inst ↪[inst] mi ∗ A 157 ↪[wf] FuncInst.wasm types[31]! inst f157 ∗
      credits Cg (100 * cfg.regularOpCost + R) ∗ n ↦[wms][ (s + 48).toNat ] old ∗
      n ↦[i32][ (s + 88).toNat ] ip ∗ n ↦[i32][ (s + 88).toNat + 4 ] ic ∗
      n ↦[i32][ (s + 88).toNat + 8 ] il ∗
      ▷ (credits Cg R ∗ n ↦[i32][ (s + 88).toNat ] ip ∗ n ↦[i32][ (s + 88).toNat + 4 ] ic ∗
        n ↦[i32][ (s + 88).toNat + 8 ] il ∗ n ↦[i32][ (s + 48).toNat ] ip ∗
        n ↦[i32][ (s + 48).toNat + 4 ] ic ∗ n ↦[i32][ (s + 48).toNat + 8 ] il -∗
        Φ.normal [] (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 13).take 8) Φ := by
  iintro ⟨#Hi, #F157, Hc, Hout, O0, O4, O8, HΦ⟩
  have hlt := s.toNat_lt
  have t31 : types[31]!.params.length = 3 := rfl
  rw [inputExpectCode_eq]
  simp only [inputExpectCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mcall (ArgsLeaves.f157_spec cfg lim (d + 1) types[31]! rfl inst mi n hn Cg (s + 48) (s + 88)
    ip ic il old hold hp (by simp [UInt32.toNat_add]; omega) (by simp [UInt32.toNat_add]; omega))
    using [Hout O0 O4 O8]
  · iunfold pre157
    iframe Hout O0 O4 O8
    ipureintro; exact ⟨1050984, rfl⟩
  iunfold post157 at HQ
  icases HQ with ⟨%hrs, O0, O4, O8, V0, V4, V8⟩
  subst hrs
  mcredits R
  iapply HΦ $$ [Hc O0 O4 O8 V0 V4 V8]
  iframe Hc O0 O4 O8 V0 V4 V8
end Spec
end WNear.Binary.BalanceOf297AbsentCall
