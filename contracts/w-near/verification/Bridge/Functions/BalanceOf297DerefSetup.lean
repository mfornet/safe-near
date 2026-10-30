import Bridge.Functions.BalanceOf297CopiedCall
import Bridge.Functions.VecDerefAuto

/-! Dereference the input vector and prepare the deployed parser-call arguments. -/
namespace WNear.Binary.BalanceOf297AbsentCall
open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.BorshFT (split64' join64')
open WNear.Binary.AllocNewCell (memBytes_addr)

def derefSetupCode : List Instr :=
  [.local_get 0, .i32_const 24, .i32_binop .add, .local_get 0, .i32_const 48, .i32_binop .add, .call 779,
   .local_get 0, .i32_const 88, .i32_binop .add, .local_get 0, .load .i32 none ⟨2, 24⟩,
   .local_get 0, .load .i32 none ⟨2, 28⟩]

theorem derefSetupCode_eq : (f297.body.drop 21).take 14 = derefSetupCode := by rfl
section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]
set_option maxRecDepth 1000000 in
set_option maxHeartbeats 16000000 in
/-- The deployed dereference and argument setup produce exactly the parser-call stack. -/
theorem deref_and_parser_setup (cfg : WasmConfig) (lim : ExecLimits) (d inst : Nat) (mi : ModuleInst) (A : Nat → Nat)
    (n : Nat) (hn : mi.memAddrs[0]? = some n) (ha : mi.funcAddrs[779]? = some (A 779))
    (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat) (s x1 : UInt32) (x2 : UInt64) (x3 ip ic il : UInt32)
    (old : List UInt8) (hold : old.length = 8) (hframe : s.toNat + 160 ≤ 2 ^ 32) (Φ : Post NearState GF) :
    inst ↪[inst] mi ∗ A 779 ↪[wf] FuncInst.wasm types[14]! inst f779 ∗
      credits Cg (100 * cfg.regularOpCost + R) ∗ n ↦[wms][ (s + 24).toNat ] old ∗
      n ↦[wms][ (s + 48).toNat ] (bytes32 ip ++ (bytes32 ic ++ bytes32 il)) ∗
      ▷ (credits Cg R ∗ n ↦[i32][ (s + 24).toNat ] ip ∗ n ↦[i32][ (s + 24).toNat + 4 ] il ∗
        n ↦[wms][ (s + 48).toNat ] (bytes32 ip ++ (bytes32 ic ++ bytes32 il)) -∗
        Φ.normal [.i32 (s + 88), .i32 ip, .i32 il] (frame inst mi s x1 x2 x3)) ⊢
    mwpi cfg lim d (frame inst mi s x1 x2 x3) [] ((f297.body.drop 21).take 14) Φ := by
  iintro ⟨#Hi, #F779, Hc, Hout, Hvec, HΦ⟩
  have hlt := s.toNat_lt
  have t14 : types[14]!.params.length = 2 := rfl
  rw [derefSetupCode_eq]
  simp only [derefSetupCode, frame]
  mstep; mstep; mstep; mstep; mstep; mstep
  mcall (VecDerefAuto.f779_spec cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s + 24) (s + 48) old
    (bytes32 ip ++ (bytes32 ic ++ bytes32 il)) hold (by simp)) using [Hout Hvec]
  · iunfold VecDeref.pre
    iframe Hout Hvec
    ipureintro; rfl
  iunfold VecDeref.post at HQ
  icases HQ with ⟨%hrs, Hout, Hvec⟩
  subst hrs
  have hvb : ∀ (a b c : UInt32), (bytes32 a ++ (bytes32 b ++ bytes32 c)).take 4 ++
      (bytes32 a ++ (bytes32 b ++ bytes32 c)).drop 8 = bytes32 a ++ bytes32 c := by
    intro a b c; simp [List.take_append, List.drop_append, bytes32_length]
  rw [hvb]
  icases split64' (n := n) (a := (s + 24).toNat) (b := (s + 24).toNat + 4) ip il (by omega) $$ Hout with ⟨P, L⟩
  mstep; mstep; mstep; mstep; mstep [P]; mstep; mstep [L]
  mcredits R
  iapply HΦ $$ [Hc P L Hvec]
  iframe Hc P L Hvec
end Spec
end WNear.Binary.BalanceOf297AbsentCall
