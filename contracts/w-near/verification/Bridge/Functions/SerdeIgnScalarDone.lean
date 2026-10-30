import Bridge.Functions.SerdeIgnContainer

/-! # Actual scalar completion and successful return of the ignored-value reader -/

namespace WNear.Binary.SerdeIgnScalarDone

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeIgnValue (fr81)

/-- The scalar's common completion tail, with the real optional saved-frame pop. -/
def scalarCode : List Instr :=
  [.i32_const 1, .local_set 3, .local_get 4, .i32_const 1, .i32_binop .and, .i32_eqz, .br_if 0,
   .local_get 1, .i32_const 8, .i32_binop .add, .local_get 2, .call 85,
   .local_get 1, .load .i32 (some ⟨8, false⟩) ⟨0, 8⟩, .i32_const 1, .i32_binop .and, .i32_eqz, .br_if 3,
   .local_get 1, .load .i32 (some ⟨8, false⟩) ⟨0, 9⟩, .local_set 8]

theorem scalarCode_at : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 2]).drop 1 = scalarCode := by rfl

/-- The success label installs result zero before leaving the outer block. -/
def successCode : List Instr := [.i32_const 0, .local_set 6]

theorem successCode_at : (SerdeIgnSegments.bodyAt f81.body [14]).drop 1 = successCode := by rfl

/-- The actual function-body epilogue restores the stack global and leaves local 6 as its result. -/
def returnCode : List Instr := [.local_get 1, .i32_const 32, .i32_binop .add, .global_set 0, .local_get 6]

theorem returnCode_at : f81.body.drop 15 = returnCode := by rfl

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
/-- A scalar inside a container uses the pending local frame without touching the saved vector. -/
theorem scalar_pending (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (Cg R : Nat) (de s l3 l6 l7 l8 : UInt32) (l5 : UInt64) (Fr : IProp GF) :
    credits Cg (7 * cfg.regularOpCost + R) ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 0 l5 l6 l7 l8) [] scalarCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 0 l5 l6 l7 l8⌝ ∗ Fr) } := by
  iintro ⟨Hc, HF⟩
  unfold scalarCode
  simp only [fr81]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  mcredits R
  iframe Hc HF
  ipureintro; trivial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- A top-level scalar pops the cleared vector and takes the actual empty-stack success branch. -/
theorem scalar_top (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (de s p cap l3 l6 l7 l8 : UInt32) (l5 : UInt64)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (Fr : IProp GF)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ credits Cg (50 * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 1 l5 l6 l7 l8) [] scalarCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 3 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 1 l5 l6 l7 l8⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗ Fr) } := by
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hs8 : (s + 8).toNat = s.toNat + 8 := by simp [UInt32.toNat_add]; omega
  iintro ⟨#HC, Hc, H32, Hst, HF⟩
  iunfold SerdeIgnValue.code81 at HC
  icases HC with ⟨#CN, -, -, -, #F85, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, -, -, -, -, -, #Hi⟩
  iunfold SerdeIgnStack.state at Hst
  icases Hst with ⟨D0, D4, D8, Hsb⟩
  have hn := hm.mem
  have ha85 := hm.funcs 85 (by decide)
  have t14 : types[14]!.params.length = 2 := rfl
  icases VecFromElem.stk_split n s.toNat 8 24 $$ H32 with ⟨H8, H24⟩
  icases VecFromElem.stk_split n (s.toNat + 8) 1 23 $$ H24 with ⟨P8, H23⟩
  icases VecFromElem.stk_split n (s.toNat + 8 + 1) 1 22 $$ H23 with ⟨P9, H22⟩
  iunfold stk at P8 P9
  icases P8 with ⟨%b8, %hb8, P8⟩
  icases P9 with ⟨%b9, %hb9, P9⟩
  obtain ⟨b8, rfl⟩ := List.length_eq_one_iff.mp hb8
  obtain ⟨b9, rfl⟩ := List.length_eq_one_iff.mp hb9
  have pop := SerdeIgnFrame.f85_empty (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi n hn Cg (s + 8) (de + 12)
    b8 b9 (by rw [hs8]; omega) (by rw [hd12]; omega)
  rw [hs8] at pop
  unfold scalarCode
  simp only [fr81]
  repeat mstep
  mcall pop using [D8 P8 P9]
  · iframe D8 P8 P9
  icases HQ with ⟨%hrs, D8, P8, P9⟩
  subst hrs
  clear pop
  repeat mstep
  mstep [P8] with omega
  simp only [SerdeKey.load8]
  mstep; mstep; mstep
  mstep_taken with decide
  mcredits R
  ihave Hst : SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] $$ [D0 D4 D8 Hsb]
  · iunfold SerdeIgnStack.state
    simp only [List.length_nil, List.reverse_nil]
    iframe D0 D4 D8 Hsb
  iframe Hc Hst HF
  isplitr
  · ipureintro; trivial
  ihave P8 := VecFromElem.stk_intro $$ P8
  ihave P9 := VecFromElem.stk_intro $$ P9
  ihave H23 := VecFromElem.stk_join n (s.toNat + 8 + 1) 1 22 $$ [P9 H22]
  · iframe P9 H22
  ihave H24 := VecFromElem.stk_join n (s.toNat + 8) 1 23 $$ [P8 H23]
  · iframe P8 H23
  iapply VecFromElem.stk_join n s.toNat 8 24
  iframe H8 H24

set_option maxRecDepth 100000 in
/-- The actual success epilogue returns zero and restores all 160 stack bytes, retaining scratch and live blocks. -/
theorem success_return (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (n g Cg R : Nat) (hg : mi.globalAddrs[0]? = some g) (gt : GlobalType)
    (de sp p cap l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (Fr : IProp GF) (hsp : 160 ≤ sp.toNat) :
    credits Cg (7 * cfg.regularOpCost + R) ∗ g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗
      stk n (sp.toNat - 160) 128 ∗ stk n (sp.toNat - 32) 32 ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de (sp - 32) l3 l4 l5 l6 l7 l8) [] (successCode ++ returnCode)
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [.i32 0] ∧ fr = fr81 inst mi de (sp - 32) l3 l4 l5 0 l7 l8⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
          SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗ Fr) } := by
  iintro ⟨Hc, Hg, H128, H32, Hst, HF⟩
  unfold successCode returnCode
  simp only [List.cons_append, List.nil_append, fr81]
  repeat mstep
  mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  mcredits R
  iframe Hc Hg Hst HF
  isplitr
  · ipureintro; trivial
  iapply VecFromElem.stk_join n (sp.toNat - 160) 128 32
  rw [show sp.toNat - 160 + 128 = sp.toNat - 32 by omega]
  iframe H128 H32

end Proof
end WNear.Binary.SerdeIgnScalarDone
