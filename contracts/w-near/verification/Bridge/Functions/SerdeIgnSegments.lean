import Bridge.Functions.SerdeIgnMachineStack
import Bridge.Functions.SerdeIgnValue

/-! # Concrete state-changing segments of the complete ignored-value reader -/

namespace WNear.Binary.SerdeIgnSegments

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.SerdeIgnValue (fr81)
open WNear.Binary.SerdeIgnMachineStack

/-- The instructions inside one structured control instruction. -/
def inside : Instr → List Instr
  | .block _ es => es
  | .loop _ es => es
  | _ => []

/-- Follow a path through the decoded body's structured control instructions. -/
def bodyAt (es : List Instr) : List Nat → List Instr
  | [] => es
  | i :: path => bodyAt (inside es[i]!) path

/-- Function 81's prologue clears reusable scratch before the value loop. -/
def startCode : List Instr :=
  [.global_get 0, .i32_const 32, .i32_binop .sub, .local_tee 1, .global_set 0,
   .local_get 0, .i32_const 12, .i32_binop .add, .local_tee 2, .call 82,
   .i32_const 0, .local_set 3, .i32_const 1, .local_set 4]

theorem startCode_eq : f81.body.take 14 = startCode := by rfl

/-- The actual enclosing block of the nested-opening tail. -/
noncomputable def openingBlock : List Instr := bodyAt f81.body [14, 0, 0, 0, 2, 0, 0]

/-- Save the optional pending frame, eat the opening byte, and install the new current frame. -/
def openCode : List Instr :=
  [.local_get 2, .local_get 3, .i32_const 1, .i32_binop .and, .local_get 8, .call 84,
   .local_get 0, .call 333, .i32_const 0, .local_set 3, .local_get 7, .local_set 8]

/-- This segment, including its following branch, is taken from the actual decoded 81 body. -/
theorem openingBlock_tail : openingBlock.drop 1 = openCode ++ [.br 2] := by rfl

/-- The actual closing segment's enclosing dispatch block. -/
noncomputable def closingBlock : List Instr := bodyAt f81.body [14, 0, 0, 0, 3, 0, 1]

/-- Eat a closing delimiter, pop the saved stack, test for completion, and restore a present frame. -/
def closeCode : List Instr :=
  [.local_get 0, .call 333, .local_get 1, .local_get 2, .call 85, .local_get 1,
   .load .i32 (some ⟨8, false⟩) ⟨0, 0⟩, .i32_const 1, .i32_binop .and, .i32_eqz, .br_if 5,
   .local_get 1, .load .i32 (some ⟨8, false⟩) ⟨0, 1⟩, .local_set 8, .i32_const 1, .local_set 3]

/-- The checked closing segment is followed by the actual branch back to the container loop. -/
theorem closingBlock_tail : closingBlock.drop 1 = closeCode ++ [.br 1] := by rfl

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- Code required by the full reader and its scratch-frame growth calls. -/
def code (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(SerdeIgnValue.code81 inst mi A ∗ SerdeIgnReserve.code n maxP inst mi A)

instance (n maxP inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code (GF := GF) n maxP inst mi A) := by
  unfold code; infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The actual reader entry clears arbitrary scratch contents while preserving its allocation and live blocks. -/
theorem start_prefix_tight (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp de p cap : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (old : List UInt8) (hsp : 160 ≤ sp.toNat)
    (hde : de.toNat + 24 ≤ 2 ^ 32) :
    code (GF := GF) n maxP inst mi A ∗ credits Cg (53 * cfg.regularOpCost + R) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap old ⊢
    mwpi cfg lim d ⟨entryLocals f81 [.i32 de], inst, mi⟩ [] startCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de (sp - 32) 0 1 0 0 0 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗ stk n (sp.toNat - 160) 128 ∗ stk n (sp.toNat - 32) 32 ∗
          SerdeIgnStack.state n maxP hl live F (de + 12) p cap []) } := by
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hentry : entryLocals f81 [.i32 de] = #[.i32 de, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i32 0, .i32 0] := rfl
  have key := SerdeIgnStack.f343_clear (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi A n g ta hm
    (by omega) Cg (de + 12) p cap maxP hl F live old (by rw [hd12]; omega)
  iintro ⟨#HC, Hc, Hg, H160, Hst⟩
  iunfold code at HC
  icases HC with ⟨#C81, -⟩
  iunfold SerdeIgnValue.code81 at C81
  icases C81 with ⟨#CN, -, #F82, #F674, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, -, -, -, -, -, #Hi⟩
  have hg := hm.glob
  have ha82 := hm.funcs 82 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  unfold startCode
  rw [hentry]
  mstep [Hg]
  repeat mstep
  mstep [Hg]
  repeat mstep
  mcall key using [Hst]
  · iframe Hst
  icases HQ with ⟨%hrs, Hst⟩
  subst hrs
  clear key
  repeat mstep
  mcredits R
  iframe Hc Hg Hst
  isplitr
  · ipureintro; trivial
  icases VecFromElem.stk_split n (sp.toNat - 160) 128 32 $$ H160 with ⟨H128, H32⟩
  rw [show sp.toNat - 160 + 128 = sp.toNat - 32 by omega]
  iframe H128 H32

set_option maxRecDepth 100000 in
/-- The original entry allowance follows from the tight 53-operation prologue. -/
theorem start_prefix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (sp de p cap : UInt32) (maxP hl F : Nat)
    (live : List (Nat × Nat)) (old : List UInt8) (hsp : 160 ≤ sp.toNat)
    (hde : de.toNat + 24 ≤ 2 ^ 32) :
    code (GF := GF) n maxP inst mi A ∗ credits Cg (60 * cfg.regularOpCost + R) ∗
      g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 160) 160 ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap old ⊢
    mwpi cfg lim d ⟨entryLocals f81 [.i32 de], inst, mi⟩ [] startCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de (sp - 32) 0 1 0 0 0 0⌝ ∗
          g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗ stk n (sp.toNat - 160) 128 ∗ stk n (sp.toNat - 32) 32 ∗
          SerdeIgnStack.state n maxP hl live F (de + 12) p cap []) } := by
  iintro ⟨#HC, Hc, Hg, H160, Hst⟩
  iapply start_prefix_tight cfg lim d inst mi A n g ta hm hd Cg R gt sp de p cap maxP hl F live old hsp hde
  iframe HC Hg H160 Hst
  iapply BorrowMut.credits_le
  iframe Hc
  ipureintro; omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- The real opening segment moves from value-mode vector ownership to opened-container ownership. -/
theorem open_prefix (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 : UInt32) (l5 : UInt64)
    (opened : UInt8) (maxP hl F : Nat) (live : List (Nat × Nat)) (frames : List UInt8)
    (bs : List UInt8) (i : Nat) (hs : 80 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hi : i < bs.length)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1) :
    code (GF := GF) n maxP inst mi A ∗ credits Cg (60 * cfg.regularOpCost + saveCost cfg F cap frames + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ⊢
    mwpi cfg lim d
      (fr81 inst mi de s (flag frames) l4 l5 l6 opened.toUInt32 (current fallback frames)) [] openCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 l5 l6 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (i + 1)) } := by
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hflag : flag frames &&& 1 = flag frames := by cases frames <;> simp only [flag] <;> decide +kernel
  have key := f84_save (GF := GF) cfg lim (d + 1) types[31]! rfl inst mi A n g ta hm (by omega) Cg gt s
    (de + 12) p cap idx fallback maxP hl F live frames opened hs (by rw [hd12]; omega) hcap hframes hr
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd⟩
  iunfold code at HC
  icases HC with ⟨#C81, #CR⟩
  iunfold SerdeIgnValue.code81 at C81
  icases C81 with ⟨#CN, -, -, -, -, #F84, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, #F333, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha84 := hm.funcs 84 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t31 : types[31]!.params.length = 3 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  generalize hK : saveCost cfg F cap frames = K at key ⊢
  unfold openCode
  simp only [fr81]
  repeat mstep
  rw [hflag]
  mcall key using [Hg H80 Hvt Hst]
  · iframe Hg H80 Hvt Hst
  icases HQ with ⟨%hrs, %p', %hl', %hh, Hg, H80, Hvt, Hst⟩
  subst hrs
  clear key hK
  repeat mstep
  mcall (SerdeRead.f333_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs i hi hlen
    (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc
  isplitr
  · ipureintro; trivial
  iexists p', hl'
  iframe Hg H80 Hvt Hst Hrd
  ipureintro; exact hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- A nested close restores the saved head and retains the changed heap/capacity in the actual loop. -/
theorem close_nonempty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (s de ptr p cap l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64) (f : UInt8)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (frames bs : List UInt8) (i : Nat)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hi : i < bs.length) :
    code (GF := GF) n maxP inst mi A ∗ credits Cg (110 * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (f :: frames) ∗
      rd n de ptr bs i ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 l8) [] closeCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 1 l4 l5 l6 l7 f.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗
          rd n de ptr bs (i + 1)) } := by
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  iintro ⟨#HC, Hc, H32, Hst, Hrd⟩
  iunfold code at HC
  icases HC with ⟨#C81, -⟩
  iunfold SerdeIgnValue.code81 at C81
  icases C81 with ⟨#CN, -, -, -, #F85, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, #F333, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha85 := hm.funcs 85 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t14 : types[14]!.params.length = 2 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  icases VecFromElem.stk_split n s.toNat 1 31 $$ H32 with ⟨P0, H31⟩
  icases VecFromElem.stk_split n (s.toNat + 1) 1 30 $$ H31 with ⟨P1, H30⟩
  iunfold stk at P0 P1
  icases P0 with ⟨%b0, %hb0, P0⟩
  icases P1 with ⟨%b1, %hb1, P1⟩
  obtain ⟨b0, rfl⟩ := List.length_eq_one_iff.mp hb0
  obtain ⟨b1, rfl⟩ := List.length_eq_one_iff.mp hb1
  unfold closeCode
  simp only [fr81]
  repeat mstep
  mcall (SerdeRead.f333_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs i hi hlen
    (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  repeat mstep
  mcall (SerdeIgnStack.f85_pop (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi n hn Cg s (de + 12) p cap
    maxP hl F live (f :: frames) b0 b1 (by omega) (by rw [hd12]; omega)) using [Hst P0 P1]
  · iframe Hst P0 P1
  icases HQ with ⟨%hrs, Hst, P0, P1⟩
  subst hrs
  simp only [SerdeIgnStack.popped]
  repeat mstep
  mstep [P0] with omega
  simp only [SerdeKey.load8]
  repeat mstep
  mstep [P1] with omega
  simp only [SerdeKey.load8]
  repeat mstep
  mcredits R
  iframe Hc Hst Hrd
  isplitr
  · ipureintro; trivial
  ihave P0 := VecFromElem.stk_intro $$ P0
  ihave P1 := VecFromElem.stk_intro $$ P1
  ihave H31 := VecFromElem.stk_join n (s.toNat + 1) 1 30 $$ [P1 H30]
  · iframe P1 H30
  iapply VecFromElem.stk_join n s.toNat 1 31
  iframe P0 H31

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Closing the last container takes 81's actual success branch and retains its scratch allocation. -/
theorem close_empty (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (s de ptr p cap l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64)
    (maxP hl F : Nat) (live : List (Nat × Nat)) (bs : List UInt8) (i : Nat)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hi : i < bs.length) :
    code (GF := GF) n maxP inst mi A ∗ credits Cg (110 * cfg.regularOpCost + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
      rd n de ptr bs i ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 l8) [] closeCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 5 ∧ vs = [] ∧ fr = fr81 inst mi de s l3 l4 l5 l6 l7 l8⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap [] ∗
          rd n de ptr bs (i + 1)) } := by
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  iintro ⟨#HC, Hc, H32, Hst, Hrd⟩
  iunfold code at HC
  icases HC with ⟨#C81, -⟩
  iunfold SerdeIgnValue.code81 at C81
  icases C81 with ⟨#CN, -, -, -, #F85, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, #F333, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha85 := hm.funcs 85 (by decide)
  have ha333 := hm.funcs 333 (by decide)
  have t14 : types[14]!.params.length = 2 := rfl
  have t0 : types[0]!.params.length = 1 := rfl
  icases VecFromElem.stk_split n s.toNat 1 31 $$ H32 with ⟨P0, H31⟩
  icases VecFromElem.stk_split n (s.toNat + 1) 1 30 $$ H31 with ⟨P1, H30⟩
  iunfold stk at P0 P1
  icases P0 with ⟨%b0, %hb0, P0⟩
  icases P1 with ⟨%b1, %hb1, P1⟩
  obtain ⟨b0, rfl⟩ := List.length_eq_one_iff.mp hb0
  obtain ⟨b1, rfl⟩ := List.length_eq_one_iff.mp hb1
  unfold closeCode
  simp only [fr81]
  repeat mstep
  mcall (SerdeRead.f333_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs i hi hlen
    (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  repeat mstep
  mcall (SerdeIgnStack.f85_pop (GF := GF) cfg lim (d + 1) types[14]! rfl inst mi n hn Cg s (de + 12) p cap
    maxP hl F live [] b0 b1 (by omega) (by rw [hd12]; omega)) using [Hst P0 P1]
  · iframe Hst P0 P1
  icases HQ with ⟨%hrs, Hst, P0, P1⟩
  subst hrs
  simp only [SerdeIgnStack.popped]
  repeat mstep
  mstep [P0] with omega
  simp only [SerdeKey.load8]
  mstep; mstep; mstep
  mstep_taken with decide
  mcredits R
  iframe Hc Hst Hrd
  isplitr
  · ipureintro; trivial
  ihave P0 := VecFromElem.stk_intro $$ P0
  ihave P1 := VecFromElem.stk_intro $$ P1
  ihave H31 := VecFromElem.stk_join n (s.toNat + 1) 1 30 $$ [P1 H30]
  · iframe P1 H30
  iapply VecFromElem.stk_join n s.toNat 1 31
  iframe P0 H31

/-- Invert the pending-frame save while retaining its exact operation prefix. -/
theorem save_some {frames r : List UInt8} {ops : List SerdeIgnTrace.Op}
    {res : Option SerdeIgnMachineTrace.Result} (h : SerdeIgnMachineTrace.save frames res = some (r, ops)) :
    ∃ ops', res = some (r, ops') ∧ ops = saveOps frames ops' := by
  cases frames with
  | nil => exact ⟨ops, h, rfl⟩
  | cons f frames =>
    simp only [SerdeIgnMachineTrace.save, SerdeIgnMachineTrace.mark, Option.map_eq_some_iff] at h
    obtain ⟨⟨r', ops'⟩, hr, he⟩ := h
    cases he
    exact ⟨ops', hr, rfl⟩

set_option maxRecDepth 100000 in
/-- The opening segment consumes precisely the traced save charge and preserves the successful continuation. -/
theorem open_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 14 < lim.maxCallDepth)
    (Cg R : Nat) (gt : GlobalType) (s de ptr p cap idx fallback l4 l6 : UInt32) (l5 : UInt64)
    (opened : UInt8) (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i : Nat) (hs : 80 ≤ s.toNat) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hcap : cap.toNat < 2 ^ 27) (hlen : bs.length < 2 ^ 32) (hi : i < bs.length)
    (hframes : (physical .val frames).length + 1 < 2 ^ 27)
    (hr : frames ≠ [] → ScratchGrow.roomRes hl maxP cap (UInt32.ofNat (physical .val frames).length) 1)
    (hmodel : SerdeIgnMachineTrace.save frames
      (SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.opened opened) frames (bs.drop (i + 1))) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (200 * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R) ∗
      g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
      SerdeIgnStack.state n maxP hl live F (de + 12) p cap (physical .val frames) ∗ rd n de ptr bs i ⊢
    mwpi cfg lim d
      (fr81 inst mi de s (flag frames) l4 l5 l6 opened.toUInt32 (current fallback frames)) [] openCode
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = saveOps frames ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.opened opened) frames (bs.drop (i + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 0 l4 l5 l6 opened.toUInt32 opened.toUInt32⌝ ∗
          ∃ (p' : UInt32) (hl' : Nat), ⌜saveHL hl hl' cap frames⌝ ∗
          g ↦[wg] ⟨gt, .i32 s⟩ ∗ stk n (s.toNat - 80) 80 ∗ AllocFirstFit.vt n 1057464 idx ta (A 578) ∗
          SerdeIgnStack.state n maxP hl' live (saveF F cap frames) (de + 12) p' (saveCap cap frames)
            (physical (.opened opened) frames) ∗ rd n de ptr bs (i + 1)) } := by
  obtain ⟨ops', hsub, hops⟩ := save_some hmodel
  have hsave := saveCost_le cfg F cap frames
  have hcost : 60 * cfg.regularOpCost + saveCost cfg F cap frames +
      (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' + R) ≤
      200 * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (physical .val frames).length ops + R := by
    rw [hops, save_extraCost]
    omega
  iintro ⟨#HC, Hc, Hg, H80, Hvt, Hst, Hrd⟩
  iapply mwpi_wand
  isplitl [Hc Hg H80 Hvt Hst Hrd]
  · iapply open_prefix cfg lim d inst mi A n g ta hm hd Cg
      (SerdeIgnTrace.extraCost cfg (saveF F cap frames) (saveCap cap frames) frames.length ops' + R)
      gt s de ptr p cap idx fallback l4 l6 l5 opened maxP hl F live frames bs i hs hde hcap hlen hi hframes hr
    iframe HC Hg H80 Hvt Hst Hrd
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; exact hcost
  iunfold Post.wand
  isplit
  · iintro %vs %fr H
    iexists ops'
    isplitr
    · ipureintro; exact ⟨hops, hsub⟩
    iexact H
  isplit
  · iintro %k %vs %fr H; iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

/-- Invert a nonempty saved-frame restoration, retaining its actual vector-pop prefix. -/
theorem restore_some {f : UInt8} {frames r t : List UInt8} {ops : List SerdeIgnTrace.Op}
    {k : UInt8 → List UInt8 → List UInt8 → Option SerdeIgnMachineTrace.Result}
    (h : SerdeIgnMachineTrace.pop true (f :: frames) t k = some (r, ops)) :
    ∃ ops', k f frames t = some (r, ops') ∧ ops = false :: ops' := by
  simp only [SerdeIgnMachineTrace.pop, ite_true, SerdeIgnMachineTrace.mark, Option.map_eq_some_iff] at h
  obtain ⟨⟨r', ops'⟩, hr, he⟩ := h
  cases he
  exact ⟨ops', hr, rfl⟩

set_option maxRecDepth 100000 in
/-- A real nested close restores the traced continuation without changing capacity or allocator bounds. -/
theorem close_traced (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth) (Cg R : Nat)
    (s de ptr p cap l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64) (f : UInt8)
    (maxP hl F N : Nat) (live : List (Nat × Nat)) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (i : Nat)
    (hs : s.toNat + 32 ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hlen : bs.length < 2 ^ 32) (hi : i < bs.length)
    (hmodel : SerdeIgnMachineTrace.pop true (f :: frames) (bs.drop (i + 1))
      (fun g frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont g) frames t) = some (r, ops)) :
    code (GF := GF) n maxP inst mi A ∗
      credits Cg (110 * cfg.regularOpCost + SerdeIgnTrace.extraCost cfg F cap (f :: frames).length ops + R) ∗
      stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap (f :: frames) ∗
      rd n de ptr bs i ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 l8) [] closeCode
      { normal := fun vs fr => iprop(∃ ops',
          ⌜ops = false :: ops' ∧ SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N
            (.cont f) frames (bs.drop (i + 1)) = some (r, ops')⌝ ∗
          credits Cg (SerdeIgnTrace.extraCost cfg F cap frames.length ops' + R) ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s 1 l4 l5 l6 l7 f.toUInt32⌝ ∗
          stk n s.toNat 32 ∗ SerdeIgnStack.state n maxP hl live F (de + 12) p cap frames ∗
          rd n de ptr bs (i + 1)) } := by
  obtain ⟨ops', hsub, hops⟩ := restore_some hmodel
  iintro ⟨#HC, Hc, H32, Hst, Hrd⟩
  rw [hops, pop_extraCost]
  iapply mwpi_wand
  isplitl [Hc H32 Hst Hrd]
  · iapply close_nonempty cfg lim d inst mi A n g ta hm hd Cg
      (SerdeIgnTrace.extraCost cfg F cap frames.length ops' + R) s de ptr p cap l3 l4 l6 l7 l8 l5 f
      maxP hl F live frames bs i hs hde hlen hi
    iframe HC H32 Hst Hrd
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iunfold Post.wand
  isplit
  · iintro %vs %fr H
    iexists ops'
    isplitr
    · ipureintro; exact ⟨rfl, hsub⟩
    iexact H
  isplit
  · iintro %k %vs %fr H; iexact H
  isplit
  · iintro %vs %fr H; iexact H
  · iintro H; iexact H

end Proof
end WNear.Binary.SerdeIgnSegments
