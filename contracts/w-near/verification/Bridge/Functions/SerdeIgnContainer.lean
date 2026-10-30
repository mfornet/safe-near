import Bridge.Functions.SerdeIgnMember

/-! # The actual container-loop peek and delimiter dispatch in ignored values -/

namespace WNear.Binary.SerdeIgnContainer

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.IgnoreModel
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.SerdeRead (rd wsLen optByte)
open WNear.Binary.SerdeIgnValue (fr81)

/-- Parse whitespace and leave the successful optional-byte result in local 5. -/
def peekCode (escape : Nat) : List Instr :=
  [.block .empty [.local_get 0, .call 339, .local_tee 5, .i64_const 1, .i64_binop .and,
    .i64_eqz, .br_if 0, .local_get 5, .i64_const 32, .i64_binop .shr_u,
    .cvt .i32_wrap_i64, .local_set 6, .br escape]]

/-- The container loop uses escape label 6; the value loop uses escape label 4. -/
theorem peekCode_at : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 3, 0]).take 1 = peekCode 6 := by rfl

theorem valuePeekCode_at : (SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0]).take 1 = peekCode 4 := by rfl

/-- EOF's real dispatch, bypassed when a byte is present. -/
def presentBody : List Instr :=
  [.local_get 5, .i64_const 256, .i64_binop .and, .i64_const 0, .i64_relop .ne, .br_if 0,
   .local_get 8, .i32_const 255, .i32_binop .and, .local_tee 8, .i32_const 91, .i32_relop .eq, .br_if 1,
   .local_get 8, .i32_const 123, .i32_relop .eq, .br_if 2,
   .i32_const 1048586, .i32_const 40, .i32_const 1048728, .call 853, .unreachable]

def commaBody : List Instr :=
  [.local_get 6, .i32_const 125, .i32_relop .eq, .br_if 0,
   .local_get 6, .i32_const 44, .i32_relop .ne, .br_if 6,
   .local_get 3, .i32_const 1, .i32_binop .and, .i32_eqz, .br_if 8,
   .local_get 0, .call 333, .br 8]

def byteBody : List Instr :=
  [.block .empty presentBody, .local_get 5, .i64_const 16, .i64_binop .shr_u,
   .cvt .i32_wrap_i64, .i32_const 255, .i32_binop .and, .local_tee 6,
   .i32_const 93, .i32_relop .eq, .br_if 3, .block .empty commaBody,
   .local_get 8, .i32_const 255, .i32_binop .and, .i32_const 123, .i32_relop .eq, .br_if 4, .br 5]

def eofArrayBody : List Instr :=
  [.block .empty byteBody, .local_get 1, .i32_const 2, .store .i32 none ⟨2, 16⟩, .br 1]

def eofObjectBody : List Instr :=
  [.block .empty eofArrayBody, .local_get 1, .i32_const 3, .store .i32 none ⟨2, 16⟩]

def errorBody : List Instr :=
  [.block .empty eofObjectBody, .local_get 0, .local_get 1, .i32_const 16,
   .i32_binop .add, .call 322, .local_set 6, .br 8]

/-- Delimiter dispatch, ending immediately before the previously proved close segment. -/
def dispatchCode : List Instr :=
  [.block .empty [.block .empty errorBody, .local_get 8, .i32_const 255,
    .i32_binop .and, .i32_const 91, .i32_relop .ne, .br_if 1]]

theorem dispatchCode_at : SerdeIgnSegments.closingBlock.take 1 = dispatchCode := by rfl

/-- Leaving the container loop for its first element/member when no comma is required. -/
def exitCode : List Instr := [.local_get 3, .i32_const 1, .i32_binop .and, .i32_eqz, .br_if 0]

theorem exitCode_at : ((SerdeIgnSegments.bodyAt f81.body [14, 0, 0, 0, 3]).drop 1).take 5 = exitCode := by rfl

/-- The matching close byte of either represented container kind. -/
def closing (f : UInt8) : UInt8 := if f = 0x5B then 0x5D else 0x7D

section Proof
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- Both actual loop peeks preserve caller resources and stop at the first non-whitespace byte or EOF. -/
theorem peek_success (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 2 < lim.maxCallDepth)
    (Cg R escape : Nat) (de s ptr l3 l4 l6 l7 l8 : UInt32) (l5 : UInt64) (bs : List UInt8) (i : Nat)
    (Fr : IProp GF) (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32)
    (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗
      credits Cg ((125 + 96 * wsLen (bs.drop i)) * cfg.regularOpCost + R) ∗ rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 l5 l6 l7 l8) [] (peekCode escape)
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte bs[i + wsLen (bs.drop i)]?) l6 l7 l8⌝ ∗
          rd n de ptr bs (i + wsLen (bs.drop i)) ∗ Fr) } := by
  have reader := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! rfl inst mi n hm.mem
    (A 332) (A 333) (hm.funcs 332 (by decide)) (hm.funcs 333 (by decide)) (by omega) Cg de ptr bs i hi hlen hptr hde
  iintro ⟨#HC, Hc, Hrd, HF⟩
  iunfold SerdeIgnValue.code81 at HC
  icases HC with ⟨#CN, #F339, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, #F332, #F333, -, -, -, -, #Hi⟩
  have ha339 := hm.funcs 339 (by decide)
  have t11 : types[11]!.params.length = 1 := rfl
  simp only [Nat.add_mul] at reader ⊢
  generalize hW : 96 * wsLen (bs.drop i) * cfg.regularOpCost = W at reader ⊢
  unfold peekCode
  simp only [fr81]
  repeat mstep
  mcall reader using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  clear reader hW
  mstep; mstep; mstep; mstep
  mstep_taken with exact SerdeIgnInt.ne0 (by simp only [SerdeRead.optByte_ok]; rfl)
  mcredits R
  iframe Hc Hrd HF
  ipureintro; trivial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- A matching container close reaches the actual close segment, preserving every caller resource. -/
theorem dispatch_close (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (Cg R : Nat) (de s l3 l4 l6 l7 : UInt32) (f : UInt8) (hf : Br f) (Fr : IProp GF) :
    credits Cg (100 * cfg.regularOpCost + R) ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s l3 l4 (optByte (some (closing f))) l6 l7 f.toUInt32) [] dispatchCode
      { normal := fun vs fr => iprop(credits Cg R ∗
          ⌜vs = [] ∧ fr = fr81 inst mi de s l3 l4 (optByte (some (closing f))) (closing f).toUInt32 l7 f.toUInt32⌝ ∗ Fr) } := by
  rcases hf with rfl | rfl <;>
    simp only [show (0x5B : UInt8).toUInt32 = (0x5B : UInt32) from by decide +kernel,
      show (0x7B : UInt8).toUInt32 = (0x7B : UInt32) from by decide +kernel] <;>
    iintro ⟨Hc, HF⟩ <;>
    unfold dispatchCode errorBody eofObjectBody eofArrayBody byteBody commaBody presentBody <;>
    simp only [fr81, closing, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_true, ite_false] <;>
    repeat mstep
  all_goals mcredits R
  all_goals iframe Hc HF
  all_goals ipureintro; trivial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- A first element/member leaves the dispatch without consuming its first byte. -/
theorem dispatch_first (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (Cg R : Nat) (de s l4 l6 l7 l8 : UInt32) (c : UInt8)
    (h93 : c ≠ 0x5D) (h125 : c ≠ 0x7D) (h44 : c ≠ 0x2C) (Fr : IProp GF) :
    credits Cg (35 * cfg.regularOpCost + R) ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 0 l4 (optByte (some c)) l6 l7 l8) [] dispatchCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 0 l4 (optByte (some c)) c.toUInt32 l7 l8⌝ ∗ Fr) } := by
  have ht93 := SerdeIgnValue.t93 c
  rw [if_neg h93] at ht93
  have ht125 := SerdeIgnValue.t125 c
  rw [if_neg h125] at ht125
  have ht44 := SerdeIgnValue.t44 c
  rw [if_neg h44] at ht44
  iintro ⟨Hc, HF⟩
  unfold dispatchCode errorBody eofObjectBody eofArrayBody byteBody commaBody presentBody
  simp only [fr81]
  repeat mstep
  mstep_taken with exact SerdeIgnValue.some_ne c
  repeat mstep
  rw [SerdeIgnValue.ob16 c, SerdeIgnValue.band255 c]
  repeat mstep
  mcredits R
  iframe Hc HF
  ipureintro; trivial

set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
/-- An accepted comma is consumed and takes the actual exit toward the next member/value. -/
theorem dispatch_comma (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (A : Nat → Nat) (n g ta : Nat) (hm : IfaceMod mi A n g ta) (hd : d + 1 < lim.maxCallDepth)
    (Cg R : Nat) (de s ptr l4 l6 l7 l8 : UInt32) (bs : List UInt8) (i : Nat) (Fr : IProp GF)
    (hi : i < bs.length) (hlen : bs.length < 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32) :
    SerdeIgnValue.code81 (GF := GF) inst mi A ∗ credits Cg (65 * cfg.regularOpCost + R) ∗
      rd n de ptr bs i ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 1 l4 (optByte (some 0x2C)) l6 l7 l8) [] dispatchCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 2 ∧ vs = [] ∧ fr = fr81 inst mi de s 1 l4 (optByte (some 0x2C)) 0x2C l7 l8⌝ ∗
          rd n de ptr bs (i + 1) ∗ Fr) } := by
  iintro ⟨#HC, Hc, Hrd, HF⟩
  iunfold SerdeIgnValue.code81 at HC
  icases HC with ⟨#CN, -⟩
  iunfold SerdeIgnNum.numCode at CN
  icases CN with ⟨-, -, #F333, -, -, -, -, #Hi⟩
  have hn := hm.mem
  have ha333 := hm.funcs 333 (by decide)
  have t0 : types[0]!.params.length = 1 := rfl
  unfold dispatchCode errorBody eofObjectBody eofArrayBody byteBody commaBody presentBody
  simp only [fr81]
  repeat mstep
  mcall (SerdeRead.f333_spec (GF := GF) cfg lim (d + 1) types[0]! rfl inst mi n hn Cg de ptr bs i hi hlen hde)
    using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  repeat mstep
  mcredits R
  iframe Hc Hrd HF
  ipureintro; trivial

set_option maxRecDepth 100000 in
/-- The actual post-loop guard sends a first element/member to the member tail. -/
theorem first_exit (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (inst : Nat) (mi : ModuleInst)
    (Cg R : Nat) (de s l4 l6 l7 l8 : UInt32) (l5 : UInt64) (Fr : IProp GF) :
    credits Cg (5 * cfg.regularOpCost + R) ∗ Fr ⊢
    mwpi cfg lim d (fr81 inst mi de s 0 l4 l5 l6 l7 l8) [] exitCode
      { normal := fun _ _ => iprop(False)
        br := fun k vs fr => iprop(credits Cg R ∗
          ⌜k = 0 ∧ vs = [] ∧ fr = fr81 inst mi de s 0 l4 l5 l6 l7 l8⌝ ∗ Fr) } := by
  iintro ⟨Hc, HF⟩
  unfold exitCode
  simp only [fr81]
  mstep; mstep; mstep; mstep
  mstep_taken with decide
  mcredits R
  iframe Hc HF
  ipureintro; trivial

/-- A closing delimiter or comma cannot be the next value in the complete pure machine. -/
theorem value_bad (N : Nat) (frames : List UInt8) (c : UInt8) (t : List UInt8)
    (hc : c = 0x5D ∨ c = 0x7D ∨ c = 0x2C) :
    SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val frames (c :: t) = none := by
  cases N with
  | zero => rfl
  | succ N =>
    have hw : NearInterface.Json.isWhitespace c = false := by rcases hc with rfl | rfl | rfl <;> rfl
    have hv := SerdeIgnPure.vSkip_close (x := t) hc
    rcases hc with rfl | rfl | rfl <;>
      simp only [SerdeIgnMachineTrace.run, WNear.JsonFuel.skip_of_not t hw, hv, Option.bind_none] <;>
      split <;> simp_all

/-- Neither a closing delimiter nor a comma can begin an ignored object key. -/
theorem key_bad {α : Type} (c : UInt8) (t : List UInt8) (k : List UInt8 → Option α)
    (hc : c = 0x5D ∨ c = 0x7D ∨ c = 0x2C) :
    SerdeIgnMachineTrace.key SerdeIgnMachineTrace.keyBody (c :: t) k = none := by
  have hw : NearInterface.Json.isWhitespace c = false := by rcases hc with rfl | rfl | rfl <;> rfl
  rcases hc with rfl | rfl | rfl <;>
    simp only [SerdeIgnMachineTrace.key, WNear.JsonFuel.skip_of_not t hw] <;>
    split <;> simp_all

/-- Classify a complete traced container transition using the same three branches as the actual dispatch. -/
theorem phase_cases (N : Nat) (opened : Bool) (f c : UInt8) (frames bs t r : List UInt8)
    (ops : List SerdeIgnTrace.Op) (hf : Br f)
    (hs : NearInterface.Json.skipWhitespace bs = c :: t)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened f else .cont f) frames bs = some (r, ops)) :
    (c = closing f ∧ SerdeIgnMachineTrace.pop true frames t
      (fun g frames t => SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N (.cont g) frames t) = some (r, ops)) ∨
    (opened = true ∧ c ≠ 0x5D ∧ c ≠ 0x7D ∧ c ≠ 0x2C ∧
      SerdeIgnMember.nextModel N f frames (c :: t) = some (r, ops)) ∨
    (opened = false ∧ c = 0x2C ∧ SerdeIgnMember.nextModel N f frames t = some (r, ops)) := by
  cases opened
  · simp only [Bool.false_eq_true, ite_false, SerdeIgnMachineTrace.run] at h
    rw [hs] at h
    split at h
    · rename_i t' he
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      right; right
      refine ⟨rfl, rfl, ?_⟩
      rcases hf with rfl | rfl <;> simpa only [SerdeIgnMember.nextModel,
        show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_true, ite_false] using h
    · rename_i t' he
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rcases hf with rfl | rfl
      · left; exact ⟨rfl, h⟩
      · simp at h
    · rename_i t' he
      obtain ⟨rfl, rfl⟩ := List.cons.inj he
      rcases hf with rfl | rfl
      · simp at h
      · left; exact ⟨rfl, h⟩
    · cases h
  · simp only [ite_true, SerdeIgnMachineTrace.run] at h
    rw [hs] at h
    rcases hf with rfl | rfl
    · simp only [ite_true] at h
      by_cases hc : c = 0x5D
      · subst hc
        left
        simpa only [closing, ite_true] using (show (0x5D : UInt8) = 0x5D ∧ _ from ⟨rfl, h⟩)
      · have hn : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val (0x5B :: frames) (c :: t) = some (r, ops) := by
          split at h
          · rename_i t' he
            exact absurd (List.cons.inj he).1 hc
          · exact h
        right; left
        refine ⟨rfl, hc, ?_, ?_, ?_⟩
        · intro he; subst he; rw [value_bad N _ _ _ (Or.inr (Or.inl rfl))] at hn; cases hn
        · intro he; subst he; rw [value_bad N _ _ _ (Or.inr (Or.inr rfl))] at hn; cases hn
        · simpa only [SerdeIgnMember.nextModel, ite_true] using hn
    · simp only [show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at h
      by_cases hc : c = 0x7D
      · subst hc
        left
        simpa only [closing, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] using
          (show (0x7D : UInt8) = 0x7D ∧ _ from ⟨rfl, h⟩)
      · have hn : SerdeIgnMember.nextModel N 0x7B frames (c :: t) = some (r, ops) := by
          unfold SerdeIgnMember.nextModel
          rw [if_neg (by decide)]
          split at h
          · rename_i t' he
            exact absurd (List.cons.inj he).1 hc
          · exact h
        right; left
        refine ⟨rfl, ?_, hc, ?_, hn⟩
        · intro he; subst he
          simp only [SerdeIgnMember.nextModel, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at hn
          rw [key_bad _ _ _ (Or.inl rfl)] at hn; cases hn
        · intro he; subst he
          simp only [SerdeIgnMember.nextModel, show ¬ ((0x7B : UInt8) = 0x5B) from by decide, ite_false] at hn
          rw [key_bad _ _ _ (Or.inr (Or.inr rfl))] at hn; cases hn

/-- A complete value transition cannot succeed on empty input, even with pending saved frames. -/
theorem value_nil (N : Nat) (frames : List UInt8) :
    SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody N .val frames [] = none := by
  cases N with
  | zero => rfl
  | succ N =>
    simp only [SerdeIgnMachineTrace.run, NearInterface.Json.skipWhitespace, List.dropWhile_nil,
      SerdeIgnPure.vSkip_nil, Option.bind_none]

/-- EOF cannot finish either container phase of the complete traced machine. -/
theorem phase_eof (N : Nat) (opened : Bool) (f : UInt8) (frames bs : List UInt8)
    (hs : NearInterface.Json.skipWhitespace bs = []) :
    SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened f else .cont f) frames bs = none := by
  cases opened
  · simp only [Bool.false_eq_true, ite_false, SerdeIgnMachineTrace.run]
    rw [hs]
  · simp only [ite_true, SerdeIgnMachineTrace.run]
    rw [hs]
    split
    · exact value_nil N _
    · rfl

/-- Successful container phases always supply the byte consumed by the concrete peek/dispatch contracts. -/
theorem phase_nonempty (N : Nat) (opened : Bool) (f : UInt8) (frames bs r : List UInt8)
    (ops : List SerdeIgnTrace.Op)
    (h : SerdeIgnMachineTrace.run vSkip SerdeIgnMachineTrace.keyBody (N + 1)
      (if opened then .opened f else .cont f) frames bs = some (r, ops)) :
    ∃ c t, NearInterface.Json.skipWhitespace bs = c :: t := by
  cases hs : NearInterface.Json.skipWhitespace bs with
  | nil => rw [phase_eof N opened f frames bs hs] at h; cases h
  | cons c t => exact ⟨c, t, rfl⟩

end Proof
end WNear.Binary.SerdeIgnContainer
