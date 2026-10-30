import Bridge.Functions.SerdeIgnInt
import Bridge.Functions.SerdeIdent
import Bridge.Functions.SerdeIgnFrame
import Bridge.Functions.SerdeIgnPure
import Bridge.Functions.SerdeStructObj

/-!
# `ignore_value` (81) on the shallow values (M6)

`ignore_value` (81) skips one value iteratively (`IgnoreModel`). On a value that pushes no frame,
a scalar or one bracket of scalars (`IgnoreShallow.ign1`), its loops are:

```wat
;; 81 ignore_value(de) -> i32        (a 32-byte frame; l2 = &scratch, l3 = accept_comma, l4 = top,
;;                                    l8 = the frame's bracket)
clear the scratch (82); l3 := 0; l4 := 1
loop @4                                ;; a value
  ws (339); EOF → error
  '"' → 650 | '-' → 83 | digit → 83 | 't' 'f' 'n' → 323 | '[' '{' → push l8 if l3 (84), l8 := b → CONT
  scalar done: l3 := 1; l4 → CONT; else pop (85) → None → return 0
  CONT: loop @6  ws; ']' '}' matching l8 → eat, pop → None → return 0
                 ',' (l3) → eat, break; other (not l3) → break
  break: l4 := 0; l3 := 1; l8 = '{' → ws '"' 650 ws ':'; continue @4
```

* `f81_shallow`: where `ign1` skips a value from `j` to the rest `r` (on an input without `\`), 81
  returns `0` with the reader at `|bs| - |r|`, within `(166 + 470 · (|bs| - |r| - j))·c`.
-/

namespace WNear.Binary.SerdeIgnValue

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.Interface (IfaceMod)
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr stk_intro)
open WNear.Binary.SerdeRead (rd optByte byteOrNull wsLen)
open WNear.Binary.SerdeIgnNum (numCode)
open WNear.Binary.SerdeStructArr (tbl)
open WNear.IgnoreShallow (scal cont1 open1 ign1 sk)
open WNear.IgnoreModel (Br vSkip keyThen)
open NearInterface.Json (isDigit isWhitespace skipWhitespace stringBody)

/-! ## The byte tests -/

theorem ob16 (b : UInt8) : (optByte (some b) >>> (16 % 64)).toUInt32 = b.toUInt32 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem band255 (b : UInt8) : b.toUInt32 &&& 255 = b.toUInt32 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem some_ne (b : UInt8) : Numeric.bool (Numeric.irelop64 IRelOp.ne (optByte (some b) &&& 256) 0) ≠ 0 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

section Split

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}

/-- Run `es₁`, and from where it falls through (`N`), `es₂`. -/
theorem mwpi_split (es₁ es₂ : List Instr) {Φ : Post NearState GF} (N : List Value → Frame → IProp GF) :
    mwpi cfg lim d f vs es₁ { Post.mseq cfg lim d es₂ Φ with normal := N } ∗
      (∀ vs' g, N vs' g -∗ mwpi cfg lim d g vs' es₂ Φ) ⊢ mwpi cfg lim d f vs (es₁ ++ es₂) Φ := by
  iintro ⟨H1, H2⟩
  iapply mwpi_seq
  iapply mwpi_wand
  isplitl [H1]
  · iexact H1
  iunfold Post.wand
  isplit
  · iintro %vs' %g HN
    dsimp only [Post.mseq_normal]
    iapply H2 $$ HN
  isplit
  · iintro %n %vs' %g H; iexact H
  isplit
  · iintro %vs' %g H; iexact H
  · iintro H; iexact H

theorem mwpi_split1 {a : Instr} {es : List Instr} {Φ : Post NearState GF} (N : List Value → Frame → IProp GF) :
    mwpi cfg lim d f vs [a] { Post.mseq cfg lim d es Φ with normal := N } ∗
      (∀ vs' g, N vs' g -∗ mwpi cfg lim d g vs' es Φ) ⊢ mwpi cfg lim d f vs (a :: es) Φ :=
  mwpi_split [a] es N

theorem mwpi_split3 {a b c : Instr} {es : List Instr} {Φ : Post NearState GF} (N : List Value → Frame → IProp GF) :
    mwpi cfg lim d f vs [a, b, c] { Post.mseq cfg lim d es Φ with normal := N } ∗
      (∀ vs' g, N vs' g -∗ mwpi cfg lim d g vs' es Φ) ⊢ mwpi cfg lim d f vs (a :: b :: c :: es) Φ :=
  mwpi_split [a, b, c] es N

end Split

section Defs

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code 81 runs on a shallow value. -/
def code81 (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(numCode inst mi A ∗ A 339 ↪[wf] FuncInst.wasm types[11]! inst f339 ∗
    A 82 ↪[wf] FuncInst.wasm types[0]! inst f343 ∗ A 674 ↪[wf] FuncInst.wasm types[14]! inst f674 ∗
    A 85 ↪[wf] FuncInst.wasm types[14]! inst f85 ∗ A 84 ↪[wf] FuncInst.wasm types[31]! inst f84 ∗
    VecAppend.appCode inst mi A ∗ A 650 ↪[wf] FuncInst.wasm types[32]! inst f650 ∗
    A 323 ↪[wf] FuncInst.wasm types[15]! inst f323 ∗ A 673 ↪[wf] FuncInst.wasm types[31]! inst f673 ∗
    A 83 ↪[wf] FuncInst.wasm types[32]! inst f83)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (code81 (GF := GF) inst mi A) := by
  unfold code81; infer_instance

/-- 81's frame. -/
def fr81 (inst : Nat) (mi : ModuleInst) (de s l3 l4 : UInt32) (l5 : UInt64) (l6 l7 l8 : UInt32) : Frame :=
  ⟨#[.i32 de, .i32 s, .i32 (de + 12), .i32 l3, .i32 l4, .i64 l5, .i32 l6, .i32 l7, .i32 l8], inst, mi⟩

/-- The shallow ignored reader's scratch descriptor and read-only tables. -/
def scratchTables (n : Nat) (de ptrS capS : UInt32) : IProp GF :=
  iprop((∃ sl : UInt32, n ↦[i32][ de.toNat + 20 ] sl) ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
    n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[i32][ de.toNat + 12 ] ptrS ∗
    n ↦[i32][ de.toNat + 16 ] capS ∗ n ↦[wms][ 1048576 ] SerdeIdent.identBytes)

/-- What 81 keeps through its loops: globals, stack, empty scratch of any capacity, and tables. -/
def P81 (n g : Nat) (gt : GlobalType) (sp de ptrS capS : UInt32) : IProp GF :=
  iprop(g ↦[wg] ⟨gt, .i32 (sp - 32)⟩ ∗ stk n (sp.toNat - 32) 32 ∗ stk n (sp.toNat - 96) 64 ∗
    n ↦[i32][ de.toNat + 20 ] 0 ∗ n ↦[wms][ 1062392 ] ParseStr.escTable ∗
    n ↦[wms][ 1071704 ] FromUtf8Gen.utf8Width ∗ n ↦[i32][ de.toNat + 12 ] ptrS ∗ n ↦[i32][ de.toNat + 16 ] capS ∗
    n ↦[wms][ 1048576 ] SerdeIdent.identBytes)

/-- The value loop's invariant: the first value (`top`, at `j`), or a value inside the frame `f`. -/
def inv4 (n g inst : Nat) (mi : ModuleInst) (Cg c₀ : Nat) (gt : GlobalType) (sp de ptr ptrS capS : UInt32)
    (bs : List UInt8) (j : Nat) (r : List UInt8) (T0 Ein R : Nat) : List Value → Frame → IProp GF := fun X fr =>
  iprop(⌜X = []⌝ ∗
    ((∃ (l5 : UInt64) (l6 l7 l8 : UInt32), ⌜fr = fr81 inst mi de (sp - 32) 0 1 l5 l6 l7 l8⌝ ∗
      credits Cg (T0 * c₀ + 470 * (bs.length - r.length - j) * c₀ + R) ∗ rd n de ptr bs j ∗ P81 n g gt sp de ptrS capS) ∨
    (∃ (p : Nat) (l5 : UInt64) (l6 l7 : UInt32) (fb : UInt8) (N : Nat),
      ⌜fr = fr81 inst mi de (sp - 32) 1 0 l5 l6 l7 fb.toUInt32 ∧ Br fb ∧ p ≤ bs.length ∧
        (scal (bs.drop p)).bind (cont1 fb N) = some r⌝ ∗
      credits Cg (Ein * c₀ + 470 * (bs.length - r.length - p) * c₀ + R) ∗ rd n de ptr bs p ∗ P81 n g gt sp de ptrS capS)))

/-- After a value or a bracket: the container's loop (`op`: just opened). -/
def contSt (n g inst : Nat) (mi : ModuleInst) (Cg c₀ : Nat) (gt : GlobalType) (sp de ptr ptrS capS : UInt32)
    (bs : List UInt8) (r : List UInt8) (Eo Ec R : Nat) : Frame → IProp GF := fun fr =>
  iprop(∃ (p : Nat) (l3 l4 : UInt32) (l5 : UInt64) (l6 l7 : UInt32) (fb : UInt8) (N : Nat) (op : Bool),
    ⌜fr = fr81 inst mi de (sp - 32) l3 l4 l5 l6 l7 fb.toUInt32 ∧ Br fb ∧ p ≤ bs.length ∧
      (if op then l3 = 0 ∧ l4 = 1 ∧ open1 fb N (bs.drop p) = some r
       else l3 = 1 ∧ l4 = 0 ∧ cont1 fb N (bs.drop p) = some r)⌝ ∗
    credits Cg ((if op = true then (if fb = 0x5B then Eo else 200) else Ec) * c₀ + 470 * (bs.length - r.length - p) * c₀ + R) ∗
    rd n de ptr bs p ∗ P81 n g gt sp de ptrS capS)

/-- After a break out of the container's loop: the next element (`[`), or the next member's key (`{`). -/
def brkSt (n g inst : Nat) (mi : ModuleInst) (Cg c₀ : Nat) (gt : GlobalType) (sp de ptr ptrS capS : UInt32)
    (bs : List UInt8) (r : List UInt8) (Eb R : Nat) : Frame → IProp GF := fun fr =>
  iprop(∃ (p : Nat) (l3 l4 : UInt32) (l5 : UInt64) (l6 l7 : UInt32) (fb : UInt8) (N : Nat),
    ⌜fr = fr81 inst mi de (sp - 32) l3 l4 l5 l6 l7 fb.toUInt32 ∧ Br fb ∧ p ≤ bs.length ∧
      (fb = 0x5B → (scal (bs.drop p)).bind (cont1 fb N) = some r) ∧
      (fb = 0x7B → keyThen sk (bs.drop p) (fun r3 => (scal r3).bind (cont1 fb N)) = some r)⌝ ∗
    credits Cg ((if fb = 0x5B then Eb else 0) * c₀ + 470 * (bs.length - r.length - p) * c₀ + R) ∗ rd n de ptr bs p ∗ P81 n g gt sp de ptrS capS)

end Defs

theorem t93 (c : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq c.toUInt32 93) = if c = 0x5D then 1 else 0 := by
  revert c; exact SerdeRead.uint8_forall (by decide +kernel)

theorem t125 (c : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.eq c.toUInt32 125) = if c = 0x7D then 1 else 0 := by
  revert c; exact SerdeRead.uint8_forall (by decide +kernel)

theorem t44 (c : UInt8) : Numeric.bool (Numeric.irelop32 IRelOp.ne c.toUInt32 44) = if c = 0x2C then 0 else 1 := by
  revert c; exact SerdeRead.uint8_forall (by decide +kernel)

theorem dig_ne {b : UInt8} (hd : isDigit b = true) {k : UInt32} (hk : k.toNat < 48 ∨ 57 < k.toNat) :
    b.toUInt32 ≠ k := by
  intro h
  have := SerdeNumModel.isDigit_range hd
  have e := congrArg UInt32.toNat h
  simp at e
  omega

theorem eqb_zero {a k : UInt32} (h : a ≠ k) : Numeric.bool (Numeric.irelop32 IRelOp.eq a k) = 0 := by
  simp [Numeric.bool, Numeric.irelop32, h]

theorem dig_lt (b : UInt8) (hd : isDigit b = true) :
    Numeric.bool (Numeric.irelop32 IRelOp.lt_u (b.toUInt32 + 4294967248 &&& 255) 10) ≠ 0 := by
  revert b hd; exact SerdeRead.uint8_forall (by decide +kernel)

set_option hygiene false in
/-- Close the state at the end of the value block (`contSt`, after a value, at `p1`). -/
local macro "n3close" : tactic => `(tactic| (
  isplitr
  · ipureintro; trivial
  iunfold contSt
  iexists p1
  iexists 1
  iexists 0
  iexists _
  iexists _
  iexists _
  iexists fb
  iexists N
  iexists false
  isplitr
  · ipureintro
    refine ⟨rfl, hfb, by omega, ?_⟩
    show (1 : UInt32) = 1 ∧ (0 : UInt32) = 0 ∧ cont1 fb N (bs.drop p1) = some r
    exact ⟨rfl, rfl, by rw [hp1]; exact hc1⟩
  simp only [Bool.false_eq_true, ite_false]
  rw [hWq]
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hrd
  iunfold P81
  iframe Hg S81 SB D20 He Hw D12 D16 Hid))

set_option hygiene false in
/-- A scalar inside a frame is done: `l3 := 1`, `l4 = 0`, out of the value block. -/
local macro "sdIn" : tactic => `(tactic| (
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with decide
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  n3close))

set_option hygiene false in
/-- The first value was a scalar: `l3 := 1`, `l4 = 1`, so pop the empty scratch (85): `None`, return 0. -/
local macro "sdTop" : tactic => `(tactic| (
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with decide
  icases stk_split n (sp.toNat - 32) 8 24 $$ S81 with ⟨S0, S8⟩
  icases stk_split n (sp.toNat - 32 + 8) 1 23 $$ S8 with ⟨P8, S9⟩
  icases stk_split n (sp.toNat - 32 + 8 + 1) 1 22 $$ S9 with ⟨P9, S10⟩
  iunfold stk at P8 P9
  icases P8 with ⟨%c8, %hc8, P8⟩
  icases P9 with ⟨%c9, %hc9, P9⟩
  obtain ⟨x8, rfl⟩ := List.length_eq_one_iff.mp hc8
  obtain ⟨x9, rfl⟩ := List.length_eq_one_iff.mp hc9
  have h8 : (sp - 32 + 8).toNat = sp.toNat - 32 + 8 := by rw [UInt32.toNat_add, h32]; simp; omega
  have s85 := SerdeIgnFrame.f85_empty (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 32 + 8)
    (de + 12) x8 x9 (by omega) (by omega)
  rw [h8, hd12, show de.toNat + 12 + 8 = de.toNat + 20 by omega] at s85
  mstep; mstep; mstep; mstep
  mcall s85 using [D20 P8 P9]
  · iframe D20 P8 P9
  icases HQ with ⟨%hrs, D20, P8, P9⟩
  subst hrs
  mstep
  mstep [P8] with (rw [h32]; omega)
  simp only [SerdeKey.load8]
  mstep; mstep; mstep
  mstep_taken with decide
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg
  isplitr
  · ipureintro; simp [htype]
  isplitl [SB S0 P8 P9 S10]
  · ihave P8 := stk_intro $$ P8
    ihave P9 := stk_intro $$ P9
    rw [show ([0] : List UInt8).length = 1 by rfl]
    ihave S9 := stk_join n (sp.toNat - 32 + 8 + 1) 1 22 $$ [P9 S10]
    · iframe P9 S10
    ihave S8 := stk_join n (sp.toNat - 32 + 8) 1 (1 + 22) $$ [P8 S9]
    · iframe P8 S9
    ihave S81 := stk_join n (sp.toNat - 32) 8 (1 + (1 + 22)) $$ [S0 S8]
    · iframe S0 S8
    ihave S81 := stk_addr (show sp.toNat - 32 = sp.toNat - 96 + 64 by omega) $$ S81
    iapply stk_join n (sp.toNat - 96) 64 (8 + (1 + (1 + 22)))
    iframe SB S81
  isplitl [Hrd]
  · rw [← hp1q]; iexact Hrd
  iunfold scratchTables
  iframe He Hw D12 D16 Hid
  iexists 0
  iexact D20))

set_option hygiene false in
/-- The first value is a bracket: the credits by byte, 339, and the dispatch up to its first test. -/
local macro "brPre" : tactic => `(tactic| (
  generalize hp : j = p at hop hw hb hlt hdr hws hsk hwle hj
  have hq1 : p + w + 1 ≤ bs.length - r.length := by
    have := IgnoreShallow.vSkip_strict (IgnoreShallow.open1_sound _ (by first | exact Or.inl rfl | exact Or.inr rfl) _ hop)
    simp at this; omega
  rw [show 470 * (bs.length - r.length - p) * cfg.regularOpCost =
    96 * w * cfg.regularOpCost + (374 * w * cfg.regularOpCost + (470 * cfg.regularOpCost +
      470 * (bs.length - r.length - (p + w + 1)) * cfg.regularOpCost)) by
    rw [show bs.length - r.length - p = w + 1 + (bs.length - r.length - (p + w + 1)) by omega]; ring]
  generalize hWS : 96 * w * cfg.regularOpCost = WS
  generalize hX1 : 374 * w * cfg.regularOpCost = X1
  generalize hWq : 470 * (bs.length - r.length - (p + w + 1)) * cfg.regularOpCost = Wq
  have s339 := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) ha333 (by omega) Cg de ptr bs p (by omega) hlen hptr (by omega)
  rw [hw, Nat.add_mul, hWS] at s339
  mstep; mstep
  mcall s339 using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hb]
  mstep; mstep; mstep; mstep
  mstep_taken with exact SerdeIgnInt.ne0 (by simp only [SerdeRead.optByte_ok]; rfl)
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with exact some_ne _
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [ob16, band255]))

set_option hygiene false in
/-- The first value is a bracket: no frame pushed (84 with the flag 0), eat it, the container's loop. -/
local macro "brTail" : tactic => `(tactic| (
  icases stk_split n (sp.toNat - 96) 48 16 $$ SB with ⟨SB1, SB2⟩
  ihave SB2 := stk_addr (show sp.toNat - 96 + 48 = (sp - 32).toNat - 16 by omega) $$ SB2
  have s84 := SerdeIgnFrame.f84_none (GF := GF) cfg lim (d + 1) types[31]! (by rfl) inst mi A n g ta hm (by omega) Cg gt
    (sp - 32) (de + 12) ptrS 0 capS l8 (by omega) (by omega) (by simp)
  rw [hd12, show de.toNat + 12 + 4 = de.toNat + 16 by omega, show de.toNat + 12 + 8 = de.toNat + 20 by omega] at s84
  ihave #S84 := s84 $$ HA
  clear s84
  mstep; mstep; mstep; mstep; mstep
  mcall S84 using [Hg SB2 D12 D16 D20]
  · iframe Hg SB2 D12 D16 D20
    ipureintro; (first | rfl | simp)
  icases HQ with ⟨%hrs, Hg, SB2, D12, D16, D20⟩
  subst hrs
  ihave SB2 := stk_addr (show (sp - 32).toNat - 16 = sp.toNat - 96 + 48 by omega) $$ SB2
  ihave SB := stk_join n (sp.toNat - 96) 48 16 $$ [SB1 SB2]
  · iframe SB1 SB2
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
    (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mstep; mstep; mstep; mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  isplitr
  · ipureintro; trivial
  iunfold contSt
  iexists p + w + 1
  iexists 0
  iexists 1
  iexists _
  iexists _
  iexists _
  iexists _
  iexists (bs.drop p).length
  iexists true
  isplitr
  · ipureintro
    refine ⟨rfl, by first | exact Or.inl rfl | exact Or.inr rfl, by omega, ?_⟩
    rw [if_pos rfl]
    exact ⟨rfl, rfl, hop⟩
  rw [hWq]
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; (try split) <;> (try split) <;> omega
  iframe Hrd
  iunfold P81
  iframe Hg S81 SB D20 He Hw D12 D16 Hid))

set_option hygiene false in
/-- The container closes at `p + w` (the reader there): eat, pop the empty scratch (85), return 0. -/
local macro "closeTail" : tactic => `(tactic| (
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
    (by omega)) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  icases stk_split n (sp.toNat - 32) 1 31 $$ S81 with ⟨P0, S1⟩
  icases stk_split n (sp.toNat - 32 + 1) 1 30 $$ S1 with ⟨P1, S2⟩
  iunfold stk at P0 P1
  icases P0 with ⟨%c0', %hc0', P0⟩
  icases P1 with ⟨%c1', %hc1', P1⟩
  obtain ⟨x0, rfl⟩ := List.length_eq_one_iff.mp hc0'
  obtain ⟨x1, rfl⟩ := List.length_eq_one_iff.mp hc1'
  have s85 := SerdeIgnFrame.f85_empty (GF := GF) cfg lim (d + 1) types[14]! (by rfl) inst mi n hn Cg (sp - 32)
    (de + 12) x0 x1 (by omega) (by omega)
  rw [h32, hd12, show de.toNat + 12 + 8 = de.toNat + 20 by omega] at s85
  mstep; mstep
  mcall s85 using [D20 P0 P1]
  · iframe D20 P0 P1
  icases HQ with ⟨%hrs, D20, P0, P1⟩
  subst hrs
  mstep
  mstep [P0] with (rw [h32]; omega)
  simp only [SerdeKey.load8]
  mstep; mstep; mstep
  mstep_taken with decide
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep
  (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
  mstep; mstep; mstep; mstep [Hg]
  rw [show sp - 32 + 32 = sp by simp]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hg
  isplitr
  · ipureintro; simp [htype]
  isplitl [SB P0 P1 S2]
  · ihave P0 := stk_intro $$ P0
    ihave P1 := stk_intro $$ P1
    rw [show ([0] : List UInt8).length = 1 by rfl]
    ihave S1 := stk_join n (sp.toNat - 32 + 1) 1 30 $$ [P1 S2]
    · iframe P1 S2
    ihave S81 := stk_join n (sp.toNat - 32) 1 (1 + 30) $$ [P0 S1]
    · iframe P0 S1
    ihave S81 := stk_addr (show sp.toNat - 32 = sp.toNat - 96 + 64 by omega) $$ S81
    iapply stk_join n (sp.toNat - 96) 64 (1 + (1 + 30))
    iframe SB S81
  isplitl [Hrd]
  · rw [show bs.length - r.length = p + w + 1 by rw [hr]; simp; omega]; iexact Hrd
  iunfold scratchTables
  iframe He Hw D12 D16 Hid
  iexists 0
  iexact D20))

set_option hygiene false in
/-- The end of the container's block: the state after a break (`brkSt`) at `p'`, fuel `N'`. -/
local macro "n4close " p':term:max N':term:max f:term:max : tactic => `(tactic| (
  isplitr
  · ipureintro; trivial
  iunfold brkSt
  iexists $p'
  iexists _
  iexists _
  iexists _
  iexists _
  iexists _
  iexists $f
  iexists $N'
  isplitr
  · ipureintro
    exact ⟨rfl, hfb, by omega, hk5, hk7⟩
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; (try split) <;> (first | omega | (rename_i hh; exact absurd hh (by decide)))
  iframe Hrd
  iunfold P81
  iframe Hg S81 SB D20 He Hw D12 D16 Hid))

set_option hygiene false in
/-- 81 at a scalar from `p` (the reader there, the whitespace `w`, the byte `b`, the value's end `p1`):
339, the dispatch, the scalar's reader; `sd` finishes from the scalar's end. -/
local macro "vbody " sd:tactic : tactic => `(tactic| (
  have s339 := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (A 333)
    (hm.funcs 332 (by decide)) ha333 (by omega) Cg de ptr bs p (by omega) hlen hptr (by omega)
  rw [hw, Nat.add_mul, hWS] at s339
  mstep; mstep
  mcall s339 using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  rw [hb]
  mstep; mstep; mstep; mstep
  mstep_taken with exact SerdeIgnInt.ne0 (by simp only [SerdeRead.optByte_ok]; rfl)
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with exact some_ne b
  mstep; mstep; mstep; mstep; mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [ob16 b, band255 b]
  rcases SerdeIgnPure.vSkip_byte hws hv with ⟨rfl, s0, hsb⟩ | ⟨rfl, hix⟩ | ⟨hdg, hix⟩ | ⟨rfl, hlit⟩ |
      ⟨rfl, hlit⟩ | ⟨rfl, hlit⟩ | rfl | rfl
  · -- a string: 333, 650
    rw [hdr] at hr1s
    have hsb' : stringBody (bs.drop (p + w + 1)) [] = some (s0, r1) := hsb
    obtain ⟨hsplit, hplain⟩ := SerdeIgnPure.str_split hnb hsb'
    generalize hbody : SerdeKeyNoEsc.keyBody bs (p + w + 1) = body at hsplit hplain
    have hpos : p1 = p + w + 1 + body.length + 1 := by
      have := congrArg List.length hsplit; simp at this; omega
    have hS : 21 * body.length * cfg.regularOpCost + 940 * cfg.regularOpCost ≤
        470 * (p1 - (p + w)) * cfg.regularOpCost := by
      have e : 470 * (p1 - (p + w)) * cfg.regularOpCost = 470 * body.length * cfg.regularOpCost +
          940 * cfg.regularOpCost := by rw [show p1 - (p + w) = body.length + 2 by omega]; ring
      have := Nat.mul_le_mul_right cfg.regularOpCost (Nat.mul_le_mul_right body.length (show 21 ≤ 470 by omega))
      omega
    generalize hS' : 470 * (p1 - (p + w)) * cfg.regularOpCost = S at hS hS1
    generalize hM : 21 * body.length * cfg.regularOpCost = M at hS
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    have s650 := SerdeIgnStr.f650_noesc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi n g hn hg Cg gt (sp - 32)
      de ptr bs body r1 (p + w + 1) hlen hptr hsplit hplain
    rw [show SerdeIgnStr.cost650 body.length * cfg.regularOpCost = 56 * cfg.regularOpCost + M by
      unfold SerdeIgnStr.cost650; rw [← hM]; simp only [Nat.add_mul]] at s650
    mstep
    mcall s650 using [Hg Hrd He]
    · iframe Hg Hrd He
    icases HQ with ⟨%hrs, Hg, Hrd, He⟩
    subst hrs
    mstep; mstep
    mstep_taken with decide
    rw [show p + w + 1 + body.length + 1 = p1 by omega]
    ($sd:tactic)
  · -- `-`: 333, then 83
    have hlt1 : p + w + 1 < bs.length := by
      by_contra hc
      rw [List.drop_eq_nil_of_le (by omega)] at hix
      simp [SerdeNumModel.intR] at hix
    have hK := Nat.mul_le_mul_right cfg.regularOpCost (SerdeIgnInt.cost83_le hlt1 hix)
    rw [hP1, Nat.add_mul, Nat.add_mul] at hK
    have eS : 470 * (p1 - (p + w)) * cfg.regularOpCost =
        470 * cfg.regularOpCost + 470 * (p1 - (p + w + 1)) * cfg.regularOpCost := by
      rw [show p1 - (p + w) = (p1 - (p + w + 1)) + 1 by omega]; ring
    rw [eS]
    generalize hS' : 470 * (p1 - (p + w + 1)) * cfg.regularOpCost = S at hK
    generalize hK83 : SerdeIgnInt.cost83 bs (p + w + 1) r1 * cfg.regularOpCost = K83 at hK
    have s83 := SerdeIgnInt.f83_acc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm
      (by omega) Cg gt (sp - 32) de ptr bs r1 (p + w + 1) hlen hptr (by omega) hlt1 hix
    rw [hK83, hP1] at s83
    ihave #S83 := s83 $$ HN
    clear s83
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep
    mcall S83 using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mstep; mstep
    mstep_taken with decide
    ($sd:tactic)
  · -- a digit: 83
    have hix' : NearInterface.Json.isDigit b = true ∧ SerdeNumModel.intR (bs.drop (p + w)) = some r1 := by
      rw [hdr]; exact ⟨hdg, hix⟩
    have hK := Nat.mul_le_mul_right cfg.regularOpCost (SerdeIgnInt.cost83_le hlt hix'.2)
    rw [hP1, Nat.add_mul, Nat.add_mul] at hK
    generalize hS' : 470 * (p1 - (p + w)) * cfg.regularOpCost = S at hK hS1
    generalize hK83 : SerdeIgnInt.cost83 bs (p + w) r1 * cfg.regularOpCost = K83 at hK
    have s83 := SerdeIgnInt.f83_acc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi A n g ta hm
      (by omega) Cg gt (sp - 32) de ptr bs r1 (p + w) hlen hptr (by omega) hlt hix'.2
    rw [hK83, hP1] at s83
    ihave #S83 := s83 $$ HN
    clear s83
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep
    mstep_not_taken with exact eqb_zero (dig_ne hix'.1 (by decide))
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep_taken with exact dig_lt b hix'.1
    mstep
    mcall S83 using [Hg Hrd]
    · iframe Hg Hrd
    icases HQ with ⟨%hrs, Hg, Hrd⟩
    subst hrs
    mstep; mstep
    mstep_taken with decide
    ($sd:tactic)
  · -- `true`: 333, then 323 on `rue`
    have hpos : p1 = p + w + 4 := by
      have e1 := congrArg List.length hlit; have e2 := congrArg List.length hp1
      simp at e1 e2; omega
    have hlitk : ∀ k, k < 3 → bs[p + w + 1 + k]? = SerdeIdent.identBytes[4 + k]? := by
      intro k hk
      rw [← List.getElem?_drop, hlit]
      interval_cases k <;> rfl
    have s323 := SerdeIdent.f323_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n g hn hg
      (A 324) (A 673) (hm.funcs 324 (by decide)) (hm.funcs 673 (by decide)) (by omega) Cg gt (sp - 32) de ptr
      1048580 3 bs (p + w + 1) 4 3 (by rfl) (by rfl) (by decide) (by omega) hlitk hlen hptr (by omega) (by omega)
    simp only [SerdeIdent.cost323, Nat.reduceMul, Nat.reduceAdd] at s323
    rw [show 470 * (p1 - (p + w)) * cfg.regularOpCost = 1880 * cfg.regularOpCost by
      rw [show p1 - (p + w) = 4 by omega]]
    icases stk_split n (sp.toNat - 96) 32 32 $$ SB with ⟨SB1, SB2⟩
    ihave SB2 := stk_addr (show sp.toNat - 96 + 32 = (sp - 32).toNat - 32 by omega) $$ SB2
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep; mstep; mstep
    mcall s323 using [Hg SB2 Hrd Hid]
    · iframe Hg SB2 Hrd Hid
    icases HQ with ⟨%hrs, Hg, SB2, Hrd, Hid⟩
    subst hrs
    ihave SB2 := stk_addr (show (sp - 32).toNat - 32 = sp.toNat - 96 + 32 by omega) $$ SB2
    ihave SB := stk_join n (sp.toNat - 96) 32 32 $$ [SB1 SB2]
    · iframe SB1 SB2
    rw [show p + w + 1 + 3 = p1 by omega]
    mstep; mstep
    mstep_taken with decide
    ($sd:tactic)
  · -- `false`: 333, then 323 on `alse`
    have hpos : p1 = p + w + 5 := by
      have e1 := congrArg List.length hlit; have e2 := congrArg List.length hp1
      simp at e1 e2; omega
    have hlitk : ∀ k, k < 4 → bs[p + w + 1 + k]? = SerdeIdent.identBytes[0 + k]? := by
      intro k hk
      rw [← List.getElem?_drop, hlit]
      interval_cases k <;> rfl
    have s323 := SerdeIdent.f323_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n g hn hg
      (A 324) (A 673) (hm.funcs 324 (by decide)) (hm.funcs 673 (by decide)) (by omega) Cg gt (sp - 32) de ptr
      1048576 4 bs (p + w + 1) 0 4 (by rfl) (by rfl) (by decide) (by omega) hlitk hlen hptr (by omega) (by omega)
    simp only [SerdeIdent.cost323, Nat.reduceMul, Nat.reduceAdd] at s323
    rw [show 470 * (p1 - (p + w)) * cfg.regularOpCost = 2350 * cfg.regularOpCost by
      rw [show p1 - (p + w) = 5 by omega]]
    icases stk_split n (sp.toNat - 96) 32 32 $$ SB with ⟨SB1, SB2⟩
    ihave SB2 := stk_addr (show sp.toNat - 96 + 32 = (sp - 32).toNat - 32 by omega) $$ SB2
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep; mstep; mstep
    mcall s323 using [Hg SB2 Hrd Hid]
    · iframe Hg SB2 Hrd Hid
    icases HQ with ⟨%hrs, Hg, SB2, Hrd, Hid⟩
    subst hrs
    ihave SB2 := stk_addr (show (sp - 32).toNat - 32 = sp.toNat - 96 + 32 by omega) $$ SB2
    ihave SB := stk_join n (sp.toNat - 96) 32 32 $$ [SB1 SB2]
    · iframe SB1 SB2
    rw [show p + w + 1 + 4 = p1 by omega]
    mstep; mstep
    mstep_taken with decide
    ($sd:tactic)
  · -- `null`: 333, then 323 on `ull`
    have hpos : p1 = p + w + 4 := by
      have e1 := congrArg List.length hlit; have e2 := congrArg List.length hp1
      simp at e1 e2; omega
    have hlitk : ∀ k, k < 3 → bs[p + w + 1 + k]? = SerdeIdent.identBytes[7 + k]? := by
      intro k hk
      rw [← List.getElem?_drop, hlit]
      interval_cases k <;> rfl
    have s323 := SerdeIdent.f323_spec (GF := GF) cfg lim (d + 1) types[15]! (by rfl) inst mi n g hn hg
      (A 324) (A 673) (hm.funcs 324 (by decide)) (hm.funcs 673 (by decide)) (by omega) Cg gt (sp - 32) de ptr
      1048583 3 bs (p + w + 1) 7 3 (by rfl) (by rfl) (by decide) (by omega) hlitk hlen hptr (by omega) (by omega)
    simp only [SerdeIdent.cost323, Nat.reduceMul, Nat.reduceAdd] at s323
    rw [show 470 * (p1 - (p + w)) * cfg.regularOpCost = 1880 * cfg.regularOpCost by
      rw [show p1 - (p + w) = 4 by omega]]
    icases stk_split n (sp.toNat - 96) 32 32 $$ SB with ⟨SB1, SB2⟩
    ihave SB2 := stk_addr (show sp.toNat - 96 + 32 = (sp - 32).toNat - 32 by omega) $$ SB2
    mstep_not_taken with decide
    mstep; mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep
    mstep; mstep; mstep
    mstep_not_taken with decide
    mstep; mstep; mstep
    mstep_taken with decide
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
      (by omega)) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mstep; mstep; mstep
    mcall s323 using [Hg SB2 Hrd Hid]
    · iframe Hg SB2 Hrd Hid
    icases HQ with ⟨%hrs, Hg, SB2, Hrd, Hid⟩
    subst hrs
    ihave SB2 := stk_addr (show (sp - 32).toNat - 32 = sp.toNat - 96 + 32 by omega) $$ SB2
    ihave SB := stk_join n (sp.toNat - 96) 32 32 $$ [SB1 SB2]
    · iframe SB1 SB2
    rw [show p + w + 1 + 3 = p1 by omega]
    mstep
    mstep_not_taken with decide
    ($sd:tactic)
  · exact absurd rfl hb5B
  · exact absurd rfl hb7B
))

section L81

variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 64000000 in
/-- **`ignore_value(de)`** (81) on a shallow value: where `ign1` skips from `j` to `r`, `0`, the reader at
`|bs| - |r|`. -/
theorem f81_shallow_reuse (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr ptrS capS : UInt32) (bs : List UInt8) (j : Nat) (r : List UInt8)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hsp : 96 ≤ sp.toNat) (hj : j ≤ bs.length) (hnb : (0x5C : UInt8) ∉ bs) (hx : ign1 (bs.drop j) = some r) :
    code81 inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f81 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          rd n de ptr bs j ∗ scratchTables n de ptrS capS))
        (fun _ => (166 + 470 * (bs.length - r.length - j)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          rd n de ptr bs (bs.length - r.length) ∗ scratchTables n de ptrS capS)) := by
  iintro #Hk
  ihave #Hk' := Hk
  iunfold code81 at Hk'
  icases Hk' with ⟨#HN, #F339, #F82, #F674, #F85, #F84, #HA, #F650, #F323, #F673, #F83⟩
  ihave #HN' := HN
  iunfold numCode at HN'
  icases HN' with ⟨#F324, #F332, #F333, #F329, #F88, #F87, #F86, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha333 := hm.funcs 333 (by decide)
  have ha339 := hm.funcs 339 (by decide)
  have ha82 := hm.funcs 82 (by decide)
  have ha83 := hm.funcs 83 (by decide)
  have ha84 := hm.funcs 84 (by decide)
  have ha85 := hm.funcs 85 (by decide)
  have ha650 := hm.funcs 650 (by decide)
  have ha323 := hm.funcs 323 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  have t14 : types[14]!.params.length = 2 := by rfl
  have t31 : types[31]!.params.length = 3 := by rfl
  have t32 : types[32]!.params.length = 1 := by rfl
  have t15 : types[15]!.params.length = 3 := by rfl
  have hlt := sp.toNat_lt
  have h32 : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  have hd12 : (de + 12).toNat = de.toNat + 12 := by simp [UInt32.toNat_add]; omega
  have hq : bs.length - r.length ≤ bs.length := by omega
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hrd, Ht⟩
  subst hargs
  iunfold scratchTables at Ht
  icases Ht with ⟨⟨%sl, D20⟩, He, Hw, D12, D16, Hid⟩
  icases stk_split n (sp.toNat - 96) 64 32 $$ Hs with ⟨SB, S81⟩
  rw [show sp.toNat - 96 + 64 = sp.toNat - 32 by omega]
  simp only [f81]
  generalize hW : 470 * (bs.length - r.length - j) * cfg.regularOpCost = W
  rw [Nat.add_mul, hW]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep; mstep; mstep; mstep
  rw [show de.toNat + 20 = (de + 12).toNat + 8 by omega]
  mcall (SerdeDeStr.f343_s cfg lim (d + 1) types[0]! (by rfl) inst mi A n g ta hm (by omega) Cg (de + 12) sl
    (by omega)) using [D20]
  · iframe D20
  icases HQ with ⟨%hrs, D20⟩
  subst hrs
  rw [show (de + 12).toNat + 8 = de.toNat + 20 by omega]
  rw [show 166 * cfg.regularOpCost + W + R - 49 * cfg.regularOpCost = 117 * cfg.regularOpCost + (W + R) by omega]
  mstep; mstep; mstep; mstep
  mstep; mstep; mstep
  mcredits (cfg.regularOpCost + (109 * cfg.regularOpCost + W + R))
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 109 * cfg.regularOpCost + W + R)
    (I := inv4 n g inst mi Cg cfg.regularOpCost gt sp de ptr ptrS capS bs j r 109 60 R) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv4 at HI
    icases HI with ⟨%hX, HI⟩
    subst hX
    iapply mwpi_split3 (N := fun vs fr => iprop(⌜vs = []⌝ ∗
      contSt n g inst mi Cg cfg.regularOpCost gt sp de ptr ptrS capS bs r 250 0 R fr))
    isplitl [HI]
    · icases HI with (⟨%l5, %l6, %l7, %l8, %hfr, Hc, Hrd, HP⟩ | ⟨%p, %l5, %l6, %l7, %fb, %N, %⟨hfr, hfb, hp, hmod⟩, Hc, Hrd, HP⟩)
      · rw [hfr]; simp only [fr81]
        iunfold P81 at HP
        icases HP with ⟨Hg, S81, SB, D20, He, Hw, D12, D16, Hid⟩
        have hsk : skipWhitespace (bs.drop j) = bs.drop (j + wsLen (bs.drop j)) := by
          rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
        have hwle := SerdeRead.wsLen_le (bs.drop j)
        generalize hw : wsLen (bs.drop j) = w at hsk hwle
        simp only [List.length_drop] at hwle
        obtain ⟨b, hb⟩ : ∃ b, bs[j + w]? = some b := by
          cases hb : bs[j + w]? with
          | some b => exact ⟨b, rfl⟩
          | none =>
            exfalso
            have hnil : bs.drop (j + w) = [] := List.drop_eq_nil_of_le (by have := List.getElem?_eq_none_iff.mp hb; omega)
            rw [hnil] at hsk
            unfold ign1 at hx
            rw [hsk] at hx
            simp [SerdeIgnPure.vSkip_nil] at hx
        have hlt : j + w < bs.length := by
          by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; simp at hb
        have hdr := SerdeIgnInt.drop_cons hlt hb
        have hws : isWhitespace b = false :=
          SerdeRead.wsLen_stop (bs.drop j) b (by rw [hw, List.getElem?_drop]; exact hb)
        rcases SerdeIgnPure.ign1_cons hx (hsk.trans hdr) with ⟨rfl, hop⟩ | ⟨rfl, hop⟩ | ⟨hb5B, hb7B, hv⟩
        · -- `[`
          brPre
          mstep_not_taken with decide
          mstep; mstep
          mstep; mstep; mstep
          mstep_not_taken with decide
          mstep; mstep; mstep
          mstep_taken with decide
          brTail
        · -- `{`
          brPre
          mstep_not_taken with decide
          mstep; mstep
          mstep; mstep; mstep
          mstep_not_taken with decide
          mstep; mstep; mstep
          mstep_not_taken with decide
          mstep
          mstep; mstep; mstep
          mstep_not_taken with decide
          mstep; mstep; mstep
          mstep_not_taken with decide
          mstep
          mstep; mstep; mstep
          mstep_not_taken with decide
          mstep; mstep; mstep
          mstep_taken with decide
          brTail
        · -- a scalar: the value is all of it
          generalize hp : j = p at hv hw hb hlt hdr hws hsk hwle hj
          obtain ⟨r1, hr1⟩ : ∃ r1, r1 = r := ⟨r, rfl⟩
          rw [← hr1] at hv
          have hr1s : r1 <:+ bs.drop (p + w) := by rw [hdr]; exact IgnoreShallow.vSkip_suf hv
          have hr1l : r1.length < bs.length - (p + w) := by
            have := IgnoreShallow.vSkip_strict hv; rw [← hdr] at this; simp at this; omega
          have hp1 : bs.drop (bs.length - r1.length) = r1 := JsonSuffix.drop_suf' hr1s
          generalize hP1 : bs.length - r1.length = p1 at hp1
          have hp1l : p + w < p1 := by omega
          have hp1q : p1 = bs.length - r.length := by rw [← hr1]; omega
          rw [show 470 * (bs.length - r.length - p) * cfg.regularOpCost =
            96 * w * cfg.regularOpCost + (374 * w * cfg.regularOpCost + (470 * (p1 - (p + w)) * cfg.regularOpCost +
              470 * (bs.length - r.length - p1) * cfg.regularOpCost)) by
            rw [show bs.length - r.length - p = w + (p1 - (p + w)) + (bs.length - r.length - p1) by omega]; ring]
          have hS1 : 470 * cfg.regularOpCost ≤ 470 * (p1 - (p + w)) * cfg.regularOpCost :=
            Nat.mul_le_mul_right cfg.regularOpCost (show 470 ≤ 470 * (p1 - (p + w)) by omega)
          generalize hWS : 96 * w * cfg.regularOpCost = WS
          generalize hX1 : 374 * w * cfg.regularOpCost = X1
          generalize hWq : 470 * (bs.length - r.length - p1) * cfg.regularOpCost = Wq
          vbody sdTop
      · rw [hfr]; simp only [fr81]
        iunfold P81 at HP
        icases HP with ⟨Hg, S81, SB, D20, He, Hw, D12, D16, Hid⟩
        obtain ⟨r1, hs1, hc1⟩ : ∃ r1, scal (bs.drop p) = some r1 ∧ cont1 fb N r1 = some r := by
          simp only [Option.bind_eq_some_iff] at hmod; exact hmod
        have hsk : skipWhitespace (bs.drop p) = bs.drop (p + wsLen (bs.drop p)) := by
          rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
        have hwle := SerdeRead.wsLen_le (bs.drop p)
        generalize hw : wsLen (bs.drop p) = w at hsk hwle
        simp only [List.length_drop] at hwle
        obtain ⟨b, hb⟩ : ∃ b, bs[p + w]? = some b := by
          cases hb : bs[p + w]? with
          | some b => exact ⟨b, rfl⟩
          | none =>
            exfalso
            have hnil : bs.drop (p + w) = [] := List.drop_eq_nil_of_le (by have := List.getElem?_eq_none_iff.mp hb; omega)
            rw [hnil] at hsk
            unfold scal at hs1
            rw [hsk] at hs1
            simp [SerdeIgnPure.vSkip_nil] at hs1
        have hlt : p + w < bs.length := by
          by_contra hc; rw [List.getElem?_eq_none (by omega)] at hb; simp at hb
        have hdr := SerdeIgnInt.drop_cons hlt hb
        have hws : isWhitespace b = false :=
          SerdeRead.wsLen_stop (bs.drop p) b (by rw [hw, List.getElem?_drop]; exact hb)
        obtain ⟨hb5B, hb7B, hv⟩ := SerdeIgnPure.scal_cons hs1 (hsk.trans hdr)
        have hr1s : r1 <:+ bs.drop (p + w) := by rw [hdr]; exact IgnoreShallow.vSkip_suf hv
        have hr1l : r1.length < bs.length - (p + w) := by
          have := IgnoreShallow.vSkip_strict hv; rw [← hdr] at this; simp at this; omega
        have hrr1 : r.length ≤ r1.length := (SerdeIgnPure.cont1_suf fb N r1 r hc1).length_le
        have hp1 : bs.drop (bs.length - r1.length) = r1 := JsonSuffix.drop_suf' hr1s
        generalize hP1 : bs.length - r1.length = p1 at hp1
        have hp1l : p + w < p1 := by omega
        have hp1q : p1 ≤ bs.length - r.length := by omega
        rw [show 470 * (bs.length - r.length - p) * cfg.regularOpCost =
          96 * w * cfg.regularOpCost + (374 * w * cfg.regularOpCost + (470 * (p1 - (p + w)) * cfg.regularOpCost +
            470 * (bs.length - r.length - p1) * cfg.regularOpCost)) by
          rw [show bs.length - r.length - p = w + (p1 - (p + w)) + (bs.length - r.length - p1) by omega]; ring]
        have hS1 : 470 * cfg.regularOpCost ≤ 470 * (p1 - (p + w)) * cfg.regularOpCost :=
          Nat.mul_le_mul_right cfg.regularOpCost (show 470 ≤ 470 * (p1 - (p + w)) by omega)
        generalize hWS : 96 * w * cfg.regularOpCost = WS
        generalize hX1 : 374 * w * cfg.regularOpCost = X1
        generalize hWq : 470 * (bs.length - r.length - p1) * cfg.regularOpCost = Wq
        vbody sdIn
    · iintro %vs %fr ⟨%hvs, HS⟩
      subst hvs
      iunfold contSt at HS
      icases HS with ⟨%p, %l3, %l4, %l5, %l6, %l7, %fb, %N, %op, %⟨hfr, hfb, hp, hst⟩, Hc, Hrd, HP⟩
      subst hfr
      have hsk : skipWhitespace (bs.drop p) = bs.drop (p + wsLen (bs.drop p)) := by
        rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
      have hwle := SerdeRead.wsLen_le (bs.drop p)
      generalize hw : wsLen (bs.drop p) = w at hsk hwle
      simp only [List.length_drop] at hwle
      have hrl : r.length < bs.length - (p + w) := by
        have := (show r.length < (skipWhitespace (bs.drop p)).length by
          cases op
          · rw [if_neg (by decide)] at hst; exact SerdeIgnPure.cont1_lt hfb hst.2.2
          · rw [if_pos rfl] at hst; exact SerdeIgnPure.open1_lt hfb hst.2.2)
        rw [hsk] at this; simpa using this
      obtain ⟨c0, hc0⟩ : ∃ c0, bs[p + w]? = some c0 := ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hlt : p + w < bs.length := by omega
      have hdr := SerdeIgnInt.drop_cons hlt hc0
      have hws : isWhitespace c0 = false :=
        SerdeRead.wsLen_stop (bs.drop p) c0 (by rw [hw, List.getElem?_drop]; exact hc0)
      rw [show 470 * (bs.length - r.length - p) * cfg.regularOpCost =
        96 * w * cfg.regularOpCost + (374 * w * cfg.regularOpCost + (470 * cfg.regularOpCost +
          470 * (bs.length - r.length - (p + w + 1)) * cfg.regularOpCost)) by
        rw [show bs.length - r.length - p = w + 1 + (bs.length - r.length - (p + w + 1)) by omega]; ring]
      generalize hWS : 96 * w * cfg.regularOpCost = WS
      generalize hX1 : 374 * w * cfg.regularOpCost = X1
      generalize hWq : 470 * (bs.length - r.length - (p + w + 1)) * cfg.regularOpCost = Wq
      generalize hEC : (if op = true then (if fb = 0x5B then 250 else 200) else 0) * cfg.regularOpCost = EC
      iapply mwpi_split1 (N := fun vs fr => iprop(⌜vs = []⌝ ∗
        brkSt n g inst mi Cg cfg.regularOpCost gt sp de ptr ptrS capS bs r 75 R fr))
      isplitl [Hc Hrd HP]
      · simp only [fr81]
        mstep
        mcredits (cfg.regularOpCost + (EC + 468 * cfg.regularOpCost + WS + X1 + Wq + R))
        iapply mwpi_cons
        iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := EC + 468 * cfg.regularOpCost + WS + X1 + Wq + R)
          (I := fun X fr' => iprop(⌜X = [] ∧ fr' = fr81 inst mi de (sp - 32) l3 l4 l5 l6 l7 fb.toUInt32⌝ ∗
            credits Cg (EC + 468 * cfg.regularOpCost + WS + X1 + Wq + R) ∗ rd n de ptr bs p ∗ P81 n g gt sp de ptrS capS))
          _ _ rfl
        isplitr
        · imodintro
          iintro %X %lc HI
          icases HI with ⟨%⟨hX, hfr'⟩, Hc, Hrd, HP⟩
          subst hX
          rw [hfr']; simp only [fr81]
          iunfold P81 at HP
          icases HP with ⟨Hg, S81, SB, D20, He, Hw, D12, D16, Hid⟩
          have s339 := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn
            (A 332) (A 333) (hm.funcs 332 (by decide)) ha333 (by omega) Cg de ptr bs p (by omega) hlen hptr (by omega)
          rw [hw, Nat.add_mul, hWS] at s339
          mstep; mstep
          mcall s339 using [Hrd]
          · iframe Hrd
          icases HQ with ⟨%hrs, Hrd⟩
          subst hrs
          rw [hc0]
          mstep; mstep; mstep; mstep
          mstep_taken with exact SerdeIgnInt.ne0 (by simp only [SerdeRead.optByte_ok]; rfl)
          mstep; mstep; mstep; mstep; mstep; mstep; mstep
          mstep; mstep; mstep; mstep; mstep
          mstep_taken with exact some_ne _
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          rw [ob16, band255]
          cases op with
          | true =>
            rw [if_pos rfl] at hst
            obtain ⟨rfl, rfl, hst⟩ := hst
            rcases SerdeIgnPure.open1_cons hfb hst (hsk.trans hdr) with ⟨rfl, rfl, hr⟩ | ⟨rfl, rfl, hr⟩ |
                ⟨h5D, h7D, h2C, hm5, hm7⟩
            · -- `[` then `]`
              mstep_taken with decide
              mstep; mstep; mstep; mstep; mstep
              mstep_not_taken with decide
              closeTail
            · -- `{` then `}`
              mstep_not_taken with decide
              mstep
              mstep; mstep; mstep
              mstep_taken with decide
              mstep; mstep; mstep; mstep; mstep
              mstep_taken with decide
              closeTail
            · -- the first element or member: break
              have hk5 : fb = 0x5B → (scal (bs.drop (p + w))).bind (cont1 fb N) = some r := by rw [hdr]; exact hm5
              have hk7 : fb = 0x7B → keyThen sk (bs.drop (p + w)) (fun r3 => (scal r3).bind (cont1 fb N)) = some r := by
                rw [hdr]; exact hm7
              have f93 := t93 c0
              rw [if_neg h5D] at f93
              have f125 := t125 c0
              rw [if_neg h7D] at f125
              have f44 := t44 c0
              rw [if_neg h2C] at f44
              mstep_not_taken with exact f93
              mstep
              mstep; mstep; mstep
              mstep_not_taken with exact f125
              mstep; mstep; mstep
              mstep_taken with exact SerdeIgnInt.ne0 f44
              (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
              mstep; mstep; mstep; mstep
              mstep_taken with decide
              (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
              have hq2 : 470 * (bs.length - r.length - (p + w)) * cfg.regularOpCost = 470 * cfg.regularOpCost + Wq := by
                rw [← hWq, show bs.length - r.length - (p + w) = 1 + (bs.length - r.length - (p + w + 1)) by omega]; ring
              rcases hfb with rfl | rfl
              · have hfb : Br (0x5B : UInt8) := Or.inl rfl
                have hE : EC = 250 * cfg.regularOpCost := by rw [← hEC]; rfl
                n4close (p + w) N 0x5B
              · have hfb : Br (0x7B : UInt8) := Or.inr rfl
                have hE : EC = 200 * cfg.regularOpCost := by rw [← hEC]; rfl
                n4close (p + w) N 0x7B
          | false =>
            rw [if_neg (by decide)] at hst
            obtain ⟨rfl, rfl, hst⟩ := hst
            obtain ⟨N', rfl, hcc⟩ := SerdeIgnPure.cont1_cons hfb hst (hsk.trans hdr)
            rcases hcc with ⟨rfl, rfl, hr⟩ | ⟨rfl, rfl, hr⟩ | ⟨rfl, hm5, hm7⟩
            · -- `]`
              mstep_taken with decide
              mstep; mstep; mstep; mstep; mstep
              mstep_not_taken with decide
              closeTail
            · -- `}`
              mstep_not_taken with decide
              mstep
              mstep; mstep; mstep
              mstep_taken with decide
              mstep; mstep; mstep; mstep; mstep
              mstep_taken with decide
              closeTail
            · -- `,`: eat, break
              have hk5 : fb = 0x5B → (scal (bs.drop (p + w + 1))).bind (cont1 fb N') = some r := hm5
              have hk7 : fb = 0x7B → keyThen sk (bs.drop (p + w + 1)) (fun r3 => (scal r3).bind (cont1 fb N')) = some r :=
                hm7
              have hEC' : EC = 0 := by rw [← hEC, if_neg (by decide)]; simp
              mstep_not_taken with decide
              mstep
              mstep; mstep; mstep
              mstep_not_taken with decide
              mstep; mstep; mstep
              mstep_not_taken with decide
              mstep; mstep; mstep; mstep
              mstep_not_taken with decide
              mstep
              mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w) hlt hlen
                (by omega)) using [Hrd]
              · iframe Hrd
              icases HQ with ⟨%hrs, Hrd⟩
              subst hrs
              mstep
              (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
              n4close (p + w + 1) N' fb
        · iframe Hc
          inext
          iintro Hc
          iframe Hc Hrd HP
          ipureintro; exact ⟨rfl, rfl⟩
      · iintro %vs %fr ⟨%hvs, HB⟩
        subst hvs
        iunfold brkSt at HB
        icases HB with ⟨%p, %l3, %l4, %l5, %l6, %l7, %fb, %N, %⟨hfr, hfb, hp, hk5, hk7⟩, Hc, Hrd, HP⟩
        subst hfr
        simp only [fr81]
        rcases hfb with rfl | rfl
        · -- `[`: the next element
          rw [show (if (0x5B : UInt8) = 0x5B then 75 else 0) = 75 from rfl]
          generalize hWp : 470 * (bs.length - r.length - p) * cfg.regularOpCost = Wp
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          mstep_taken with decide
          simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iunfold inv4
          isplitr
          · ipureintro; rfl
          iright
          iexists p
          iexists l5
          iexists l6
          iexists l7
          iexists 0x5B
          iexists N
          isplitr
          · ipureintro; exact ⟨rfl, Or.inl rfl, hp, hk5 rfl⟩
          rw [hWp]
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          iframe Hrd HP
        · -- `{`: the next member's key, `:`, then the value
          rw [show (if (0x7B : UInt8) = 0x5B then 75 else 0) = 0 from rfl]
          iunfold P81 at HP
          icases HP with ⟨Hg, S81, SB, D20, He, Hw, D12, D16, Hid⟩
          obtain ⟨r1, s1, r2, r3, hk1, hk2, hk3, hk4⟩ := SerdeIgnPure.keyThen_some (hk7 rfl)
          have hsk : skipWhitespace (bs.drop p) = bs.drop (p + wsLen (bs.drop p)) := by
            rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
          generalize hw3 : wsLen (bs.drop p) = w3 at hsk
          rw [hsk] at hk1
          have hlt3 : p + w3 < bs.length := by
            by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hk1; simp at hk1
          have hb3 : bs[p + w3]? = some 0x22 := by
            rw [List.drop_eq_getElem_cons hlt3] at hk1
            simp only [List.cons.injEq] at hk1
            rw [List.getElem?_eq_getElem hlt3, hk1.1]
          have hr1 : r1 = bs.drop (p + w3 + 1) := by
            rw [SerdeIgnInt.drop_cons hlt3 hb3] at hk1; simp only [List.cons.injEq] at hk1; exact hk1.2.symm
          rw [hr1] at hk2
          obtain ⟨hsplit, hplain⟩ := SerdeIgnPure.str_split hnb hk2
          generalize hbody : SerdeKeyNoEsc.keyBody bs (p + w3 + 1) = body at hsplit hplain
          have hl2 : bs.length - (p + w3 + 1) = body.length + 1 + r2.length := by
            have := congrArg List.length hsplit; simp at this; omega
          have hr2 : r2 = bs.drop (p + w3 + 1 + body.length + 1) := by
            have hs2 : r2 <:+ bs.drop (p + w3 + 1) := by
              rw [hsplit]; exact (List.suffix_cons _ _).trans (List.suffix_append _ _)
            rw [← JsonSuffix.drop_suf' hs2]; congr 1; omega
          generalize hp2 : p + w3 + 1 + body.length + 1 = p2 at hr2
          have hsk2 : skipWhitespace (bs.drop p2) = bs.drop (p2 + wsLen (bs.drop p2)) := by
            rw [SerdeRead.skipWhitespace_eq, List.drop_drop]
          generalize hw4 : wsLen (bs.drop p2) = w4 at hsk2
          rw [hr2, hsk2] at hk3
          have hlt4 : p2 + w4 < bs.length := by
            by_contra hc; rw [List.drop_eq_nil_of_le (by omega)] at hk3; simp at hk3
          have hb4 : bs[p2 + w4]? = some 0x3A := by
            rw [List.drop_eq_getElem_cons hlt4] at hk3
            simp only [List.cons.injEq] at hk3
            rw [List.getElem?_eq_getElem hlt4, hk3.1]
          have hr3 : r3 = bs.drop (p2 + w4 + 1) := by
            rw [SerdeIgnInt.drop_cons hlt4 hb4] at hk3; simp only [List.cons.injEq] at hk3; exact hk3.2.symm
          rw [hr3] at hk4
          have hq3 : p2 + w4 + 1 ≤ bs.length - r.length := by
            have := (SerdeIgnPure.kont_suf _ N _ _ hk4).length_le; simp at this; omega
          rw [show 470 * (bs.length - r.length - p) * cfg.regularOpCost =
            96 * w3 * cfg.regularOpCost + (374 * w3 * cfg.regularOpCost + (21 * body.length * cfg.regularOpCost +
              (449 * body.length * cfg.regularOpCost + (96 * w4 * cfg.regularOpCost +
                (374 * w4 * cfg.regularOpCost + (1410 * cfg.regularOpCost +
                  470 * (bs.length - r.length - (p2 + w4 + 1)) * cfg.regularOpCost)))))) by
            rw [show bs.length - r.length - p = w3 + body.length + w4 + 3 + (bs.length - r.length - (p2 + w4 + 1)) by
              omega]; ring]
          generalize hWS3 : 96 * w3 * cfg.regularOpCost = WS3
          generalize hX3 : 374 * w3 * cfg.regularOpCost = X3
          generalize hM : 21 * body.length * cfg.regularOpCost = M
          generalize hXM : 449 * body.length * cfg.regularOpCost = XM
          generalize hWS4 : 96 * w4 * cfg.regularOpCost = WS4
          generalize hX4 : 374 * w4 * cfg.regularOpCost = X4
          generalize hWq3 : 470 * (bs.length - r.length - (p2 + w4 + 1)) * cfg.regularOpCost = Wq3
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          mstep_not_taken with decide
          have s339 := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn
            (A 332) (A 333) (hm.funcs 332 (by decide)) ha333 (by omega) Cg de ptr bs p (by omega) hlen hptr (by omega)
          rw [hw3, Nat.add_mul, hWS3] at s339
          mstep; mstep
          mcall s339 using [Hrd]
          · iframe Hrd
          icases HQ with ⟨%hrs, Hrd⟩
          subst hrs
          rw [hb3]
          mstep; mstep; mstep; mstep
          mstep_taken with exact SerdeIgnInt.ne0 (by simp only [SerdeRead.optByte_ok]; rfl)
          mstep; mstep; mstep; mstep; mstep; mstep
          mstep_taken with exact some_ne _
          mstep; mstep; mstep; mstep; mstep
          mstep_not_taken with decide
          mstep
          mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p + w3) hlt3 hlen
            (by omega)) using [Hrd]
          · iframe Hrd
          icases HQ with ⟨%hrs, Hrd⟩
          subst hrs
          have s650 := SerdeIgnStr.f650_noesc (GF := GF) cfg lim (d + 1) types[32]! (by rfl) inst mi n g hn hg Cg gt
            (sp - 32) de ptr bs body r2 (p + w3 + 1) hlen hptr hsplit hplain
          rw [show SerdeIgnStr.cost650 body.length * cfg.regularOpCost = 56 * cfg.regularOpCost + M by
            unfold SerdeIgnStr.cost650; rw [← hM]; simp only [Nat.add_mul], hp2] at s650
          mstep
          mcall s650 using [Hg Hrd He]
          · iframe Hg Hrd He
          icases HQ with ⟨%hrs, Hg, Hrd, He⟩
          subst hrs
          mstep
          mstep_not_taken with decide
          have s339' := SerdeRead.f339_spec (GF := GF) cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn
            (A 332) (A 333) (hm.funcs 332 (by decide)) ha333 (by omega) Cg de ptr bs p2 (by omega) hlen hptr (by omega)
          rw [hw4, Nat.add_mul, hWS4] at s339'
          mstep; mstep
          mcall s339' using [Hrd]
          · iframe Hrd
          icases HQ with ⟨%hrs, Hrd⟩
          subst hrs
          rw [hb4]
          mstep; mstep; mstep; mstep
          mstep_taken with exact SerdeIgnInt.ne0 (by simp only [SerdeRead.optByte_ok]; rfl)
          mstep; mstep; mstep; mstep; mstep; mstep
          mstep_taken with exact some_ne _
          mstep; mstep; mstep; mstep; mstep; mstep
          mstep_not_taken with decide
          mstep
          mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (p2 + w4) hlt4 hlen
            (by omega)) using [Hrd]
          · iframe Hrd
          icases HQ with ⟨%hrs, Hrd⟩
          subst hrs
          mstep
          simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iunfold inv4
          isplitr
          · ipureintro; rfl
          iright
          iexists p2 + w4 + 1
          iexists _
          iexists _
          iexists _
          iexists 0x7B
          iexists N
          isplitr
          · ipureintro; exact ⟨rfl, Or.inr rfl, by omega, hk4⟩
          rw [hWq3]
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          iframe Hrd
          iunfold P81
          iframe Hg S81 SB D20 He Hw D12 D16 Hid
  · iframe Hc
    inext
    iintro Hc
    iunfold inv4
    isplitr
    · ipureintro; rfl
    ileft
    iexists 0
    iexists 0
    iexists 0
    iexists 0
    isplitr
    · ipureintro; rfl
    rw [← hW]
    iframe Hc Hrd
    iunfold P81
    iframe Hg S81 SB D20 He Hw D12 D16 Hid

theorem f81_shallow (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 8 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs : List UInt8) (j : Nat) (r : List UInt8)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 24 ≤ 2 ^ 32)
    (hsp : 96 ≤ sp.toNat) (hj : j ≤ bs.length) (hnb : (0x5C : UInt8) ∉ bs) (hx : ign1 (bs.drop j) = some r) :
    code81 inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f81 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          rd n de ptr bs j ∗ tbl n de))
        (fun _ => (166 + 470 * (bs.length - r.length - j)) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 96) 96 ∗
          rd n de ptr bs (bs.length - r.length) ∗ tbl n de)) := by
  exact f81_shallow_reuse cfg lim d type htype inst mi A n g ta hm hd Cg gt sp de ptr 1 0 bs j r
    hlen hptr hde hsp hj hnb hx

end L81

end WNear.Binary.SerdeIgnValue
