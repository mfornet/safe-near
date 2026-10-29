import Bridge.Functions.SerdeNumModel
import Bridge.Functions.SerdeErrBox

/-!
# Numbers in ignored values (M6): 88, 87, 86, 83 on accepted numbers

`ignore_value` (81) skips a number with `ignore_integer` (83) after eating its `-`; 83 calls
`ignore_decimal` (86) at a `.` and `ignore_exponent` (87) at an `e` or `E`. Their accepting runs,
against `SerdeNumModel`'s `intR`, `fracR`, `expR`:

* `f88_spec`: `next_char_or_null`, the byte at the index (or 0) at bits 8..15, the index past it.
* `f87_acc`: at `e`/`E`, an exponent `expR` reads: 0, the reader at its end.
* `f86_acc`: at `.`, a fraction `fracR` reads: 0, the reader at its end.
* `f83_acc`: at a digit, a number `intR` reads: 0, the reader at its end.

The digit loops cost `D` per digit; the byte tests are `decide`d over the 256 bytes.
-/

namespace WNear.Binary.SerdeIgnNum

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd optByte byteOrNull)
open NearInterface.Json (isDigit)
open WNear.SerdeNumModel

set_option hygiene false in
/-- A `br_if` taken (the condition `h`), out of the enclosing blocks. -/
local macro "brt " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr; ipureintro; exact ⟨rfl, $h⟩
  mctrl_norm; repeat mpay))

set_option hygiene false in
/-- A `br_if` not taken (the condition `h`). -/
local macro "brn " h:term : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, $h⟩; inext; iintro Hc; mctrl_norm))

theorem bon88 (o : Option UInt8) :
    (optByte o >>> ((8 : UInt64) % 64) &&& Numeric.intToUInt64 ((optByte o <<< ((55 : UInt64) % 64)).toIntS >>> ((63 : UInt64) % 64).toNat) &&& 65280 |||
      optByte o &&& 18446744069414584320 ||| 0) = byteOrNull o := by
  cases o with
  | none => decide +kernel
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

section L88

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`next_char_or_null`** (88): the byte at the index (or 0), the index past it. -/
theorem f88_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a324 : Nat) (ha324 : mi.funcAddrs[324]? = some a324)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (de ptr : UInt32) (bs : List UInt8) (i : Nat)
    (hi : i ≤ bs.length) (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hde : de.toNat + 12 ≤ 2 ^ 32) :
    a324 ↪[wf] FuncInst.wasm types[11]! inst f324 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f88 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ rd n de ptr bs i))
        (fun _ => 74 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (byteOrNull bs[i]?)]⌝ ∗ rd n de ptr bs (min (i + 1) bs.length))) := by
  iintro ⟨#F324, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hrd⟩
  subst hargs
  have t11 : types[11]!.params.length = 1 := by rfl
  simp only [f88]
  mstep; mstep; mstep
  mstep; mstep
  mcall (SerdeRead.f324_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn Cg de ptr bs i hi hlen hptr hde)
    using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  have hok1 : Numeric.bool (optByte bs[i]? &&& 1 == 0) = 1 := by simp only [SerdeRead.optByte_ok]; rfl
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok1
  repeat mstep
  rw [bon88]
  mcredits R
  iframe Hc Hrd
  ipureintro; simp [htype]

end L88

theorem bon_ok (o : Option UInt8) : Numeric.bool (byteOrNull o &&& 1 == 0) = 1 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- The digit test `(b - 48) & 255 ≤ 9` of a peeked byte (0 at the end). -/
theorem bon_le9 (o : Option UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.le_u (((byteOrNull o).toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) =
      if isDigit (o.getD 0) then 1 else 0 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- The digit test `(b - 48) & 255 > 9` of a peeked byte (0 at the end). -/
theorem bon_gt9 (o : Option UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.gt_u (((byteOrNull o).toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) =
      if isDigit (o.getD 0) then 0 else 1 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- 87's sign test: `br_table` on `b - 43`, to label 0 for `+` and `-`. -/
theorem bon_sign (o : Option UInt8) :
    ([0, 1, 0] : List Nat)[(((byteOrNull o).toUInt32 >>> (8 % 32) &&& 255) + 4294967253).toNat]?.getD 1 =
      if o = some 0x2B ∨ o = some 0x2D then 0 else 1 := by
  cases o with
  | none => decide
  | some b => revert b; exact SerdeRead.uint8_forall (by decide +kernel)

theorem tw_mem {l : List UInt8} {x : UInt8} (h : x ∈ l.takeWhile isDigit) : isDigit x = true := by
  induction l with
  | nil => simp at h
  | cons y l ih =>
    simp only [List.takeWhile_cons] at h
    split at h
    · rename_i hy
      rcases List.mem_cons.mp h with rfl | h
      · exact hy
      · exact ih h
    · simp at h

theorem dw_head {l : List UInt8} : ∀ x r, l.dropWhile isDigit = x :: r → isDigit x = false := by
  induction l with
  | nil => intro x r h; simp at h
  | cons y l ih =>
    intro x r h
    simp only [List.dropWhile_cons] at h
    split at h
    · exact ih x r h
    · rename_i hy
      simp only [List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      simpa using hy

/-- The digits at `j` (`nd` of them) and the byte after them. -/
theorem digits_at (bs : List UInt8) (j : Nat) (hj : j ≤ bs.length) :
    let nd := ((bs.drop j).takeWhile isDigit).length
    j + nd ≤ bs.length ∧ (∀ k, j ≤ k → k < j + nd → ∃ x, bs[k]? = some x ∧ isDigit x = true) ∧
      isDigit ((bs[j + nd]?).getD 0) = false ∧ bs.drop (j + nd) = (bs.drop j).dropWhile isDigit := by
  intro nd
  have hs := (List.takeWhile_append_dropWhile (p := isDigit) (l := bs.drop j)).symm
  have hl := congrArg List.length hs
  simp only [List.length_drop, List.length_append] at hl
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro k h1 h2
    have hk : bs[k]? = ((bs.drop j).takeWhile isDigit ++ (bs.drop j).dropWhile isDigit)[k - j]? := by
      rw [← hs, List.getElem?_drop]; congr 1; omega
    rw [List.getElem?_append_left (by omega)] at hk
    refine ⟨((bs.drop j).takeWhile isDigit)[k - j]'(by omega), ?_, tw_mem (List.getElem_mem _)⟩
    rw [hk, List.getElem?_eq_getElem]
  · have hk : bs[j + nd]? = ((bs.drop j).takeWhile isDigit ++ (bs.drop j).dropWhile isDigit)[nd]? := by
      rw [← hs, List.getElem?_drop]
    rw [List.getElem?_append_right (by omega), Nat.sub_self] at hk
    rw [hk]
    cases hd : (bs.drop j).dropWhile isDigit with
    | nil => rfl
    | cons x r => exact dw_head x r hd
  · rw [← List.drop_drop]
    conv_lhs => rw [hs]
    rw [List.drop_left' rfl]

section L87

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The code of the number skippers' callees (persistent). -/
def numCode (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : IProp GF :=
  iprop(A 324 ↪[wf] FuncInst.wasm types[11]! inst f324 ∗ A 332 ↪[wf] FuncInst.wasm types[11]! inst f332 ∗
    A 333 ↪[wf] FuncInst.wasm types[0]! inst f333 ∗ A 329 ↪[wf] FuncInst.wasm types[11]! inst f329 ∗
    A 88 ↪[wf] FuncInst.wasm types[11]! inst f88 ∗ A 87 ↪[wf] FuncInst.wasm types[32]! inst f87 ∗
    A 86 ↪[wf] FuncInst.wasm types[32]! inst f86 ∗ inst ↪[inst] mi)

instance (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) : Persistent (numCode (GF := GF) inst mi A) := by
  unfold numCode; infer_instance

/-- 87's frame. -/
def fr87 (inst : Nat) (mi : ModuleInst) (de l1 : UInt32) (l2 : UInt64) : Frame :=
  ⟨#[.i32 de, .i32 l1, .i64 l2], inst, mi⟩

/-- 87's digit loop: the reader at `k ≤ e`, `D` per digit left. -/
def inv87 (n inst : Nat) (mi : ModuleInst) (Cg c₀ D E R : Nat) (de l1 ptr : UInt32) (bs : List UInt8) (s e : Nat)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (l2 : UInt64), ⌜X = [] ∧ g = fr87 inst mi de l1 l2 ∧ s ≤ k ∧ k ≤ e⌝ ∗
    credits Cg (D * (e - k) * c₀ + E * c₀ + R) ∗ rd n de ptr bs k ∗ P)

theorem inv87_intro (n inst : Nat) (mi : ModuleInst) (Cg c₀ D E R : Nat) (de l1 ptr : UInt32) (bs : List UInt8)
    (s e : Nat) (P : IProp GF) (k : Nat) (l2 : UInt64) (h1 : s ≤ k) (h2 : k ≤ e) :
    credits Cg (D * (e - k) * c₀ + E * c₀ + R) ∗ rd n de ptr bs k ∗ P ⊢
      inv87 n inst mi Cg c₀ D E R de l1 ptr bs s e P [] ⟨#[.i32 de, .i32 l1, .i64 l2], inst, mi⟩ := by
  iintro ⟨Hc, Hrd, HP⟩
  iunfold inv87
  iexists k
  iexists l2
  iframe Hc Hrd HP
  ipureintro; exact ⟨rfl, rfl, h1, h2⟩

/-- 87's cost: `150` and `127` per byte read (the `e`, the sign, the digits). -/
def cost87 (m : Nat) : Nat := 300 + 127 * m

set_option hygiene false in
/-- 87 from the 88 at `j` (the first digit): the digit loop, then 0. -/
local macro "tail87" : tactic => `(tactic| (
  obtain ⟨hjn, hdig, hstop, hdrop⟩ := digits_at bs j (by omega)
  generalize hnd : ((bs.drop j).takeWhile isDigit).length = nd at hjn hdig hstop hdrop
  have hnd1 : 1 ≤ nd := by
    rw [← hnd]; cases hh : (bs.drop j).takeWhile isDigit with
    | nil => rw [hu, hh] at hne; simp at hne
    | cons _ _ => simp
  obtain ⟨x0, hx0, hdx0⟩ := hdig j (Nat.le_refl _) (by omega)
  mstep; mstep
  mcall (f88_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 324) (hm.funcs 324 (by decide))
    (by omega) Cg de ptr bs j (by omega) hlen hptr hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (40 * cfg.regularOpCost + (127 * L * cfg.regularOpCost + R))
  rw [hx0, show min (j + 1) bs.length = j + 1 by omega]
  generalize hob0 : byteOrNull (some x0) = ob0
  have hok0 : Numeric.bool (ob0 &&& 1 == 0) = 1 := by rw [← hob0]; exact bon_ok _
  have hg0 : Numeric.bool (Numeric.irelop32 IRelOp.gt_u ((ob0.toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) = 0 := by
    rw [← hob0, bon_gt9]; simp [hdx0]
  clear hob0
  mstep; mstep; mstep; mstep
  mstep_taken with exact hok0
  mstep
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with exact hg0
  have hLnd : L = (j + nd - (j + 1)) + (j - i + 1) := by
    rw [← hL, ← hx, hu, ← hdrop]; simp; omega
  rw [hLnd, Nat.mul_add, Nat.add_mul, hji]
  mcredits (cfg.regularOpCost + (127 * (j + nd - (j + 1)) * cfg.regularOpCost + 112 * cfg.regularOpCost + R))
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 127 * (j + nd - (j + 1)) * cfg.regularOpCost + 112 * cfg.regularOpCost + R)
    (I := inv87 n inst mi Cg cfg.regularOpCost 127 112 R de (sp - 16) ptr bs (j + 1) (j + nd)
      iprop(g ↦[wg] ⟨gt, .i32 (sp - 16)⟩)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv87 at HI
    icases HI with ⟨%k, %l2, %⟨hX, hfr, hk1, hk2⟩, Hc, Hrd, Hg⟩
    subst hX
    rw [hfr]
    simp only [fr87]
    clear hfr
    generalize hZ0 : 127 * (j + nd - k) * cfg.regularOpCost = Z0
    mstep; mstep
    mcall (SerdeRead.f329_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (hm.funcs 332 (by decide))
      (by omega) Cg de ptr bs k (by omega) hlen hptr hde) using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    mcredits (27 * cfg.regularOpCost + (Z0 + R))
    rw [← hZ0]
    generalize hobk : byteOrNull bs[k]? = obk
    have hokk : Numeric.bool (obk &&& 1 == 0) = 1 := by rw [← hobk]; exact bon_ok _
    mstep; mstep; mstep; mstep
    mstep_taken with exact hokk
    by_cases hke : k < j + nd
    · obtain ⟨xk, hxk, hdk⟩ := hdig k (by omega) hke
      rw [hxk] at hobk
      have hlk : Numeric.bool (Numeric.irelop32 IRelOp.le_u ((obk.toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) = 1 := by
        rw [← hobk, bon_le9]; simp [hdk]
      rw [show 127 * (j + nd - k) * cfg.regularOpCost =
        127 * cfg.regularOpCost + 127 * (j + nd - (k + 1)) * cfg.regularOpCost by
          rw [show j + nd - k = (j + nd - (k + 1)) + 1 by omega]; simp only [Nat.mul_add, Nat.add_mul]; omega]
      generalize hZ : 127 * (j + nd - (k + 1)) * cfg.regularOpCost = Z
      clear hobk
      mstep
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_taken with exact hlk
      mstep
      mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs k (by omega) hlen hde)
        using [Hrd]
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
      iapply inv87_intro n inst mi Cg cfg.regularOpCost 127 112 R de (sp - 16) ptr bs (j + 1) (j + nd) _ (k + 1) _
        (by omega) (by omega)
      iframe Hrd Hg
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    · have hk : k = j + nd := by omega
      subst hk
      have hlk : Numeric.bool (Numeric.irelop32 IRelOp.le_u ((obk.toUInt32 >>> (8 % 32) + 4294967248) &&& 255) 9) = 0 := by
        rw [← hobk, bon_le9]; simp [hstop]
      rw [show 127 * (j + nd - (j + nd)) * cfg.regularOpCost = 0 by simp, Nat.zero_add]
      clear hobk
      mstep
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      mstep_not_taken with exact hlk
      mstep; mstep; mstep
      (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
      mstep; mstep; mstep; mstep [Hg]
      rw [show sp - 16 + 16 = sp by simp]
      repeat mstep
      isplitl [Hc]
      · iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      iframe Hg
      isplitr
      · ipureintro; simp [htype]
      rw [show bs.length - rest.length = j + nd by
        rw [← hx, hu, ← hdrop]; simp; omega]
      iexact Hrd
  · iframe Hc
    inext
    iintro Hc
    iapply inv87_intro n inst mi Cg cfg.regularOpCost 127 112 R de (sp - 16) ptr bs (j + 1) (j + nd) _ (j + 1) _
      (by omega) (by omega)
    iframe Hrd Hg
    iexact Hc))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 16000000 in
/-- **`ignore_exponent(rd)`** (87) at `e`/`E`: an exponent `expR` reads after it, `0`, the reader at its
end. -/
theorem f87_acc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : Interface.IfaceMod mi A n g ta) (hd : d + 3 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs rest : List UInt8) (i : Nat)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32) (hde : de.toNat + 12 ≤ 2 ^ 32)
    (hi : i < bs.length) (hx : expR (bs.drop (i + 1)) = some rest) :
    numCode inst mi A ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f87 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs i))
        (fun _ => cost87 (bs.length - rest.length - i) * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs (bs.length - rest.length))) := by
  iintro #Hk
  iunfold numCode at Hk
  icases Hk with ⟨#F324, #F332, #F333, #F329, #F88, -, -, #Hi⟩
  have hn := hm.mem
  have hg := hm.glob
  have ha333 := hm.funcs 333 (by decide)
  have ha329 := hm.funcs 329 (by decide)
  have ha88 := hm.funcs 88 (by decide)
  have t11 : types[11]!.params.length = 1 := by rfl
  have t0 : types[0]!.params.length = 1 := by rfl
  unfold expR at hx
  obtain ⟨sg, u, hsp⟩ : ∃ sg u, signPart (bs.drop (i + 1)) = (sg, u) := ⟨_, _, rfl⟩
  rw [hsp] at hx
  simp only at hx
  by_cases hne : (u.takeWhile isDigit).isEmpty = true
  · simp [hne] at hx
  simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hx
  have hlt : i + 1 < bs.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hsp
    simp only [signPart, Prod.mk.injEq] at hsp
    rw [← hsp.2] at hne; simp at hne
  obtain ⟨b1, hb1⟩ : ∃ b1, bs[i + 1]? = some b1 := ⟨_, List.getElem?_eq_getElem hlt⟩
  have hd1 : bs.drop (i + 1) = b1 :: bs.drop (i + 2) := by
    rw [List.drop_eq_getElem_cons hlt]
    rw [List.getElem?_eq_getElem hlt] at hb1
    rw [Option.some.inj hb1]
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hrd⟩
  subst hargs
  simp only [f87, cost87]
  generalize hL : bs.length - rest.length - i = L
  rw [show (300 + 127 * L) * cfg.regularOpCost + R = 300 * cfg.regularOpCost + (127 * L * cfg.regularOpCost + R) by
    simp only [Nat.add_mul]; omega]
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs i hi hlen hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (270 * cfg.regularOpCost + (127 * L * cfg.regularOpCost + R))
  mstep; mstep; mstep
  mcall (SerdeRead.f329_spec cfg (lim := lim) (d + 1) types[11]! (by rfl) inst mi n hn (A 332) (hm.funcs 332 (by decide))
    (by omega) Cg de ptr bs (i + 1) (by omega) hlen hptr hde) using [Hrd]
  · iframe Hrd
  icases HQ with ⟨%hrs, Hrd⟩
  subst hrs
  mcredits (190 * cfg.regularOpCost + (127 * L * cfg.regularOpCost + R))
  rw [hb1]
  generalize hob : byteOrNull (some b1) = ob
  mstep; mstep; mstep; mstep
  have hok : Numeric.bool (ob &&& 1 == 0) = 1 := by rw [← hob]; exact bon_ok _
  mstep_taken with exact hok
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  by_cases hs : b1 = 0x2B ∨ b1 = 0x2D
  · -- a sign: eaten, the digits from `i + 2`
    have hsg : some b1 = some 0x2B ∨ some b1 = some 0x2D := by rcases hs with rfl | rfl <;> simp
    have hk := bon_sign (some b1)
    rw [if_pos hsg, hob] at hk
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have hu : u = bs.drop (i + 2) := by
      rw [hd1] at hsp
      rcases hs with rfl | rfl <;> (simp only [signPart, Prod.mk.injEq] at hsp; exact hsp.2.symm)
    mstep
    mcall (SerdeRead.f333_spec cfg lim (d + 1) types[0]! (by rfl) inst mi n hn Cg de ptr bs (i + 1) hlt hlen hde)
      using [Hrd]
    · iframe Hrd
    icases HQ with ⟨%hrs, Hrd⟩
    subst hrs
    generalize hj : i + 1 + 1 = j at hu ⊢
    have hjl : j ≤ bs.length := by omega
    have hji : j - i + 1 = 3 := by omega
    mcredits (130 * cfg.regularOpCost + (127 * L * cfg.regularOpCost + R))
    tail87
  · have hsg : ¬ (some b1 = some 0x2B ∨ some b1 = some 0x2D) := by simpa using hs
    have hk := bon_sign (some b1)
    rw [if_neg hsg, hob] at hk
    iapply FromUtf8Gen.mwpi_br_table_k hk
    isplitr
    · ipureintro; rfl
    clear hk
    mctrl_norm; repeat mpay
    have hu : u = bs.drop (i + 1) := by
      rw [hd1] at hsp
      unfold signPart at hsp
      split at hsp
      · rename_i x heq; simp only [List.cons.injEq] at heq; exact absurd (Or.inl heq.1) hs
      · rename_i x heq; simp only [List.cons.injEq] at heq; exact absurd (Or.inr heq.1) hs
      · simp only [Prod.mk.injEq] at hsp; rw [← hsp.2, hd1]
    generalize hj : i + 1 = j at hu ⊢
    have hjl : j ≤ bs.length := by omega
    have hji : j - i + 1 = 2 := by omega
    mcredits (130 * cfg.regularOpCost + (127 * L * cfg.regularOpCost + R))
    tail87

end L87

end WNear.Binary.SerdeIgnNum
