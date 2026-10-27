import Binary.Code.Part10
import NearLogic.Tactic.Control

/-!
# wee_alloc's leaf helpers, in the metered logic

The small functions wee_alloc 0.4.5 (`LargeAllocPolicy` only, no size
classes) calls on its paths, each an `MFunSpec` on the path that does not
panic (their panics are `core::panicking::panic` (853) on an arithmetic
overflow, which `HeapInv` rules out; see `AllocInv.lean`).
Costs exclude the activation (paid by the caller), in `regular_op_cost`s:

| fn  | Rust                                        | result               | cost |
|-----|---------------------------------------------|----------------------|------|
| 578 | `LargeAllocPolicy::min_cell_size`           | 16                   | 1    |
| 579 | `…::should_merge_adjacent_free_cells`       | 1                    | 1    |
| 576 | `CellHeader::size`                          | `(w &&& !3) - c - 8` | 15   |
| 574 | the `x - 8` overflow assertion              | `()` if `8 ≤ x`      | 7    |
| 572 | `Words → Bytes`                             | `w <<< 2`, `w < 2^30` | 9   |
| 573 | `Pages → Bytes`                             | `p <<< 16`, `p < 2^16` | 9  |
| 568 | `round_up_to`, `(a + b - 1) / b`            | `a + b < 2^32`, `b ≠ 0` | 18 |
| 570 | `Bytes → Words` (568 by 4)                  | `(a + 3) / 4`         | 31 (with 568) |
| 569 | `Bytes → Pages` (568 by 65536)              | `(a + 65535) / 65536` | 31 (with 568) |
-/

namespace WNear.Binary.AllocLeaves

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-- A branch condition on `u32` arithmetic: by `toNat`, then `omega`. -/
macro "ucond" : tactic =>
  `(tactic| (simp only [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt,
      UInt32.le_iff_toNat_le, UInt32.toNat_add, UInt32.toNat_sub, gt_iff_lt, ge_iff_le,
      decide_eq_true_eq, beq_iff_eq, bne_iff_ne, ne_eq, ite_eq_right_iff, ite_eq_left_iff,
      UInt32.toNat_ofNat, UInt32.reduceToNat] at *; muint_bounds; first | omega | (simp_all; omega) | simp_all))

theorem sub8_toNat (x c : UInt32) (h : c.toNat + 8 ≤ x.toNat) :
    (x - c + 4294967288).toNat = x.toNat - c.toNat - 8 := by
  have := x.toNat_lt; have := c.toNat_lt
  simp only [UInt32.toNat_add, UInt32.toNat_sub]; simp; omega

theorem and_mask_eq (w m : UInt32) (k : Nat) (hm : m.toNat = 2 ^ k - 1) (h : w.toNat < 2 ^ k) :
    (w &&& m) = w := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_and, hm, Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt h]

set_option maxRecDepth 20000

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `LargeAllocPolicy::min_cell_size` (578): 16, whatever the arguments. -/
theorem f578_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (a b : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f578 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 b]⌝))
        (fun _ => 1 * cfg.regularOpCost) (fun _ rs => iprop(⌜rs = [.i32 16]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f578]
  mstep
  rw [htype]
  iframe Hc
  ipureintro; rfl

/-- `CellHeader::size` (576). -/
theorem f576_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (c w : UInt32)
    (hc : c.toNat + 4 ≤ 2 ^ 32)
    (hw : c.toNat + 8 ≤ (w &&& 4294967292).toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f576 Cg
        (fun args => iprop(⌜args = [.i32 c]⌝ ∗ n ↦[wms][ c.toNat ] bytes32 w))
        (fun _ => 15 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 ((w &&& 4294967292) - c + 4294967288)]⌝ ∗
          n ↦[wms][ c.toNat ] bytes32 w)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, Hw⟩ Hc
  subst hargs

  simp only [f576]
  mstep; mstep; mstep [Hw]; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep
  mstep_not_taken with ucond
  mstep; mstep
  rw [htype]
  iframe Hc Hw
  ipureintro; rfl

/-- `LargeAllocPolicy::should_merge_adjacent_free_cells` (579): `true`. -/
theorem f579_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (a : UInt32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f579 Cg
        (fun args => iprop(⌜args = [.i32 a]⌝))
        (fun _ => 1 * cfg.regularOpCost) (fun _ rs => iprop(⌜rs = [.i32 1]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f579]
  mstep
  rw [htype]
  iframe Hc
  ipureintro; rfl

/-- The `x - 8` assertion (574): returns when `8 ≤ x`. -/
theorem f574_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (x : UInt32)
    (hx : 8 ≤ x.toNat) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f574 Cg
        (fun args => iprop(⌜args = [.i32 x]⌝))
        (fun _ => 7 * cfg.regularOpCost) (fun _ rs => iprop(⌜rs = []⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f574]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with ucond
  mstep
  iframe Hc

/-- `Words → Bytes` (572): `w * 4` when it does not overflow. -/
theorem f572_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (w : UInt32)
    (hw : w.toNat < 2 ^ 30) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f572 Cg
        (fun args => iprop(⌜args = [.i32 w]⌝))
        (fun _ => 9 * cfg.regularOpCost) (fun _ rs => iprop(⌜rs = [.i32 (w <<< 2)]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f572]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with (simp [and_mask_eq w 1073741823 30 (by decide) hw, Numeric.bool, Numeric.irelop32])
  mstep; mstep; mstep
  rw [htype]
  iframe Hc
  ipureintro; rfl

/-- `Pages → Bytes` (573): `p * 65536` when it does not overflow. -/
theorem f573_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (p : UInt32)
    (hp : p.toNat < 2 ^ 16) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f573 Cg
        (fun args => iprop(⌜args = [.i32 p]⌝))
        (fun _ => 9 * cfg.regularOpCost) (fun _ rs => iprop(⌜rs = [.i32 (p <<< 16)]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f573]
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_taken with (simp [and_mask_eq p 65535 16 (by decide) hp, Numeric.bool, Numeric.irelop32])
  mstep; mstep; mstep
  rw [htype]
  iframe Hc
  ipureintro; rfl

/-- `round_up_to` (568): `(a + b - 1) / b`, when `a + b` neither overflows nor
is zero, and `b ≠ 0`. -/
theorem f568_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (Cg : Nat) (a b : UInt32)
    (hab : a.toNat + b.toNat < 2 ^ 32) (h1 : 1 ≤ a.toNat + b.toNat) (hb : b ≠ 0) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f568 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 b]⌝))
        (fun _ => 18 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 ((a + b + 4294967295) / b)]⌝)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f568]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with ucond
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep_not_taken with (simp only [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_add, gt_iff_lt, decide_eq_true_eq, ite_eq_right_iff, UInt32.toNat_ofNat, UInt32.reduceToNat]; omega)
  mstep; mstep
  mstep with (simp only [Numeric.ibinop32, beq_iff_eq, hb, if_false]; rfl)
  mstep
  rw [htype]
  iframe Hc
  ipureintro; rfl


/-- `Bytes → Words` rounding up (570): `round_up_to(a, 4)`, through 568. -/
theorem f570_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (a568 : Nat)
    (ha : mi.funcAddrs[568]? = some a568) (ty568 : FuncType) (hty1 : ty568.params.length = 2)
    (hty2 : ty568.results.length = 1) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (a : UInt32)
    (ha4 : a.toNat + 4 < 2 ^ 32) :
    a568 ↪[wf] FuncInst.wasm ty568 inst f568 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f570 Cg
        (fun args => iprop(⌜args = [.i32 a]⌝))
        (fun _ => 31 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 ((a + 4 + 4294967295) / 4)]⌝)) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f570]
  mstep; mstep
  mcall (f568_spec cfg lim (d + 1) ty568 hty2 inst mi Cg a 4 (by simp; omega) (by simp)
      (by decide)) with (simp [activationGas, entryLocals, f568, ValType.default]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  rw [htype]
  mpay
  iframe Hc

/-- `Bytes → Pages` rounding up (569): `round_up_to(a, 65536)`, through 568. -/
theorem f569_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (a568 : Nat)
    (ha : mi.funcAddrs[568]? = some a568) (ty568 : FuncType) (hty1 : ty568.params.length = 2)
    (hty2 : ty568.results.length = 1) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (a : UInt32)
    (ha4 : a.toNat + 65536 < 2 ^ 32) :
    a568 ↪[wf] FuncInst.wasm ty568 inst f568 ∗ inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f569 Cg
        (fun args => iprop(⌜args = [.i32 a]⌝))
        (fun _ => 31 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 ((a + 65536 + 4294967295) / 65536)]⌝)) := by
  iintro ⟨#Hf, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R %hargs Hc
  subst hargs
  simp only [f569]
  mstep; mstep
  mcall (f568_spec cfg lim (d + 1) ty568 hty2 inst mi Cg a 65536 (by simp; omega) (by simp)
      (by decide)) with (simp [activationGas, entryLocals, f568, ValType.default]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  rw [htype]
  mpay
  iframe Hc
end Spec

end WNear.Binary.AllocLeaves
