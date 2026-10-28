import Bridge.Functions.MemCpy

/-!
# `memset` (function 952), in the metered logic

`memset(dst, c, len) -> dst`, compiler_builtins' forward byte loop:

```wat
block
  local.get 2  i32.eqz  br_if 0
  local.get 0  local.set 3
  loop
    local.get 3  local.get 1  i32.store8
    local.get 3  i32.const 1  i32.add  local.set 3
    local.get 2  i32.const -1  i32.add  local.tee 2  br_if 0
  end
end
local.get 0
```

`f952_spec` is its `MFunSpec` for any length: `cost len` `regular_op_cost`s,
4 for `len = 0` and `13 len + 6` otherwise; the `len` bytes at `dst` become
`replicate len (byteOf c)` (`byteOf c` the low byte of `c`). The loop is
proved with `mwpi_loop` (`MemCpy.mwpi_loop0`) from the invariant `inv` (the
`k`-th iteration: the first `k` bytes set, credits for the `len - k`
iterations left), as `MemCpy.f951_spec`.
-/

namespace WNear.Binary.MemSet

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.MemCpy (memBytes_pick memBytes_unpick mwpi_loop0)

/-- The byte `i32.store8` writes of `c`. -/
def byteOf (c : UInt32) : UInt8 := UInt8.ofNat c.toNat

theorem storeBytes_i32_1 (c : UInt32) : storeBytes (.i32 c) 1 = [byteOf c] := by
  simp [storeBytes, storeRaw, byteOf, List.range, List.range.loop]

theorem set_step (ob : List UInt8) (b : UInt8) (k : Nat) (_h1 : k < ob.length) :
    List.take k (List.replicate k b ++ List.drop k ob) ++
        b :: List.drop (k + 1) (List.replicate k b ++ List.drop k ob)
      = List.replicate (k + 1) b ++ ob.drop (k + 1) := by
  rw [List.take_left' (by simp), List.drop_append,
    List.drop_eq_nil_of_le (by simp)]
  simp [List.drop_drop, List.replicate_succ', List.append_assoc]

/-- The loop invariant at iteration `k < N`: the locals `(dst, c, N - k, dst + k)`,
the first `k` bytes set, the credits of the iterations left. -/
def inv {GF : BundledGFunctors} [WasmGS NearState GF] (n inst : Nat) (mi : ModuleInst)
    (Cg R c₀ : Nat) (dst c : UInt32) (N : Nat) (ob : List UInt8) :
    List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (r e : UInt32), ⌜X = [] ∧ g = ⟨#[.i32 dst, .i32 c, .i32 r, .i32 e], inst, mi⟩ ∧
      k < N ∧ e.toNat = dst.toNat + k ∧ r.toNat = N - k⌝ ∗
    credits Cg (13 * (N - k) * c₀ + R) ∗
    n ↦[wms][ dst.toNat ] (List.replicate k (byteOf c) ++ ob.drop k))

/-- The cost of `memset` of `N` bytes, activation excluded, in `regular_op_cost`s. -/
def cost (N : Nat) : Nat := if N = 0 then 4 else 13 * N + 6

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre (n : Nat) (dst c len : UInt32) (ob : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dst, .i32 c, .i32 len]⌝ ∗ n ↦[wms][ dst.toNat ] ob)

def post (n : Nat) (dst c len : UInt32) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 dst]⌝ ∗ n ↦[wms][ dst.toNat ] List.replicate len.toNat (byteOf c))

/-- `memset` (function 952 of `contract.wasm`) of `len` bytes at `dst` to the
low byte of `c`. -/
theorem f952_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (dst c len : UInt32) (ob : List UInt8)
    (hob : ob.length = len.toNat) (hdst : dst.toNat + len.toNat ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f952 Cg (pre n dst c len ob)
        (fun _ => cost len.toNat * cfg.regularOpCost) (post n dst c len) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hd⟩
  subst hargs
  simp only [f952]
  by_cases h0 : len.toNat = 0
  · have hl : len = 0 := by
      apply UInt32.toNat_inj.mp; simpa using h0
    subst hl
    simp only [cost, h0, ite_true]
    mstep; mstep; mstep; mstep; mstep
    have e1 : ob = [] := List.eq_nil_of_length_eq_zero (by simpa using hob)
    subst e1
    rw [htype]
    iframe Hc
    iunfold post
    simp only [UInt32.toNat_zero, List.replicate_zero]
    iframe Hd
    ipureintro; rfl
  · have hN : 0 < len.toNat := Nat.pos_of_ne_zero h0
    have hl : len ≠ 0 := fun e => h0 (by simp [e])
    simp only [cost, h0, ite_false]
    rw [show (13 * len.toNat + 6) * cfg.regularOpCost + R =
      6 * cfg.regularOpCost + (13 * len.toNat * cfg.regularOpCost + R) by rw [Nat.add_mul]; omega]
    mstep; mstep; mstep; mstep; mstep; mstep
    iapply mwpi_loop0 (Cg := Cg) (R := 13 * len.toNat * cfg.regularOpCost + R)
      (I := inv n inst mi Cg R cfg.regularOpCost dst c len.toNat ob) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold inv at HI
      icases HI with ⟨%k, %r, %e, %⟨hX, hg, hk, he, hr⟩, Hc, Hd⟩
      subst hX
      rw [hg]
      have hkN : k < ob.length := by omega
      ihave Hd := memBytes_pick n dst.toNat k (List.replicate k (byteOf c) ++ ob.drop k)
        (by simp; omega) $$ Hd
      icases Hd with ⟨Hd1, Hdk, Hd2⟩
      rw [show 13 * (len.toNat - k) * cfg.regularOpCost + R =
        11 * cfg.regularOpCost + ((13 * (len.toNat - k) - 11) * cfg.regularOpCost + R) by
          rw [Nat.sub_mul]
          have : 11 * cfg.regularOpCost ≤ 13 * (len.toNat - k) * cfg.regularOpCost :=
            Nat.mul_le_mul_right _ (by omega)
          omega]
      mstep; mstep; mstep [Hdk]
      rw [storeBytes_i32_1]
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      ihave Hd := memBytes_unpick n dst.toNat k
        (List.take k (List.replicate k (byteOf c) ++ List.drop k ob)) (byteOf c)
        (List.drop (k + 1) (List.replicate k (byteOf c) ++ List.drop k ob)) (by simp) $$ [Hd1 Hdk Hd2]
      · iframe Hd1 Hdk Hd2
      rw [set_step ob (byteOf c) k hkN]
      have hc1 : (r + 4294967295).toNat = len.toNat - k - 1 := by
        rw [UInt32.toNat_add]; simp; omega
      by_cases hk1 : k + 1 < len.toNat
      · have hne : r + 4294967295 ≠ 0 := by
          intro h; rw [h] at hc1; simp at hc1; omega
        rw [show (13 * (len.toNat - k) - 11) * cfg.regularOpCost + R =
          2 * cfg.regularOpCost + (13 * (len.toNat - (k + 1)) * cfg.regularOpCost + R) by
            rw [show 13 * (len.toNat - k) - 11 = 2 + 13 * (len.toNat - (k + 1)) by omega, Nat.add_mul]
            omega]
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, hne⟩
        simp only [Post.mloop, List.reverse_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        rw [Nat.add_sub_cancel_left]
        iunfold inv
        iexists k + 1
        iexists r + 4294967295
        iexists e + 1
        iframe Hc Hd
        ipureintro
        refine ⟨by simp, rfl, hk1, ?_, by omega⟩
        rw [UInt32.toNat_add]; simp; omega
      · have heq : r + 4294967295 = 0 := UInt32.toNat_inj.mp (by simp; omega)
        rw [show (13 * (len.toNat - k) - 11) * cfg.regularOpCost + R =
          2 * cfg.regularOpCost + R by
            rw [show 13 * (len.toNat - k) - 11 = 2 by omega]]
        iapply mwpi_br_if_not'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨rfl, by omega, heq⟩
        inext
        iintro Hc
        rw [heq]
        simp only [Post.mloop, List.reverse_nil, List.append_nil]
        rw [show 2 * cfg.regularOpCost + R - cfg.regularOpCost = cfg.regularOpCost + R by omega]
        clear hg hc1 heq
        mpay
        mpay
        mstep
        have ed : List.replicate (k + 1) (byteOf c) ++ List.drop (k + 1) ob =
            List.replicate len.toNat (byteOf c) := by
          rw [List.drop_eq_nil_of_le (by omega), List.append_nil, show k + 1 = len.toNat by omega]
        rw [htype, ed]
        iframe Hc
        iunfold post
        iframe Hd
        ipureintro; rfl
    isplitl [Hc]
    · iexact Hc
    inext
    iintro Hc
    iunfold inv
    iexists 0
    iexists len
    iexists dst
    simp only [Nat.sub_zero, List.replicate_zero, List.drop_zero, List.nil_append]
    iframe Hc Hd
    ipureintro
    simp [hN]

end Spec

end WNear.Binary.MemSet
