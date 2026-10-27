import Binary.Code.Part20
import NearLogic.Tactic.Control

/-!
# `memcpy` (function 951), in the metered logic

`memcpy(dst, src, len) -> dst`, compiler_builtins' forward byte loop:

```wat
block
  local.get 2  i32.eqz  br_if 0
  local.get 0  local.set 3
  loop
    local.get 3  local.get 1  i32.load8_u  i32.store8
    local.get 1  i32.const 1  i32.add  local.set 1
    local.get 3  i32.const 1  i32.add  local.set 3
    local.get 2  i32.const -1  i32.add  local.tee 2  br_if 0
  end
end
local.get 0
```

`f951_spec` is its `MFunSpec` for any length, on separately owned (hence,
when `len > 0`, disjoint) ranges: `cost len` `regular_op_cost`s, 4 for
`len = 0` and `18 len + 6` otherwise (with the activation 10, paid by the
caller, the harness's `14` and `16 + 18 len`, `memcpy`). The loop is proved
once with `mwpi_loop` from the invariant `inv` (the `k`-th iteration: the
first `k` bytes copied, credits for the `len - k` iterations left).
-/

namespace WNear.Binary.MemCpy

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

section Bytes

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem memBytes_cons (n a : Nat) (b : UInt8) (l : List UInt8) :
    memBytes (H := NearState) (GF := GF) n a (b :: l) ⊣⊢ n ↦[wms][ a ] [b] ∗ n ↦[wms][ a + 1 ] l :=
  memBytes_append (GF := GF) n a [b] l

/-- The `k`-th byte of a range, apart. -/
theorem memBytes_pick (n a k : Nat) (l : List UInt8) (h : k < l.length) :
    memBytes (H := NearState) (GF := GF) n a l ⊢
      n ↦[wms][ a ] (l.take k) ∗ n ↦[wms][ a + k ] [l[k]] ∗ n ↦[wms][ a + k + 1 ] (l.drop (k + 1)) := by
  have e := (memBytes_append (GF := GF) (H := NearState) n a (l.take k) (l.drop k)).1
  rw [List.take_append_drop, List.length_take, show min k l.length = k by omega,
    List.drop_eq_getElem_cons h] at e
  iintro H
  ihave H := e $$ H
  icases H with ⟨H1, H2⟩
  ihave H2 := (memBytes_cons n (a + k) l[k] (l.drop (k + 1))).1 $$ H2
  iframe H1 H2

/-- The bytes `xs`, `b`, `ys` in a row. -/
theorem memBytes_unpick (n a k : Nat) (xs : List UInt8) (b : UInt8) (ys : List UInt8)
    (h : xs.length = k) :
    n ↦[wms][ a ] xs ∗ n ↦[wms][ a + k ] [b] ∗ n ↦[wms][ a + k + 1 ] ys ⊢
      memBytes (H := NearState) (GF := GF) n a (xs ++ b :: ys) := by
  iintro ⟨H1, H2, H3⟩
  iapply (memBytes_append (GF := GF) (H := NearState) n a xs (b :: ys)).2
  rw [h]
  iframe H1
  iapply (memBytes_cons n (a + k) b ys).2
  iframe H2 H3

/-- `mwpi_loop` on an empty stack, for a block type without parameters. -/
theorem mwpi_loop0 {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame}
    {Φ : Post NearState GF} {Cg R : Nat} (bt : BlockType) (body : List Instr)
    (I : List Value → Frame → IProp GF) (hp : (Exec.blockType f.mi bt).params = []) :
    □ (∀ X l, I X (f.withLocals l) -∗ mwpi cfg lim d (f.withLocals l) X body
          (Post.mloop cfg Cg 0 [] I Φ)) ∗
      credits Cg (cfg.regularOpCost + R) ∗ ▷ (credits Cg R -∗ I [] f)
      ⊢ mwpi cfg lim d f [] [.loop bt body] Φ := by
  have h := mwpi_loop (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f) (Cg := Cg) (R := R)
    bt body [] [] I (by simp [hp])
  simpa [hp] using h

theorem storeBytes_load8 (b : UInt8) :
    storeBytes (loadValue NumType.i32 (some { bits := 8, signed := false }) (Memory.decodeLE [b])) 1
      = [b] := by
  have hb := b.toNat_lt
  simp [loadValue, storeBytes, storeRaw, Memory.decodeLE, List.range, List.range.loop]

theorem dst_step (sb ob : List UInt8) (k : Nat) (h1 : k < sb.length) :
    List.take k (List.take k sb ++ List.drop k ob) ++
        sb[k] :: List.drop (k + 1) (List.take k sb ++ List.drop k ob)
      = sb.take (k + 1) ++ ob.drop (k + 1) := by
  rw [List.take_left' (by simp; omega), List.drop_append,
    List.drop_eq_nil_of_le (by simp; omega)]
  simp [List.length_take, show min k sb.length = k by omega, List.drop_drop]
  rw [List.take_add_one, List.getElem?_eq_getElem h1, Option.toList_some, List.append_assoc,
    List.singleton_append]

end Bytes

/-- The loop invariant at iteration `k < N`: the locals `(dst, src + k, N - k, dst + k)`,
the first `k` bytes of `sb` copied, the credits of the iterations left. -/
def inv {GF : BundledGFunctors} [WasmGS NearState GF] (n inst : Nat) (mi : ModuleInst)
    (Cg R c₀ : Nat) (dst src : UInt32) (N : Nat) (ob sb : List UInt8) :
    List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (s c e : UInt32), ⌜X = [] ∧ g = ⟨#[.i32 dst, .i32 s, .i32 c, .i32 e], inst, mi⟩ ∧
      k < N ∧ s.toNat = src.toNat + k ∧ e.toNat = dst.toNat + k ∧ c.toNat = N - k⌝ ∗
    credits Cg (18 * (N - k) * c₀ + R) ∗ n ↦[wms][ dst.toNat ] (sb.take k ++ ob.drop k) ∗
    n ↦[wms][ src.toNat ] sb)

/-- The cost of `memcpy` of `N` bytes, activation excluded, in `regular_op_cost`s. -/
def cost (N : Nat) : Nat := if N = 0 then 4 else 18 * N + 6

section Spec

variable {GF : BundledGFunctors} [WasmGS NearState GF]

def pre (n : Nat) (dst src len : UInt32) (ob sb : List UInt8) (args : List Value) : IProp GF :=
  iprop(⌜args = [.i32 dst, .i32 src, .i32 len]⌝ ∗ n ↦[wms][ dst.toNat ] ob ∗
    n ↦[wms][ src.toNat ] sb)

def post (n : Nat) (dst src : UInt32) (sb : List UInt8) (_args rs : List Value) : IProp GF :=
  iprop(⌜rs = [.i32 dst]⌝ ∗ n ↦[wms][ dst.toNat ] sb ∗ n ↦[wms][ src.toNat ] sb)

/-- `memcpy` (function 951 of `contract.wasm`) of `len` bytes from `src` to `dst`. -/
theorem f951_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (dst src len : UInt32) (ob sb : List UInt8)
    (hob : ob.length = len.toNat) (hsb : sb.length = len.toNat)
    (hdst : dst.toNat + len.toNat ≤ 2 ^ 32) (hsrc : src.toNat + len.toNat ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f951 Cg (pre n dst src len ob sb)
        (fun _ => cost len.toNat * cfg.regularOpCost) (post n dst src sb) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  iunfold pre at HP
  icases HP with ⟨%hargs, Hd, Hs⟩
  subst hargs
  simp only [f951]
  by_cases h0 : len.toNat = 0
  · have hl : len = 0 := by
      apply UInt32.toNat_inj.mp; simpa using h0
    subst hl
    simp only [cost, h0, ite_true]
    mstep; mstep; mstep; mstep; mstep
    have e1 : ob = [] := List.eq_nil_of_length_eq_zero (by simpa using hob)
    have e2 : sb = [] := List.eq_nil_of_length_eq_zero (by simpa using hsb)
    subst e1 e2
    rw [htype]
    iframe Hc
    iunfold post
    iframe Hd Hs
    ipureintro; rfl
  · have hN : 0 < len.toNat := Nat.pos_of_ne_zero h0
    have hl : len ≠ 0 := fun e => h0 (by simp [e])
    simp only [cost, h0, ite_false]
    rw [show (18 * len.toNat + 6) * cfg.regularOpCost + R =
      6 * cfg.regularOpCost + (18 * len.toNat * cfg.regularOpCost + R) by rw [Nat.add_mul]; omega]
    mstep; mstep; mstep; mstep; mstep; mstep
    iapply mwpi_loop0 (Cg := Cg) (R := 18 * len.toNat * cfg.regularOpCost + R)
      (I := inv n inst mi Cg R cfg.regularOpCost dst src len.toNat ob sb) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold inv at HI
      icases HI with ⟨%k, %s, %c, %e, %⟨hX, hg, hk, hs, he, hc⟩, Hc, Hd, Hs⟩
      subst hX
      rw [hg]
      have hkN : k < sb.length := by omega
      ihave Hd := memBytes_pick n dst.toNat k (sb.take k ++ ob.drop k) (by simp; omega) $$ Hd
      icases Hd with ⟨Hd1, Hdk, Hd2⟩
      ihave Hs := memBytes_pick n src.toNat k sb hkN $$ Hs
      icases Hs with ⟨Hs1, Hsk, Hs2⟩
      rw [show 18 * (len.toNat - k) * cfg.regularOpCost + R =
        16 * cfg.regularOpCost + ((18 * (len.toNat - k) - 16) * cfg.regularOpCost + R) by
          rw [Nat.sub_mul]
          have : 16 * cfg.regularOpCost ≤ 18 * (len.toNat - k) * cfg.regularOpCost :=
            Nat.mul_le_mul_right _ (by omega)
          omega]
      mstep; mstep; mstep [Hsk]; mstep [Hdk]
      rw [storeBytes_load8]
      mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
      ihave Hd := memBytes_unpick n dst.toNat k (List.take k (List.take k sb ++ List.drop k ob)) sb[k]
        (List.drop (k + 1) (List.take k sb ++ List.drop k ob)) (by simp; omega) $$ [Hd1 Hdk Hd2]
      · iframe Hd1 Hdk Hd2
      ihave Hs := memBytes_unpick n src.toNat k (List.take k sb) sb[k] (List.drop (k + 1) sb)
        (by simp; omega) $$ [Hs1 Hsk Hs2]
      · iframe Hs1 Hsk Hs2
      have es : List.take k sb ++ sb[k] :: List.drop (k + 1) sb = sb := by simp
      rw [dst_step sb ob k hkN, es]
      have hc1 : (c + 4294967295).toNat = len.toNat - k - 1 := by
        rw [UInt32.toNat_add]; simp; omega
      by_cases hk1 : k + 1 < len.toNat
      · have hne : c + 4294967295 ≠ 0 := by
          intro h; rw [h] at hc1; simp at hc1; omega
        rw [show (18 * (len.toNat - k) - 16) * cfg.regularOpCost + R =
          2 * cfg.regularOpCost + (18 * (len.toNat - (k + 1)) * cfg.regularOpCost + R) by
            rw [show 18 * (len.toNat - k) - 16 = 2 + 18 * (len.toNat - (k + 1)) by omega, Nat.add_mul]
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
        iexists s + 1
        iexists c + 4294967295
        iexists e + 1
        iframe Hc Hd Hs
        ipureintro
        refine ⟨by simp, rfl, hk1, ?_, ?_, by omega⟩
        · rw [UInt32.toNat_add]; simp; omega
        · rw [UInt32.toNat_add]; simp; omega
      · have heq : c + 4294967295 = 0 := UInt32.toNat_inj.mp (by simp; omega)
        rw [show (18 * (len.toNat - k) - 16) * cfg.regularOpCost + R =
          2 * cfg.regularOpCost + R by
            rw [show 18 * (len.toNat - k) - 16 = 2 by omega]]
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
        have ed : List.take (k + 1) sb ++ List.drop (k + 1) ob = sb := by
          rw [List.take_of_length_le (by omega), List.drop_eq_nil_of_le (by omega), List.append_nil]
        rw [htype, ed]
        iframe Hc
        iunfold post
        iframe Hd Hs
        ipureintro; rfl
    isplitl [Hc]
    · iexact Hc
    inext
    iintro Hc
    iunfold inv
    iexists 0
    iexists src
    iexists len
    iexists dst
    simp only [Nat.sub_zero, List.take_zero, List.drop_zero, List.nil_append]
    iframe Hc Hd Hs
    ipureintro
    simp [hN]

end Spec

end WNear.Binary.MemCpy
