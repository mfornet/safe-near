import Bridge.Functions.SerdeRead
import Bridge.Methods.BalanceOfArgs

/-!
# Key matching in serde's derived field visitors (M6): `bcmp` and slice equality

A struct's field visitor compares the key's bytes with each field name:

```wat
;; 953 bcmp(a, b, len) -> i32           compiler_builtins: 0 when equal, else a[k] - b[k] at the
;;                                      first difference k
;; 755 <[u8] as SlicePartialEq>::equal(a, la, b, lb) -> i32   la = lb && bcmp(a, b, la) == 0
;; 754 <[A] as PartialEq<[B]>>::eq      755
;; 194 __FieldVisitor::visit_str(out?, p, k) -> i64 (ft_balance_of)
;;                                      eq(p, k, "account_id" @ 1051092, 10) ? 0 : 256
```

* `f953_spec`: `bcmp` on two separately owned ranges of the same length: a result that is `0`
  exactly when the bytes are equal; `cost953 len`.
* `f755_spec`, `f754_spec`: slice equality, `1` exactly when the slices are equal; the cost is
  bounded by the second slice.s length (`bcmp` runs only when the lengths agree), so a field
  visitor.s cost does not depend on the key.
* `f194_spec`: `ft_balance_of`'s field visitor: field 0 (`account_id`, the `i64` 0) on the key
  `account_id`, `__ignore` (the `i64` 256) on any other key, with the 10 bytes at 1051092
  (`WNear.BalanceOfArgs.keyBytes`, `keyData_segment`) owned; `cost194` regular_op_costs.
-/

namespace WNear.Binary.SerdeKey

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-- `bcmp`'s cost, in `regular_op_cost`s, activation excluded. -/
def cost953 (len : Nat) : Nat := 12 + 25 * len

set_option maxRecDepth 100000 in
theorem ld8 (u : UInt8) :
    UInt32.ofNat (if false = true then Numeric.signExtend 32 8 (Memory.decodeLE [u]) else Memory.decodeLE [u]) =
      u.toUInt32 := by
  revert u; exact SerdeRead.uint8_forall (by decide +kernel)

theorem load8 (u : UInt8) :
    loadValue NumType.i32 (some { bits := 8, signed := false }) (Memory.decodeLE [u]) = .i32 u.toUInt32 := by
  simp only [loadValue]; rw [ld8]

section L953

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 953's frame: `(a + k, b + k, len - k, r, x, y)`. -/
def fr953 (inst : Nat) (mi : ModuleInst) (a b c r x y : UInt32) : Frame :=
  ⟨#[.i32 a, .i32 b, .i32 c, .i32 r, .i32 x, .i32 y], inst, mi⟩

/-- `bcmp`'s loop invariant: the first `k < N` bytes equal, credits for the `N - k` iterations
left. -/
def inv953 (n inst : Nat) (mi : ModuleInst) (Cg c₀ W E R : Nat) (a b : UInt32) (N : Nat)
    (xs ys : List UInt8) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (x y : UInt32), ⌜X = [] ∧
      g = fr953 inst mi (a + UInt32.ofNat k) (b + UInt32.ofNat k) (UInt32.ofNat (N - k)) 0 x y ∧
      k < N ∧ xs.take k = ys.take k⌝ ∗
    credits Cg (W * (N - k) * c₀ + E * c₀ + R) ∗ n ↦[wms][ a.toNat ] xs ∗ n ↦[wms][ b.toNat ] ys)

set_option maxRecDepth 100000 in
/-- **`bcmp(a, b, len)`** (953) on `xs` at `a` and `ys` at `b`, both of length `len`: `0` exactly
when `xs = ys`. -/
theorem f953_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (a b len : UInt32) (xs ys : List UInt8)
    (hx : xs.length = len.toNat) (hy : ys.length = len.toNat)
    (ha : a.toNat + len.toNat ≤ 2 ^ 32) (hb : b.toNat + len.toNat ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f953 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 b, .i32 len]⌝ ∗ n ↦[wms][ a.toNat ] xs ∗
          n ↦[wms][ b.toNat ] ys))
        (fun _ => cost953 len.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(∃ r : UInt32, ⌜rs = [.i32 r] ∧ (r = 0 ↔ xs = ys)⌝ ∗
          n ↦[wms][ a.toNat ] xs ∗ n ↦[wms][ b.toNat ] ys)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hx, Hy⟩
  subst hargs
  simp only [f953, cost953]
  by_cases h0 : len.toNat = 0
  · have hl : len = 0 := by apply UInt32.toNat_inj.mp; simpa using h0
    subst hl
    repeat mstep
    have e1 : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hx)
    have e2 : ys = [] := List.eq_nil_of_length_eq_zero (by simpa using hy)
    subst e1 e2
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iexists 0
    iframe Hx Hy
    ipureintro
    simp [htype]
  · have hN : 0 < len.toNat := Nat.pos_of_ne_zero h0
    have hne : len ≠ 0 := fun e => h0 (by simp [e])
    rw [show (12 + 25 * len.toNat) * cfg.regularOpCost + R =
      6 * cfg.regularOpCost + (25 * (len.toNat - 0) * cfg.regularOpCost + 6 * cfg.regularOpCost + R) by
        rw [Nat.sub_zero, Nat.add_mul]; omega]
    repeat mstep
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := (25 * len.toNat + 6) * cfg.regularOpCost + R)
      (I := inv953 n inst mi Cg cfg.regularOpCost 25 6 R a b len.toNat xs ys) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold inv953 at HI
      icases HI with ⟨%k, %x, %y, %⟨hX, hg, hk, htk⟩, Hc, Hx, Hy⟩
      subst hX
      rw [hg]
      simp only [fr953]
      have hkx : k < xs.length := by omega
      have hky : k < ys.length := by omega
      ihave Hx := MemCpy.memBytes_pick n a.toNat k xs hkx $$ Hx
      icases Hx with ⟨X1, Xk, X2⟩
      ihave Hy := MemCpy.memBytes_pick n b.toNat k ys hky $$ Hy
      icases Hy with ⟨Y1, Yk, Y2⟩
      rw [show 25 * (len.toNat - k) * cfg.regularOpCost + 6 * cfg.regularOpCost + R =
        25 * cfg.regularOpCost + (25 * (len.toNat - (k + 1)) * cfg.regularOpCost + 6 * cfg.regularOpCost + R) by
          rw [show 25 * (len.toNat - k) = 25 + 25 * (len.toNat - (k + 1)) by omega, Nat.add_mul]; omega]
      generalize hZ : 25 * (len.toNat - (k + 1)) * cfg.regularOpCost = Z
      mstep
      mstep [Xk] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      mstep [Yk] with (simp [UInt32.toNat_add]; omega)
      mstep; mstep
      simp only [ld8, load8]
      by_cases hxy : xs[k] = ys[k]
      · have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne xs[k].toUInt32 ys[k].toUInt32) = 0 := by
          simp [Numeric.bool, Numeric.irelop32, hxy]
        mstep_not_taken with exact hc
        mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
        ihave Hx := MemCpy.memBytes_unpick n a.toNat k (xs.take k) xs[k] (xs.drop (k + 1)) (by simp; omega) $$ [X1 Xk X2]
        · iframe X1 Xk X2
        ihave Hy := MemCpy.memBytes_unpick n b.toNat k (ys.take k) ys[k] (ys.drop (k + 1)) (by simp; omega) $$ [Y1 Yk Y2]
        · iframe Y1 Yk Y2
        have esx : List.take k xs ++ xs[k] :: List.drop (k + 1) xs = xs := by simp
        have esy : List.take k ys ++ ys[k] :: List.drop (k + 1) ys = ys := by simp
        rw [esx, esy]
        have htk1 : xs.take (k + 1) = ys.take (k + 1) := by
          rw [List.take_add_one, List.take_add_one, htk, List.getElem?_eq_getElem hkx, List.getElem?_eq_getElem hky, hxy]
        have hc1 : UInt32.ofNat (len.toNat - k) + 4294967295 = UInt32.ofNat (len.toNat - (k + 1)) := by
          apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add]; omega
        rw [hc1]
        by_cases hk1 : k + 1 < len.toNat
        · have hlt := len.toNat_lt
          have hne0 : UInt32.ofNat (len.toNat - (k + 1)) ≠ 0 := by
            intro h; have := congrArg UInt32.toNat h; simp at this; omega
          have hc2 : Numeric.bool (UInt32.ofNat (len.toNat - (k + 1)) == 0) = 0 := by
            simp [Numeric.bool, hne0]
          generalize hcv : UInt32.ofNat (len.toNat - (k + 1)) = cv at hc2 ⊢
          clear esx esy hc1 hc hne0
          mstep_not_taken with exact hc2
          mstep
          simp only [Post.mloop, List.reverse_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iunfold inv953
          iexists k + 1
          iexists xs[k].toUInt32
          iexists ys[k].toUInt32
          iframe Hx Hy
          isplitr
          · ipureintro
            refine ⟨rfl, ?_, hk1, htk1⟩
            rw [← hcv]
            rw [UInt32.add_assoc, UInt32.add_assoc, SerdeRead.ofNat_succ k (by omega)]
            rfl
          rw [← hZ]
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        · have hk1 : k + 1 = len.toNat := by omega
          have hc2 : Numeric.bool (UInt32.ofNat (len.toNat - (k + 1)) == 0) = 1 := by
            rw [show len.toNat - (k + 1) = 0 by omega]; rfl
          generalize hcv : UInt32.ofNat (len.toNat - (k + 1)) = cv at hc2 ⊢
          clear esx esy hc1 hc
          mstep_taken with exact hc2
          simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_succ, Post.mblock_br_zero]
          mpay
          repeat mstep
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          iexists 0
          iframe Hx Hy
          ipureintro
          refine ⟨by simp [htype], ?_⟩
          simp only [true_iff]
          have := htk1
          rwa [List.take_of_length_le (by omega), List.take_of_length_le (by omega)] at this
      · have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne xs[k].toUInt32 ys[k].toUInt32) = 1 := by
          simp [Numeric.bool, Numeric.irelop32]
          intro h; apply hxy; exact UInt8.toUInt32_inj.mp h
        mstep_taken with exact hc
        simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero]
        mpay
        repeat mstep
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        iexists xs[k].toUInt32 - ys[k].toUInt32
        ihave Hx := MemCpy.memBytes_unpick n a.toNat k (xs.take k) xs[k] (xs.drop (k + 1)) (by simp; omega) $$ [X1 Xk X2]
        · iframe X1 Xk X2
        ihave Hy := MemCpy.memBytes_unpick n b.toNat k (ys.take k) ys[k] (ys.drop (k + 1)) (by simp; omega) $$ [Y1 Yk Y2]
        · iframe Y1 Yk Y2
        have esx : List.take k xs ++ xs[k] :: List.drop (k + 1) xs = xs := by simp
        have esy : List.take k ys ++ ys[k] :: List.drop (k + 1) ys = ys := by simp
        rw [esx, esy]
        iframe Hx Hy
        ipureintro
        refine ⟨by simp [htype], ?_⟩
        constructor
        · intro h
          exfalso; apply hxy; apply UInt8.toUInt32_inj.mp
          have := congrArg (· + ys[k].toUInt32) h
          simpa using this
        · intro h; subst h; exact absurd rfl hxy
    isplitl [Hc]
    · iexact Hc
    inext
    iintro Hc
    iunfold inv953
    iexists 0
    iexists 0
    iexists 0
    rw [show 25 * (len.toNat - 0) * cfg.regularOpCost + 6 * cfg.regularOpCost + R =
      (25 * len.toNat + 6) * cfg.regularOpCost + R by rw [Nat.sub_zero, Nat.add_mul]]
    iframe Hc Hx Hy
    ipureintro
    simp [fr953, hN]
    done

end L953

/-! ## Slice equality (755, 754) -/

/-- Slice equality's cost: `bcmp` and the comparison of the lengths. -/
def cost755 (len : Nat) : Nat := 30 + cost953 len

section L755

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`<[u8] as SlicePartialEq>::equal(a, la, b, lb)`** (755): `1` exactly when the slices are
equal (the lengths first, then `bcmp`). -/
theorem f755_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a953 : Nat) (ha953 : mi.funcAddrs[953]? = some a953)
    (hd : d + 1 < lim.maxCallDepth) (Cg : Nat) (a la b lb : UInt32) (xs ys : List UInt8)
    (hx : xs.length = la.toNat) (hy : ys.length = lb.toNat)
    (ha : a.toNat + la.toNat ≤ 2 ^ 32) (hb : b.toNat + lb.toNat ≤ 2 ^ 32) :
    a953 ↪[wf] FuncInst.wasm types[15]! inst f953 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f755 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 la, .i32 b, .i32 lb]⌝ ∗ n ↦[wms][ a.toNat ] xs ∗
          n ↦[wms][ b.toNat ] ys))
        (fun _ => cost755 lb.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 (if xs = ys then 1 else 0)]⌝ ∗
          n ↦[wms][ a.toNat ] xs ∗ n ↦[wms][ b.toNat ] ys)) := by
  iintro ⟨#F953, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hx, Hy⟩
  subst hargs
  have t15 : types[15]!.params.length = 3 := by rfl
  simp only [f755, cost755]
  rw [show (30 + cost953 lb.toNat) * cfg.regularOpCost + R = 30 * cfg.regularOpCost + (cost953 lb.toNat * cfg.regularOpCost + R) by
    rw [Nat.add_mul]; omega]
  by_cases hl : la = lb
  · subst hl
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne la la) = 0 := by simp [Numeric.bool, Numeric.irelop32]
    repeat mstep
    have e := Nat.add_mul 12 (cost953 la.toNat) cfg.regularOpCost
    mcall (f953_spec cfg (lim := lim) (d + 1) types[15]! (by rfl) inst mi n hn Cg a b la xs ys hx hy ha hb) using [Hx Hy]
    · iframe Hx Hy
    icases HQ with ⟨%r, %⟨hrs, hr⟩, Hx, Hy⟩
    subst hrs
    rw [show 21 * cfg.regularOpCost + (cost953 la.toNat * cfg.regularOpCost + R) -
      (12 + cost953 la.toNat) * cfg.regularOpCost = 9 * cfg.regularOpCost + R by
        rw [Nat.add_mul]; omega]
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hx Hy
    ipureintro
    by_cases h : xs = ys
    · simp [htype, h, hr.mpr h, Numeric.bool]
    · have : r ≠ 0 := fun e => h (hr.mp e)
      simp [htype, h, this, Numeric.bool]
  · have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne la lb) = 1 := by
      simp [Numeric.bool, Numeric.irelop32, hl]
    generalize hM : cost953 lb.toNat * cfg.regularOpCost = M
    repeat mstep
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hx Hy
    ipureintro
    have hne : xs ≠ ys := by
      intro h; subst h; apply hl; apply UInt32.toNat_inj.mp; omega
    simp [htype, hne]

end L755

/-- `<[A] as PartialEq<[B]>>::eq`'s cost: 755 and its activation. -/
def cost754 (len : Nat) : Nat := 20 + cost755 len

section L754

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`<[A] as PartialEq<[B]>>::eq(a, la, b, lb)`** (754): slice equality (755). -/
theorem f754_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a755 a953 : Nat) (ha755 : mi.funcAddrs[755]? = some a755)
    (ha953 : mi.funcAddrs[953]? = some a953)
    (hd : d + 2 < lim.maxCallDepth) (Cg : Nat) (a la b lb : UInt32) (xs ys : List UInt8)
    (hx : xs.length = la.toNat) (hy : ys.length = lb.toNat)
    (ha : a.toNat + la.toNat ≤ 2 ^ 32) (hb : b.toNat + lb.toNat ≤ 2 ^ 32) :
    a755 ↪[wf] FuncInst.wasm types[33]! inst f755 ∗ a953 ↪[wf] FuncInst.wasm types[15]! inst f953 ∗
      inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f754 Cg
        (fun args => iprop(⌜args = [.i32 a, .i32 la, .i32 b, .i32 lb]⌝ ∗ n ↦[wms][ a.toNat ] xs ∗
          n ↦[wms][ b.toNat ] ys))
        (fun _ => cost754 lb.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 (if xs = ys then 1 else 0)]⌝ ∗
          n ↦[wms][ a.toNat ] xs ∗ n ↦[wms][ b.toNat ] ys)) := by
  iintro ⟨#F755, #F953, #Hi⟩
  ihave #S755 := f755_spec (GF := GF) cfg lim (d + 1) types[33]! (by rfl) inst mi n hn a953 ha953 (by omega) Cg
    a la b lb xs ys hx hy ha hb $$ [F953 Hi]
  · iframe F953 Hi
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hx, Hy⟩
  subst hargs
  have t33 : types[33]!.params.length = 4 := by rfl
  simp only [f754, cost754]
  rw [show (20 + cost755 lb.toNat) * cfg.regularOpCost + R = 20 * cfg.regularOpCost + (cost755 lb.toNat * cfg.regularOpCost + R) by
    rw [Nat.add_mul]; omega]
  have e := Nat.add_mul 12 (cost755 lb.toNat) cfg.regularOpCost
  repeat mstep
  mcall S755 using [Hx Hy]
  · iframe Hx Hy
  icases HQ with ⟨%hrs, Hx, Hy⟩
  subst hrs
  rw [show 16 * cfg.regularOpCost + (cost755 lb.toNat * cfg.regularOpCost + R) -
    (12 + cost755 lb.toNat) * cfg.regularOpCost = 4 * cfg.regularOpCost + R by rw [Nat.add_mul]; omega]
  mpay
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  iframe Hx Hy
  ipureintro
  simp [htype]

end L754

/-! ## `ft_balance_of`'s field visitor (194) -/

set_option maxRecDepth 100000 in
/-- The field name `account_id` is in the data segment at 1051092. -/
theorem keyData_segment :
    (List.range 10).map (fun k => wNearSource.read (159306 + (1051092 - 1048576) + k)) =
      WNear.BalanceOfArgs.keyBytes := by
  decide

/-- The field visitor's cost: `eq` (754) on 10 bytes, its activation and 194's own. -/
def cost194 : Nat := 30 + cost754 10

section L194

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`__FieldVisitor::visit_str(p, k)`** (194, `ft_balance_of`'s `Input`): `Ok(field 0)` (the
`i64` 0) on the key `account_id`, `Ok(__ignore)` (the `i64` 256) on any other, the field name owned
at 1051092. -/
theorem f194_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a754 a755 a953 : Nat) (ha754 : mi.funcAddrs[754]? = some a754)
    (ha755 : mi.funcAddrs[755]? = some a755) (ha953 : mi.funcAddrs[953]? = some a953)
    (hd : d + 3 < lim.maxCallDepth) (Cg : Nat) (p k : UInt32) (key : List UInt8)
    (hk : key.length = k.toNat) (hp : p.toNat + k.toNat ≤ 2 ^ 32) :
    a754 ↪[wf] FuncInst.wasm types[33]! inst f754 ∗ a755 ↪[wf] FuncInst.wasm types[33]! inst f755 ∗
      a953 ↪[wf] FuncInst.wasm types[15]! inst f953 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f194 Cg
        (fun args => iprop(⌜args = [.i32 p, .i32 k]⌝ ∗ n ↦[wms][ p.toNat ] key ∗
          n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes))
        (fun _ => cost194 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i64 (if key = WNear.BalanceOfArgs.keyBytes then 0 else 256)]⌝ ∗
          n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes)) := by
  iintro ⟨#F754, #F755, #F953, #Hi⟩
  have hkl : WNear.BalanceOfArgs.keyBytes.length = (10 : UInt32).toNat := rfl
  ihave #S754 := f754_spec (GF := GF) cfg lim (d + 1) types[33]! (by rfl) inst mi n hn a755 a953 ha755 ha953
    (by omega) Cg p k 1051092 10 key WNear.BalanceOfArgs.keyBytes hk hkl hp (by decide) $$ [F755 F953 Hi]
  · iframe F755 F953 Hi
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hk, Hd⟩
  subst hargs
  have t33 : types[33]!.params.length = 4 := by rfl
  simp only [f194, cost194]
  rw [show (30 + cost754 10) * cfg.regularOpCost + R = 30 * cfg.regularOpCost + (cost754 10 * cfg.regularOpCost + R) by
    rw [Nat.add_mul]; omega]
  have e := Nat.add_mul 11 (cost754 10) cfg.regularOpCost
  repeat mstep
  mcall S754 using [Hk Hd]
  · iframe Hk Hd
  icases HQ with ⟨%hrs, Hk, Hd⟩
  subst hrs
  rw [show 24 * cfg.regularOpCost + (cost754 10 * cfg.regularOpCost + R) -
    (11 + cost754 10) * cfg.regularOpCost = 13 * cfg.regularOpCost + R by rw [Nat.add_mul]; omega]
  by_cases hkey : key = WNear.BalanceOfArgs.keyBytes
  · simp only [hkey, if_true]
    iapply Borrow.mwpi_select_true'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨by omega, by decide⟩
    inext
    iintro Hc
    rw [show 13 * cfg.regularOpCost + R - cfg.regularOpCost = 12 * cfg.regularOpCost + R by omega]
    mpay
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hk Hd
    ipureintro
    simp [htype]
  · simp only [hkey, if_false]
    have h := mwpi_select_false (GF := GF) (vs := []) (cfg := cfg) (lim := lim) (d := d)
      (f := { locals := #[Value.i32 p, Value.i32 k], inst := inst, mi := mi }) (Cg := Cg) (R := 12 * cfg.regularOpCost + R)
      (Φ := Post.mfunc cfg Cg type.results.length
        { ret := fun rs => iprop(credits Cg R ∗ ⌜rs = [Value.i64 256]⌝ ∗
            n ↦[wms][ p.toNat ] key ∗ n ↦[wms][ 1051092 ] WNear.BalanceOfArgs.keyBytes) })
      none (.i64 0) (.i64 256)
    simp only [List.nil_append] at h
    rw [show 13 * cfg.regularOpCost + R = cfg.regularOpCost + (12 * cfg.regularOpCost + R) by omega]
    iapply h
    isplitl [Hc]
    · iexact Hc
    inext
    iintro Hc
    mpay
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hk Hd
    ipureintro
    simp [htype]

end L194

end WNear.Binary.SerdeKey
