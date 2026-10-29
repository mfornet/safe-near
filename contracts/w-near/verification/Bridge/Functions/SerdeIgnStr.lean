import Bridge.Functions.ParseStrErr

/-!
# `ignore_str` (650) on a string without escapes (M6)

`ignore_value` (81) skips a string (a value or a key of an ignored object) with 650: the scan of 646
without UTF-8 validation.

```wat
;; 650 ignore_str(rd) -> i32        a 16-byte frame, written only on the error paths
loop                                ;; once per escape
  (index, ptr, len) := rd
  while index < len and ESCAPE[[ptr + index]] = 0: index += 1     ;; stored at each step
  index = len → Err(EofWhileParsingString) (651)
  b = '\' → index += 1; ignore_escape (652); loop
  b ≠ '"' → Err(ControlCharacterWhileParsingString) (651)
  b = '"' → index += 1; Ok (0)
```

* `f650_noesc`: from `i`, plain bytes up to a `"`: `0`, the reader past the `"`, at
  `56 + 21` per byte (`cost650`).
* `str_noesc_shape`: on such an input, `stringBody` (the model) accepts exactly at that `"`.
-/

namespace WNear.Binary.SerdeIgnStr

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.ArgsLeaves (sliceRead)
open WNear.Binary.SerdeRead (rd)
open WNear.Binary.ParseStr (plain escTable esc_at escTable_length)
open NearInterface.Json (stringBody)

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

/-- On plain bytes then a byte that stops the scan and is not `\`, the model's string is accepted
only at a `"`. -/
theorem str_noesc_shape (body tail : List UInt8) (hplain : ∀ b ∈ body, plain b = true)
    (hstop : ∀ x rest, tail = x :: rest → plain x = false ∧ x ≠ 0x5C) {x : Option String} {r : List UInt8}
    (h : stringBody (body ++ tail) [] = some (x, r)) : tail = 0x22 :: r := by
  rw [ParseStr.stringBody_skip body tail [] hplain] at h
  match tail, hstop, h with
  | [], _, h => simp [stringBody] at h
  | y :: t, hstop, h =>
    obtain ⟨hyp, hy5c⟩ := hstop y t rfl
    by_cases hy : y = 0x22
    · subst hy
      rw [stringBody.eq_2] at h
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.2]
    · have hlt : y < 0x20 := by
        simp only [plain, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq, Bool.and_eq_false_imp] at hyp
        apply UInt8.lt_iff_toNat_lt.mpr
        have e5c : y.toNat ≠ 0x5C := fun e => hy5c (UInt8.toNat_inj.mp (by rw [e]; rfl))
        have e22 : y.toNat ≠ 0x22 := fun e => hy (UInt8.toNat_inj.mp (by rw [e]; rfl))
        simp; by_contra hc; exact absurd (hyp (by omega)) (by simp; omega)
      rw [stringBody.eq_13 _ _ _ hy (fun _ _ e _ => hy5c e), if_pos hlt] at h
      simp at h

section L650

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 650's frame: `(rd, sp, index, ptr, len, byte)`. -/
def fr650 (inst : Nat) (mi : ModuleInst) (de l1 l2 l3 l4 l5 : UInt32) : Frame :=
  ⟨#[.i32 de, .i32 l1, .i32 l2, .i32 l3, .i32 l4, .i32 l5], inst, mi⟩

/-- The scan loop's invariant: at `k ≤ i + m` (the index stored too), `21` per byte left. -/
def inv650 (n inst : Nat) (mi : ModuleInst) (Cg c₀ E R : Nat) (de l1 l3 l4 : UInt32) (i m : Nat)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (l5 : UInt32), ⌜X = [] ∧ g = fr650 inst mi de l1 (UInt32.ofNat k) l3 l4 l5 ∧
      i ≤ k ∧ k ≤ i + m⌝ ∗
    credits Cg (21 * (i + m - k) * c₀ + E * c₀ + R) ∗ n ↦[i32][ de.toNat + 8 ] UInt32.ofNat k ∗ P)

theorem inv650_intro (n inst : Nat) (mi : ModuleInst) (Cg c₀ E R : Nat) (de l1 l3 l4 : UInt32)
    (i m : Nat) (P : IProp GF) (k : Nat) (l5 : UInt32) (h1 : i ≤ k) (h2 : k ≤ i + m) :
    credits Cg (21 * (i + m - k) * c₀ + E * c₀ + R) ∗ n ↦[i32][ de.toNat + 8 ] UInt32.ofNat k ∗ P ⊢
      inv650 n inst mi Cg c₀ E R de l1 l3 l4 i m P []
        ⟨#[.i32 de, .i32 l1, .i32 (UInt32.ofNat k), .i32 l3, .i32 l4, .i32 l5], inst, mi⟩ := by
  iintro ⟨Hc, D8, HP⟩
  iunfold inv650
  iexists k
  iexists l5
  iframe Hc D8 HP
  ipureintro; exact ⟨rfl, rfl, h1, h2⟩

/-- 650's cost on an escape-free string of `m` bytes. -/
def cost650 (m : Nat) : Nat := 56 + 21 * m

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`ignore_str(rd)`** (650) on a string without escapes: from `i`, plain bytes up to a `"`: `0`,
the reader past the `"`. -/
theorem f650_noesc (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (Cg : Nat)
    (gt : GlobalType) (sp de ptr : UInt32) (bs body rest : List UInt8) (i : Nat)
    (hlen : bs.length < 2 ^ 32) (hptr : ptr.toNat + bs.length ≤ 2 ^ 32)
    (hsplit : bs.drop i = body ++ 0x22 :: rest) (hplain : ∀ b ∈ body, plain b = true) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f650 Cg
        (fun args => iprop(⌜args = [.i32 de]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs i ∗
          n ↦[wms][ 1062392 ] escTable))
        (fun _ => cost650 body.length * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 0]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗ rd n de ptr bs (i + body.length + 1) ∗
          n ↦[wms][ 1062392 ] escTable)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hrd, He⟩
  subst hargs
  have hil : i + body.length + 1 ≤ bs.length := by
    have := congrArg List.length hsplit; simp at this; omega
  iunfold rd, sliceRead at Hrd
  icases Hrd with ⟨⟨D0, D4, D8⟩, Hb⟩
  simp only [f650, cost650]
  have hm0 : i + body.length - i = body.length := by omega
  rw [show (56 + 21 * body.length) * cfg.regularOpCost + R =
    56 * cfg.regularOpCost + (21 * body.length * cfg.regularOpCost + R) by
      simp only [Nat.add_mul]; omega]
  generalize hW : 21 * body.length * cfg.regularOpCost = W
  mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
  mstep
  mcredits (cfg.regularOpCost + (W + 49 * cfg.regularOpCost + R))
  iapply mwpi_cons
  iapply MemCpy.mwpi_loop0 (Cg := Cg)
    (R := W + 49 * cfg.regularOpCost + R)
    (I := fun X fr => iprop(⌜X = [] ∧ fr = fr650 inst mi de (sp - 16) 0 0 0 0⌝ ∗
      credits Cg (W + 49 * cfg.regularOpCost + R) ∗
      n ↦[wms][ 1062392 ] escTable ∗ n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
      n ↦[i32][ de.toNat + 8 ] UInt32.ofNat i ∗ n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    icases HI with ⟨%⟨hX, hfr⟩, Hc, He, D0, D4, D8, Hb, Hg⟩
    subst hX
    rw [hfr]
    simp only [fr650]
    clear hfr
    mstep; mstep [D8]; mstep; mstep; mstep [D0]; mstep; mstep; mstep [D4]; mstep
    mstep
    mcredits (cfg.regularOpCost + (W + 38 * cfg.regularOpCost + R))
    iapply mwpi_cons
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := W + 38 * cfg.regularOpCost + R)
      (I := inv650 n inst mi Cg cfg.regularOpCost 38 R de (sp - 16) ptr (UInt32.ofNat bs.length) i body.length
        iprop(n ↦[wms][ 1062392 ] escTable ∗ n ↦[i32][ de.toNat ] ptr ∗ n ↦[i32][ de.toNat + 4 ] UInt32.ofNat bs.length ∗
          n ↦[wms][ ptr.toNat ] bs ∗ g ↦[wg] ⟨gt, .i32 (sp - 16)⟩)) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold inv650 at HI
      icases HI with ⟨%k, %l5, %⟨hX, hfr, hik, hkm⟩, Hc, D8, HP⟩
      subst hX
      rw [hfr]
      simp only [fr650]
      clear hfr
      icases HP with ⟨He, D0, D4, Hb, Hg⟩
      have hkl : k < bs.length := by omega
      have hge : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat k) (UInt32.ofNat bs.length)) = 0 := by
        have hu : (UInt32.ofNat k).toNat = k := by simp; omega
        have hv : (UInt32.ofNat bs.length).toNat = bs.length := by simp; omega
        generalize UInt32.ofNat k = u at hu ⊢
        generalize UInt32.ofNat bs.length = v at hv ⊢
        simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
      have hbk : bs[k]? = (body ++ 0x22 :: rest)[k - i]? := by
        rw [← hsplit, List.getElem?_drop]; congr 1; omega
      ihave Hb := MemCpy.memBytes_pick n ptr.toNat k bs hkl $$ Hb
      icases Hb with ⟨B1, Bk, B2⟩
      obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
      rw [hxk]
      rw [List.getElem?_eq_getElem hkl, hxk] at hbk
      have es : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
      have hx8 : x.toNat < 256 := x.toNat_lt
      by_cases hkm' : k < i + body.length
      · have hxb : plain x = true := by
          rw [List.getElem?_append_left (by omega)] at hbk
          exact hplain x (List.mem_of_getElem? hbk.symm)
        rw [show 21 * (i + body.length - k) * cfg.regularOpCost + 38 * cfg.regularOpCost + R =
          21 * cfg.regularOpCost + (21 * (i + body.length - (k + 1)) * cfg.regularOpCost + 38 * cfg.regularOpCost + R) by
            rw [show i + body.length - k = (i + body.length - (k + 1)) + 1 by omega]; simp only [Nat.mul_add, Nat.add_mul]; omega]
        generalize hZ : 21 * (i + body.length - (k + 1)) * cfg.regularOpCost = Z
        mstep; mstep; mstep
        brn hge
        clear hge
        mstep; mstep; mstep; mstep
        mstep [Bk] with (simp [UInt32.toNat_add]; omega)
        simp only [SerdeKey.load8]
        ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
        · iframe B1 Bk B2
        rw [es]
        mstep; mstep; mstep
        ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
        icases He with ⟨E1, Ek, E2⟩
        mstep [Ek] with (simp [UInt32.toNat_add, UInt8.toNat_toUInt32]; omega)
        rw [SerdeKey.load8, esc_at, if_pos hxb]
        ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
        · iframe E1 Ek E2
        rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
        brn rfl
        mstep; mstep; mstep; mstep; mstep
        mstep [D8]
        rw [SerdeRead.ofNat_succ k (by omega)]
        mstep
        simp only [Post.mloop, List.length_nil, Nat.sub_zero, List.drop_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        iapply inv650_intro n inst mi Cg cfg.regularOpCost 38 R de (sp - 16) ptr _ i body.length _ (k + 1) _
          (by omega) (by omega)
        iframe D8 He D0 D4 Hb Hg
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      · have hk : k = i + body.length := by omega
        have hx : x = 0x22 := by
          rw [List.getElem?_append_right (by omega), show k - i - body.length = 0 by omega] at hbk
          simpa using hbk
        rw [show 21 * (i + body.length - k) * cfg.regularOpCost = 0 by rw [show i + body.length - k = 0 by omega]; simp,
          Nat.zero_add]
        mstep; mstep; mstep
        brn hge
        clear hge
        mstep; mstep; mstep; mstep
        mstep [Bk] with (simp [UInt32.toNat_add]; omega)
        simp only [SerdeKey.load8]
        ihave Hb := MemCpy.memBytes_unpick n ptr.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
        · iframe B1 Bk B2
        rw [es]
        mstep; mstep; mstep
        ihave He := MemCpy.memBytes_pick n 1062392 x.toNat escTable (by rw [escTable_length]; exact x.toNat_lt) $$ He
        icases He with ⟨E1, Ek, E2⟩
        mstep [Ek] with (simp [UInt32.toNat_add, UInt8.toNat_toUInt32]; omega)
        rw [SerdeKey.load8, esc_at, if_neg (by rw [hx]; decide)]
        ihave He := MemCpy.memBytes_unpick n 1062392 x.toNat (escTable.take x.toNat) _ (escTable.drop (x.toNat + 1)) (by simp [escTable_length]; omega) $$ [E1 Ek E2]
        · iframe E1 Ek E2
        rw [show List.take x.toNat escTable ++ escTable[x.toNat]'(by rw [escTable_length]; exact x.toNat_lt) :: List.drop (x.toNat + 1) escTable = escTable by simp]
        iapply mwpi_cons
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, by decide⟩
        mctrl_norm
        simp only [Post.mloop]
        mctrl_norm
        repeat mpay
        rw [hx]
        mstep; mstep; mstep; mstep
        brn (by decide)
        mstep; mstep; mstep; mstep
        brt (by decide)
        mstep; mstep; mstep; mstep
        mstep [D8]
        rw [SerdeRead.ofNat_succ k (by omega)]
        mstep; mstep; mstep
        (try simp only [Post.mloop]); (try mctrl_norm); (repeat mpay)
        mstep; mstep; mstep; mstep [Hg]
        rw [show sp - 16 + 16 = sp by simp]
        repeat mstep
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        iframe Hg He
        isplitr
        · ipureintro; simp [htype]
        iunfold rd, sliceRead
        rw [hk]
        iframe D0 D4 D8 Hb
    · iframe Hc
      inext
      iintro Hc
      iapply inv650_intro n inst mi Cg cfg.regularOpCost 38 R de (sp - 16) ptr _ i body.length _ i _
        (by omega) (by omega)
      rw [hm0, hW]
      iframe D8 He D0 D4 Hb Hg
      iexact Hc
  · iframe Hc
    inext
    iintro Hc
    iframe Hc He D0 D4 D8 Hb Hg
    ipureintro; exact ⟨rfl, rfl⟩

end L650

end WNear.Binary.SerdeIgnStr
