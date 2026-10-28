import Bridge.Functions.SerdeKey
import NearInterface.AccountId

/-!
# `is_valid_account_id` (554) against `validAccountIdBytes` (M6)

near-sdk 3.1.0's `env::is_valid_account_id(&[u8]) -> bool`, which `ValidAccountId::try_from`
(502) runs on the deserialized `String`:

```wat
;; 673 <&[T] as IntoIterator>::into_iter(out, p, len)   [out + 4] := p + len; [out] := p
;; 554 is_valid_account_id(p, len) -> i32               (a 16-byte frame for the iterator)
len - 2 > 62 (unsigned) → 0
(cur, end) := into_iter(p, len);  prev := 1
loop
  prev' := prev
  cur = end → return prev' ^ 1                 ;; no separator at the end
  b := [cur]
  (b - 97) & 255 < 26 → sep := 0               ;; a..z
  (b - 48) & 255 < 10 → sep := 0               ;; 0..9
  b - 45 < 2 (unsigned) → sep := 1             ;; - .
  b = 95 → sep := 1                            ;; _
  otherwise → return 0
  cur += 1;  prev := sep
  prev' & sep = 1 → return 0                   ;; two separators in a row (or one first)
```

* `f673_spec`: the iterator's two words.
* `byte_cases`: the five ways a byte goes through the four tests, `decide`d over all 256 bytes,
  each with the class `accountIdFormat` gives it (`alnum`, `sep`, neither).
* `f554_spec`: `1` exactly when `validAccountIdBytes bs`, at `cost554 len`. The loop (`inv554`) keeps
  `accountIdFormat true bs = accountIdFormat prev (bs.drop k)`.
-/

namespace WNear.Binary.AccountIdValid

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.VecFromElem (stk stk_split stk_join stk_word stk_addr)

section L673

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **`<&[T] as IntoIterator>::into_iter(out, p, len)`** (673): the slice iterator `(p, p + len)`. -/
theorem f673_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out p len : UInt32) (ob : List UInt8)
    (hob : ob.length = 8) (hout : out.toNat + 8 ≤ 2 ^ 32) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f673 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 p, .i32 len]⌝ ∗ n ↦[wms][ out.toNat ] ob))
        (fun _ => 8 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[i32][ out.toNat ] p ∗ n ↦[i32][ out.toNat + 4 ] (p + len))) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho⟩
  subst hargs
  have ho4 : (ob.take 4).length = 4 := by simp; omega
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  simp only [f673]
  repeat mstep
  mstep [O4]
  repeat mstep
  mstep [O0]
  mcredits R
  iframe Hc O0 O4

end L673

/-! ## The byte classes -/

/-- `accountIdFormat`'s first test: `a..z` or `0..9`. -/
def alnum (b : UInt8) : Bool := (97 ≤ b.toNat && b.toNat ≤ 122) || (48 ≤ b.toNat && b.toNat ≤ 57)

/-- `accountIdFormat`'s second test: `-`, `_` or `.`. -/
def sepB (b : UInt8) : Bool := b.toNat == 45 || b.toNat == 95 || b.toNat == 46

theorem format_cons (pr : Bool) (b : UInt8) (rest : List UInt8) :
    accountIdFormat pr (b :: rest) =
      if alnum b then accountIdFormat false rest
      else if sepB b && !pr then accountIdFormat true rest else false := by
  simp only [accountIdFormat, alnum, sepB]; rfl

theorem restore16 {GF : BundledGFunctors} [WasmGS NearState GF] (n : Nat) (sp p q : UInt32) (hsp : 16 ≤ sp.toNat) :
    stk n (sp.toNat - 16) 8 ∗ n ↦[i32][ (sp - 16 + 8).toNat ] p ∗ n ↦[i32][ (sp - 16 + 8).toNat + 4 ] q ⊢
      stk (GF := GF) n (sp.toNat - 16) 16 := by
  have hlt := sp.toNat_lt
  have h8 : (sp - 16 + 8).toNat = sp.toNat - 16 + 8 := by
    rw [UInt32.toNat_add, UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le] <;> omega
  rw [h8]
  iintro ⟨H8, I0, I4⟩
  ihave I0 := stk_word n _ p $$ I0
  ihave I4 := stk_word n _ q $$ I4
  ihave I := stk_join n (sp.toNat - 16 + 8) 4 4 $$ [I0 I4]
  · iframe I0 I4
  iapply stk_join n (sp.toNat - 16) 8 8
  iframe H8 I

/-- 554's four byte tests: `a..z`, `0..9`, `-`/`.`, `_`. -/
def t1 (b : UInt8) : UInt32 := Numeric.bool (Numeric.irelop32 IRelOp.lt_u (b.toUInt32 + 4294967199 &&& 255) 26)
def t2 (b : UInt8) : UInt32 := Numeric.bool (Numeric.irelop32 IRelOp.lt_u (b.toUInt32 + 4294967248 &&& 255) 10)
def t3 (b : UInt8) : UInt32 := Numeric.bool (Numeric.irelop32 IRelOp.lt_u (b.toUInt32 + 4294967251) 2)
def t4 (b : UInt8) : UInt32 := Numeric.bool (Numeric.irelop32 IRelOp.eq b.toUInt32 95)

set_option maxRecDepth 100000 in
/-- **The five ways through 554's byte tests**, with `accountIdFormat`'s class of the byte. -/
theorem byte_cases (b : UInt8) :
    (t1 b ≠ 0 ∧ alnum b = true) ∨
    (t1 b = 0 ∧ t2 b ≠ 0 ∧ alnum b = true) ∨
    (t1 b = 0 ∧ t2 b = 0 ∧ t3 b ≠ 0 ∧ alnum b = false ∧ sepB b = true) ∨
    (t1 b = 0 ∧ t2 b = 0 ∧ t3 b = 0 ∧ t4 b ≠ 0 ∧ alnum b = false ∧ sepB b = true) ∨
    (t1 b = 0 ∧ t2 b = 0 ∧ t3 b = 0 ∧ t4 b = 0 ∧ alnum b = false ∧ sepB b = false) := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option hygiene false in
/-- A `br_if` taken, inside a sequence, out of the enclosing block. -/
local macro "brt " h:ident : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr; ipureintro; exact ⟨rfl, by simpa only [t1, t2, t3, t4] using $h⟩
  clear $h; mctrl_norm; mpay))

set_option hygiene false in
/-- A `br_if` not taken, inside a sequence. -/
local macro "brn " h:ident : tactic => `(tactic| (
  iapply mwpi_cons; iapply mwpi_br_if_not'; isplitl [Hc]; iexact Hc; isplitr; ipureintro;
  exact ⟨rfl, by omega, by simpa only [t1, t2, t3, t4] using $h⟩; inext; iintro Hc; clear $h; mctrl_norm))

/-- The cost of `is_valid_account_id` on `len` bytes, activation excluded. -/
def cost554 (len : Nat) : Nat := 100 + 60 * len

section L554

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- 554's frame: `(cur, prev, sp', r, end, prev', b)`. -/
def fr554 (inst : Nat) (mi : ModuleInst) (cur prev sp r e prev' b : UInt32) : Frame :=
  ⟨#[.i32 cur, .i32 prev, .i32 sp, .i32 r, .i32 e, .i32 prev', .i32 b], inst, mi⟩

/-- The loop's invariant: `k` bytes read, the class of the last (`pr`: a separator, or the start)
in the frame, and the rest of the format check the same as the whole. -/
def inv554 (n inst : Nat) (mi : ModuleInst) (Cg c₀ W E R : Nat) (p sp : UInt32) (bs : List UInt8)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (pr : Bool) (r x y : UInt32), ⌜X = [] ∧
      g = fr554 inst mi (p + UInt32.ofNat k) (if pr then 1 else 0) sp r (p + UInt32.ofNat bs.length) x y ∧
      k ≤ bs.length ∧ accountIdFormat true bs = accountIdFormat pr (bs.drop k)⌝ ∗
    credits Cg (W * (bs.length - k) * c₀ + E * c₀ + R) ∗ n ↦[wms][ p.toNat ] bs ∗ P)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`is_valid_account_id(p, len)`** (554) on `bs` at `p`: `1` exactly when
`validAccountIdBytes bs`. -/
theorem f554_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (n g : Nat)
    (hn : mi.memAddrs[0]? = some n) (hg : mi.globalAddrs[0]? = some g) (a673 : Nat)
    (ha673 : mi.funcAddrs[673]? = some a673) (hd : d + 1 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp p len : UInt32) (bs : List UInt8) (hbs : bs.length = len.toNat)
    (hp : p.toNat + len.toNat ≤ 2 ^ 32) (hsp : 16 ≤ sp.toNat) :
    a673 ↪[wf] FuncInst.wasm types[31]! inst f673 ∗ inst ↪[inst] mi ⊢
      MFunSpec (GF := GF) cfg lim d type inst mi f554 Cg
        (fun args => iprop(⌜args = [.i32 p, .i32 len]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          stk n (sp.toNat - 16) 16 ∗ n ↦[wms][ p.toNat ] bs))
        (fun _ => cost554 len.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = [.i32 (if validAccountIdBytes bs then 1 else 0)]⌝ ∗
          g ↦[wg] ⟨gt, .i32 sp⟩ ∗ stk n (sp.toNat - 16) 16 ∗ n ↦[wms][ p.toNat ] bs)) := by
  iintro ⟨#F673, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Hg, Hs, Hb⟩
  subst hargs
  have t31 : types[31]!.params.length = 3 := by rfl
  have hlt := sp.toNat_lt
  have h16 : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le] <;> simp [UInt32.le_iff_toNat_le]; omega
  simp only [f554, cost554]
  by_cases hl : 2 ≤ len.toNat ∧ len.toNat ≤ 64
  · icases stk_split n (sp.toNat - 16) 8 8 $$ Hs with ⟨Hs8, Hs⟩
    iunfold stk at Hs
    icases Hs with ⟨%ob, %hob, Hs⟩
    ihave Hs := AllocNewCell.memBytes_addr (show sp.toNat - 16 + 8 = (sp - 16 + 8).toNat by rw [UInt32.toNat_add, h16]; simp; omega) $$ Hs
    rw [show (100 + 60 * len.toNat) * cfg.regularOpCost + R = 70 * cfg.regularOpCost + ((60 * bs.length + 30) * cfg.regularOpCost + R) by
      rw [hbs, Nat.add_mul, Nat.add_mul]; omega]
    mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + 4294967294) 62) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]; omega
    generalize hv : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + 4294967294) 62) = v at hc ⊢
    subst hc
    clear hv
    iapply mwpi_cons
    iapply mwpi_br_if_not'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨rfl, by omega, rfl⟩
    inext
    iintro Hc
    mctrl_norm
    mstep; mstep; mstep; mstep; mstep
    mcall (f673_spec cfg (lim := lim) (d + 1) types[31]! (by rfl) inst mi n hn Cg (sp - 16 + 8) p len ob hob
      (by rw [UInt32.toNat_add, h16]; simp; omega)) using [Hs]
    · iframe Hs
    icases HQ with ⟨%hrs, I0, I4⟩
    subst hrs
    mstep
    mstep [I4] with (rw [UInt32.toNat_add, h16]; simp; omega)
    mstep; mstep
    mstep [I0] with (rw [UInt32.toNat_add, h16]; simp; omega)
    mstep; mstep; mstep
    have e1 : (60 * bs.length + 30) * cfg.regularOpCost = 60 * bs.length * cfg.regularOpCost + 30 * cfg.regularOpCost :=
      Nat.add_mul _ _ _
    iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := 60 * (bs.length - 0) * cfg.regularOpCost + 30 * cfg.regularOpCost + R)
      (I := inv554 n inst mi Cg cfg.regularOpCost 60 30 R p (sp - 16) bs
        iprop(g ↦[wg] ⟨gt, .i32 (sp - 16)⟩ ∗ stk n (sp.toNat - 16) 8 ∗ n ↦[i32][ (sp - 16 + 8).toNat ] p ∗
          n ↦[i32][ (sp - 16 + 8).toNat + 4 ] (p + len))) _ _ rfl
    isplitr
    · imodintro
      iintro %X %l HI
      iunfold inv554 at HI
      icases HI with ⟨%k, %pr, %r, %x, %y, %⟨hX, hfr, hk, hfmt⟩, Hc, Hb, HP⟩
      subst hX
      rw [hfr]
      simp only [fr554]
      icases HP with ⟨Hg, Hs8, I0, I4⟩
      have hcne : ∀ k1 k2 : Nat, k1 ≤ bs.length → k2 ≤ bs.length → (p + UInt32.ofNat k1 = p + UInt32.ofNat k2 ↔ k1 = k2) := by
        intro k1 k2 h1 h2
        constructor
        · intro h; have := congrArg UInt32.toNat h; simp [UInt32.toNat_add] at this; omega
        · intro h; rw [h]
      by_cases hkl : k = bs.length
      · subst hkl
        mstep; mstep; mstep; mstep; mstep; mstep
        iapply mwpi_cons
        iapply mwpi_br_if_not'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨rfl, by omega, by simp [Numeric.bool, Numeric.irelop32]⟩
        inext
        iintro Hc
        mctrl_norm
        mstep; mstep; mstep; mstep; mstep
        simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero]
        mpay
        mstep; mstep; mstep; mstep [Hg]; mstep; mstep; mstep
        rw [show sp - 16 + 16 = sp by simp]
        isplitl [Hc]
        · iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        ihave Hs := restore16 n sp p (p + len) hsp $$ [Hs8 I0 I4]
        · iframe Hs8 I0 I4
        iframe Hg Hs Hb
        ipureintro
        have hv : validAccountIdBytes bs = !pr := by
          rw [List.drop_length] at hfmt
          simp only [validAccountIdBytes, hfmt, accountIdFormat]
          simp [hbs, hl.1, hl.2]
        rw [hv]
        cases pr <;> simp [htype]
      · have hkl' : k < bs.length := by omega
        rw [show 60 * (bs.length - k) * cfg.regularOpCost + 30 * cfg.regularOpCost + R =
          60 * cfg.regularOpCost + (60 * (bs.length - (k + 1)) * cfg.regularOpCost + 30 * cfg.regularOpCost + R) by
            rw [show 60 * (bs.length - k) = 60 + 60 * (bs.length - (k + 1)) by omega, Nat.add_mul]; omega]
        generalize hZ : 60 * (bs.length - (k + 1)) * cfg.regularOpCost = Z
        have hne : p + UInt32.ofNat bs.length ≠ p + UInt32.ofNat k := fun h => hkl ((hcne _ _ le_rfl hk).mp h).symm
        mstep; mstep; mstep; mstep; mstep; mstep
        iapply mwpi_cons
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, by simp [Numeric.bool, Numeric.irelop32, hne]⟩
        mctrl_norm
        mpay
        ihave Hb := MemCpy.memBytes_pick n p.toNat k bs hkl' $$ Hb
        icases Hb with ⟨B1, Bk, B2⟩
        mstep; mstep; mstep; mstep; mstep; mstep
        mstep [Bk] with (simp [UInt32.toNat_add]; omega)
        simp only [SerdeKey.ld8, SerdeKey.load8]
        mstep; mstep; mstep; mstep; mstep; mstep; mstep
        obtain ⟨b, hbk⟩ : ∃ b, bs[k] = b := ⟨_, rfl⟩
        rw [hbk]
        have hdrop : bs.drop k = b :: bs.drop (k + 1) := by rw [List.drop_eq_getElem_cons hkl', hbk]
        rw [hdrop, format_cons] at hfmt
        have es : List.take k bs ++ b :: List.drop (k + 1) bs = bs := by rw [← hbk]; simp
        have hcur : p + UInt32.ofNat k + 1 = p + UInt32.ofNat (k + 1) := by
          rw [UInt32.add_assoc, SerdeRead.ofNat_succ k (by omega)]
        rcases byte_cases b with ⟨h1, ha⟩ | ⟨h1, h2, ha⟩ | ⟨h1, h2, h3, ha, hs⟩ | ⟨h1, h2, h3, h4, ha, hs⟩ |
            ⟨h1, h2, h3, h4, ha, hs⟩
        · rw [ha, if_pos rfl] at hfmt
          brt h1
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          iapply mwpi_br_if_taken'
          isplitr
          · ipureintro; exact ⟨rfl, by cases pr <;> simp [Numeric.bool, Numeric.irelop32]⟩
          simp only [Post.mloop, List.reverse_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iunfold inv554
          iexists k + 1
          iexists false
          iexists 0
          iexists (if pr = true then 1 else 0)
          iexists b.toUInt32
          ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) b (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          iframe Hb Hg Hs8 I0 I4
          isplitr
          · ipureintro
            refine ⟨rfl, ?_, by omega, hfmt⟩
            simp [fr554, hcur]
          rw [← hZ]
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        · -- 0..9
          rw [ha, if_pos rfl] at hfmt
          replace h2 : Nonempty _ := ⟨h2⟩
          (try replace h3 : Nonempty _ := ⟨h3⟩)
          (try replace h4 : Nonempty _ := ⟨h4⟩)
          brn h1
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          obtain ⟨h2⟩ := h2
          brt h2
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          iapply mwpi_br_if_taken'
          isplitr
          · ipureintro; exact ⟨rfl, by cases pr <;> simp [Numeric.bool, Numeric.irelop32]⟩
          simp only [Post.mloop, List.reverse_nil]
          iapply pure_pay_intro'
          isplitl [Hc]
          · iexact Hc
          isplitr
          · ipureintro; exact ⟨by simp, by omega⟩
          inext
          iintro Hc
          iunfold inv554
          iexists k + 1
          iexists false
          iexists 0
          iexists (if pr = true then 1 else 0)
          iexists b.toUInt32
          ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) b (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          iframe Hb Hg Hs8 I0 I4
          isplitr
          · ipureintro
            refine ⟨rfl, ?_, by omega, hfmt⟩
            simp [fr554, hcur]
          rw [← hZ]
          iapply BorrowMut.credits_le
          iframe Hc
          ipureintro; omega
        · -- - or .
          rw [ha, if_neg (by simp), hs] at hfmt
          replace h2 : Nonempty _ := ⟨h2⟩
          (try replace h3 : Nonempty _ := ⟨h3⟩)
          (try replace h4 : Nonempty _ := ⟨h4⟩)
          brn h1
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          obtain ⟨h2⟩ := h2
          brn h2
          mstep; mstep; mstep; mstep; mstep; mstep; mstep
          obtain ⟨h3⟩ := h3
          brt h3
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) b (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          cases pr
          · simp only [Bool.not_false, Bool.and_self, if_true] at hfmt
            iapply mwpi_br_if_taken'
            isplitr
            · ipureintro; exact ⟨rfl, by simp [Numeric.bool, Numeric.irelop32]⟩
            simp only [Post.mloop, List.reverse_nil]
            iapply pure_pay_intro'
            isplitl [Hc]
            · iexact Hc
            isplitr
            · ipureintro; exact ⟨by simp, by omega⟩
            inext
            iintro Hc
            iunfold inv554
            iexists k + 1
            iexists true
            iexists 0
            iexists 0
            iexists b.toUInt32
            iframe Hb Hg Hs8 I0 I4
            isplitr
            · ipureintro
              refine ⟨rfl, ?_, by omega, hfmt⟩
              simp [fr554, hcur]
            rw [← hZ]
            iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false] at hfmt
            iapply mwpi_br_if_not'
            isplitl [Hc]
            · iexact Hc
            isplitr
            · ipureintro; exact ⟨rfl, by omega, by simp [Numeric.bool, Numeric.irelop32]⟩
            inext
            iintro Hc
            simp only [Post.mloop]
            mpay
            mctrl_norm
            mpay
            mstep; mstep; mstep; mstep [Hg]; mstep; mstep; mstep
            rw [show sp - 16 + 16 = sp by simp]
            isplitl [Hc]
            · iapply BorrowMut.credits_le
              iframe Hc
              ipureintro; omega
            ihave Hs := restore16 n sp p (p + len) hsp $$ [Hs8 I0 I4]
            · iframe Hs8 I0 I4
            iframe Hg Hs Hb
            ipureintro
            have hv : validAccountIdBytes bs = false := by simp [validAccountIdBytes, hfmt]
            rw [hv]; simp [htype]
        · -- _
          rw [ha, if_neg (by simp), hs] at hfmt
          replace h2 : Nonempty _ := ⟨h2⟩
          (try replace h3 : Nonempty _ := ⟨h3⟩)
          (try replace h4 : Nonempty _ := ⟨h4⟩)
          brn h1
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          obtain ⟨h2⟩ := h2
          brn h2
          mstep; mstep; mstep; mstep; mstep; mstep; mstep
          obtain ⟨h3⟩ := h3
          brn h3
          mstep; mstep; mstep
          obtain ⟨h4⟩ := h4
          brt h4
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) b (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          cases pr
          · simp only [Bool.not_false, Bool.and_self, if_true] at hfmt
            iapply mwpi_br_if_taken'
            isplitr
            · ipureintro; exact ⟨rfl, by simp [Numeric.bool, Numeric.irelop32]⟩
            simp only [Post.mloop, List.reverse_nil]
            iapply pure_pay_intro'
            isplitl [Hc]
            · iexact Hc
            isplitr
            · ipureintro; exact ⟨by simp, by omega⟩
            inext
            iintro Hc
            iunfold inv554
            iexists k + 1
            iexists true
            iexists 0
            iexists 0
            iexists b.toUInt32
            iframe Hb Hg Hs8 I0 I4
            isplitr
            · ipureintro
              refine ⟨rfl, ?_, by omega, hfmt⟩
              simp [fr554, hcur]
            rw [← hZ]
            iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          · simp only [Bool.not_true, Bool.and_false, Bool.false_eq_true, if_false] at hfmt
            iapply mwpi_br_if_not'
            isplitl [Hc]
            · iexact Hc
            isplitr
            · ipureintro; exact ⟨rfl, by omega, by simp [Numeric.bool, Numeric.irelop32]⟩
            inext
            iintro Hc
            simp only [Post.mloop]
            mpay
            mctrl_norm
            mpay
            mstep; mstep; mstep; mstep [Hg]; mstep; mstep; mstep
            rw [show sp - 16 + 16 = sp by simp]
            isplitl [Hc]
            · iapply BorrowMut.credits_le
              iframe Hc
              ipureintro; omega
            ihave Hs := restore16 n sp p (p + len) hsp $$ [Hs8 I0 I4]
            · iframe Hs8 I0 I4
            iframe Hg Hs Hb
            ipureintro
            have hv : validAccountIdBytes bs = false := by simp [validAccountIdBytes, hfmt]
            rw [hv]; simp [htype]
        · -- anything else
          rw [ha, if_neg (by simp), hs] at hfmt
          simp only [Bool.false_and, Bool.false_eq_true, if_false] at hfmt
          replace h2 : Nonempty _ := ⟨h2⟩
          (try replace h3 : Nonempty _ := ⟨h3⟩)
          (try replace h4 : Nonempty _ := ⟨h4⟩)
          brn h1
          mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
          obtain ⟨h2⟩ := h2
          brn h2
          mstep; mstep; mstep; mstep; mstep; mstep; mstep
          obtain ⟨h3⟩ := h3
          brn h3
          mstep; mstep; mstep
          obtain ⟨h4⟩ := h4
          brn h4
          mstep; mstep; mstep
          ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) b (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
          · iframe B1 Bk B2
          rw [es]
          simp only [Post.mloop, Post.mseq_br, List.append_nil, Post.mblock_br_zero, Post.mblock_br_succ]
          mpay
          mstep; mstep; mstep; mstep [Hg]; mstep; mstep; mstep
          rw [show sp - 16 + 16 = sp by simp]
          isplitl [Hc]
          · iapply BorrowMut.credits_le
            iframe Hc
            ipureintro; omega
          ihave Hs := restore16 n sp p (p + len) hsp $$ [Hs8 I0 I4]
          · iframe Hs8 I0 I4
          iframe Hg Hs Hb
          ipureintro
          have hv : validAccountIdBytes bs = false := by simp [validAccountIdBytes, hfmt]
          rw [hv]; simp [htype]
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; rw [Nat.sub_zero]; omega
    inext
    iintro Hc
    iunfold inv554
    iexists 0
    iexists true
    iexists 0
    iexists 0
    iexists 0
    iframe Hc Hb Hg Hs8 I0 I4
    ipureintro
    refine ⟨rfl, ?_, by omega, by simp⟩
    simp [fr554, hbs]
  · rw [show (100 + 60 * len.toNat) * cfg.regularOpCost + R = 100 * cfg.regularOpCost + (60 * len.toNat * cfg.regularOpCost + R) by
      rw [Nat.add_mul]; omega]
    generalize hM : 60 * len.toNat * cfg.regularOpCost = M
    mstep [Hg]; mstep; mstep; mstep; mstep [Hg]
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + 4294967294) 62) ≠ 0 := by
      have hl4 := len.toNat_lt
      simp only [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]
      split <;> simp_all; omega
    iapply mwpi_cons; iapply mwpi_br_if_taken'; isplitr; ipureintro; exact ⟨rfl, hc⟩
    clear hc
    mctrl_norm; mpay
    mstep; mstep; mstep; mstep [Hg]; mstep; mstep; mstep
    rw [show sp - 16 + 16 = sp by simp]
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro; omega
    iframe Hg Hs Hb
    ipureintro
    have hv : validAccountIdBytes bs = false := by
      simp only [validAccountIdBytes, hbs]
      simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]
      omega
    rw [hv]; simp [htype]

end L554

end WNear.Binary.AccountIdValid
