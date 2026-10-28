import Bridge.Functions.AccountIdValid
import Bridge.Functions.Utf8

/-!
# `core::str::from_utf8` (927) (M6)

serde_json's `as_str` (648) validates a string's bytes with `core::str::from_utf8`, Rust 1.50's
`run_utf8_validation`:

```wat
;; 927 from_utf8(out, p, len)     out := (0, p, len) | (1, Utf8Error)
len = 0 → Ok
wlim := len ≥ 7 ? len - 7 : 0;  align := ((p + 3) & -4) - p;  i := 0
loop                                              ;; the main loop, i < len
  b := [p + i]
  b < 0x80:
    align = -1 or (align - i) & 3 ≠ 0 → i += 1    ;; not word-aligned
    else
      while i < wlim and ([p+i] | [p+i+4]) & 0x80808080 = 0: i += 8   ;; the word loop
      i ≥ len → (exit)
      while [p + i] (signed) ≥ 0: i += 1; i = len → Ok                ;; the byte loop
  b ≥ 0x80: by the width table at 1071704 (2, 3 or 4, else 0): the next bytes checked, i past
    the character; any failure → Err
  i < len → loop
Ok
```

* `res927`: the result at `out`.
* `inv927` (the main loop), `invA` (the word loop, `S = 8`, and the byte loop, `S = 1`): the
  position, `utf8Ok bs = utf8Ok (bs.drop i)`, and the credits. The main loop holds `100` per byte
  left and `70` more. The inner loops are entered at a position `i` whose byte is ASCII and has
  not been read: they hold `100` per byte after the current one, and `F` (`124` for the word loop,
  `104` for the byte loop) at `i`, `O` (`210`, `186`) past it. That pays every exit back to the
  main loop, which happens only past `i`.
* `word_ascii`, `window_ascii`: a word test that passes means eight ASCII bytes (bits 7, 15, 23,
  31 of each word, through `Nat.testBit`).
* `f927_spec_ascii`: on ASCII bytes, `Ok(&str)` at `cost927 len = 100 + 100 · len`.

The non-ASCII branch (the general validator, against `Utf8.utf8Ok`) is not proved yet; the
proof shape (`inv927` and the result `res927`) is already the general one.
-/

namespace WNear.Binary.FromUtf8

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

section Flex

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame}
  {Φ : Post NearState GF} {Cg K : Nat}

/-- `select` on the stack `[a, b, c]`: `a` when `c ≠ 0`, else `b`. -/
theorem mwpi_select' {t : Option (List ValType)} {a b : Value} {c : UInt32} :
    credits Cg K ∗ ⌜cfg.regularOpCost ≤ K⌝ ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ Φ.normal [if c = 0 then b else a] f)
      ⊢ mwpi cfg lim d f [a, b, .i32 c] [.select t] Φ := by
  iintro ⟨Hc, %hK, H⟩
  by_cases hc : c = 0
  · subst hc
    have h := mwpi_select_false (vs := []) (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f)
      (Cg := Cg) (R := K - cfg.regularOpCost) t a b
    simp only [List.nil_append] at h
    iapply h
    rw [Nat.add_sub_cancel' hK]
    iframe Hc
    simp only [if_pos]
    iexact H
  · have h := mwpi_select_true (vs := []) (Φ := Φ) (cfg := cfg) (lim := lim) (d := d) (f := f)
      (Cg := Cg) (R := K - cfg.regularOpCost) t a b c hc
    simp only [List.nil_append] at h
    iapply h
    rw [Nat.add_sub_cancel' hK]
    iframe Hc
    simp only [hc, if_false]
    iexact H

end Flex

set_option maxRecDepth 100000 in
/-- 927's word limit: `len - 7`, saturating at 0. -/
theorem wlim_eq (len : UInt32) :
    (if Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + 4294967289) len) = 0 then .i32 (len + 4294967289)
      else Value.i32 0) = .i32 (UInt32.ofNat (len.toNat - 7)) := by
  have hl := len.toNat_lt
  by_cases h : 7 ≤ len.toNat
  · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + 4294967289) len) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]; omega
    have h2 : len + 4294967289 = UInt32.ofNat (len.toNat - 7) := by
      apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add]; omega
    rw [this, if_pos rfl, h2]
  · have : Numeric.bool (Numeric.irelop32 IRelOp.gt_u (len + 4294967289) len) = 1 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, UInt32.toNat_add]; omega
    rw [this, if_neg (by decide), show len.toNat - 7 = 0 by omega]
    rfl

theorem ltu_ofNat (j : Nat) (len : UInt32) (h : j < 2 ^ 32) :
    Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat j) len) = if j < len.toNat then 1 else 0 := by
  have e : (UInt32.ofNat j).toNat = j := by simp; omega
  simp only [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt, e]
  by_cases hj : j < len.toNat <;> simp [hj]

/-- The sign-extended byte (`(b << 24) >>s 24`). -/
def sb (b : UInt8) : UInt32 := Numeric.intToUInt32 ((b.toUInt32 <<< ((24 : UInt32) % 32)).toIntS >>> ((24 : UInt32) % 32).toNat)

set_option maxRecDepth 100000 in
theorem sb_neg (b : UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.lt_s (sb b) 0) = if b.toNat < 128 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- The byte as `i32.load8_s` gives it. -/
def sx (b : UInt8) : UInt32 := UInt32.ofNat (Numeric.signExtend 32 8 b.toNat)

set_option maxRecDepth 100000 in
theorem load8s (b : UInt8) :
    loadValue NumType.i32 (some { bits := 8, signed := true }) (Memory.decodeLE [b]) = .i32 (sx b) := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

set_option maxRecDepth 100000 in
theorem sx_neg (b : UInt8) :
    Numeric.bool (Numeric.irelop32 IRelOp.lt_s (sx b) 0) = if b.toNat < 128 then 0 else 1 := by
  revert b; exact SerdeRead.uint8_forall (by decide +kernel)

/-- Skipping `m` ASCII bytes keeps the validity. -/
theorem utf8Ok_skip (bs : List UInt8) (j m : Nat) (h : ∀ b ∈ (bs.drop j).take m, b.toNat < 128) :
    Utf8.utf8Ok (bs.drop j) = Utf8.utf8Ok (bs.drop (j + m)) := by
  induction m generalizing j with
  | zero => rfl
  | succ m ih =>
    rcases hj : bs.drop j with _ | ⟨b, rest⟩
    · have : bs.drop (j + (m + 1)) = [] := by
        rw [← List.drop_drop, hj]; simp
      rw [this]
    · have hb : b.toNat < 128 := h b (by rw [hj]; simp)
      have hd : bs.drop (j + 1) = rest := by rw [← List.drop_drop, hj]; simp
      rw [Utf8.utf8Ok_ascii b rest hb, ← hd, ih (j + 1) (fun x hx => h x (by
        rw [hj]; rw [hd] at hx; simp only [List.take_succ_cons, List.mem_cons]; exact Or.inr hx))]
      congr 2; omega

theorem bit_lt (v : Nat) (k : Nat) (h : v.testBit k = false) : v / 2 ^ k % 2 = 0 := by
  rw [Nat.testBit_eq_decide_div_mod_eq] at h; simp at h; omega

/-- 927's word test: two words with no bit of `0x80808080` set are eight ASCII bytes. -/
theorem word_ascii (a0 a1 a2 a3 b0 b1 b2 b3 : UInt8)
    (h : (UInt32.ofNat (Memory.decodeLE [b0, b1, b2, b3]) ||| UInt32.ofNat (Memory.decodeLE [a0, a1, a2, a3])) &&&
      2155905152 = 0) :
    a0.toNat < 128 ∧ a1.toNat < 128 ∧ a2.toNat < 128 ∧ a3.toNat < 128 ∧
      b0.toNat < 128 ∧ b1.toNat < 128 ∧ b2.toNat < 128 ∧ b3.toNat < 128 := by
  have := a0.toNat_lt; have := a1.toNat_lt; have := a2.toNat_lt; have := a3.toNat_lt
  have := b0.toNat_lt; have := b1.toNat_lt; have := b2.toNat_lt; have := b3.toNat_lt
  have hv0 : Memory.decodeLE [a0, a1, a2, a3] = a0.toNat + 256 * (a1.toNat + 256 * (a2.toNat + 256 * a3.toNat)) := by
    simp [Memory.decodeLE]; omega
  have hv1 : Memory.decodeLE [b0, b1, b2, b3] = b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * b3.toNat)) := by
    simp [Memory.decodeLE]; omega
  generalize Memory.decodeLE [a0, a1, a2, a3] = v0 at h hv0
  generalize Memory.decodeLE [b0, b1, b2, b3] = v1 at h hv1
  have h' := congrArg UInt32.toNat h
  have e0 : (UInt32.ofNat v0).toNat = v0 := by simp; omega
  have e1 : (UInt32.ofNat v1).toNat = v1 := by simp; omega
  simp only [UInt32.toNat_and, UInt32.toNat_or, e0, e1] at h'
  norm_num at h'
  have tb : ∀ k, k = 7 ∨ k = 15 ∨ k = 23 ∨ k = 31 → v1.testBit k = false ∧ v0.testBit k = false := by
    intro k hk
    have e := congrArg (fun x => x.testBit k) h'
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at e
    have hm : (2155905152 : Nat).testBit k = true := by rcases hk with rfl | rfl | rfl | rfl <;> decide
    rw [hm, Bool.and_true, Bool.or_eq_false_iff] at e
    exact e
  have e7 := tb 7 (by simp); have e15 := tb 15 (by simp); have e23 := tb 23 (by simp); have e31 := tb 31 (by simp)
  have c1 := bit_lt _ _ e7.1; have c2 := bit_lt _ _ e7.2
  have c3 := bit_lt _ _ e15.1; have c4 := bit_lt _ _ e15.2
  have c5 := bit_lt _ _ e23.1; have c6 := bit_lt _ _ e23.2
  have c7 := bit_lt _ _ e31.1; have c8 := bit_lt _ _ e31.2
  subst hv0 hv1
  norm_num at c1 c2 c3 c4 c5 c6 c7 c8
  omega

/-- `word_ascii` on two 4-byte windows. -/
theorem window_ascii (wa wb : List UInt8) (ha : wa.length = 4) (hb : wb.length = 4)
    (h : (UInt32.ofNat (Memory.decodeLE wb) ||| UInt32.ofNat (Memory.decodeLE wa)) &&& 2155905152 = 0) :
    ∀ b ∈ wa ++ wb, b.toNat < 128 := by
  rcases wa with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at ha
  rcases wb with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at hb
  have := word_ascii a0 a1 a2 a3 b0 b1 b2 b3 h
  intro b hb'
  simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hb'
  rcases hb' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

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

set_option hygiene false in
/-- Out of the main loop with `Ok` (`hok'` for `j ≥ len` in context): the result `(0, p, len)`. -/
local macro "exit927" : tactic => `(tactic| (
  icases U128From.memBytes_split n out.toNat 4 ob (by omega) $$ Ho with ⟨O0, O4⟩
  icases U128From.memBytes_split n (out.toNat + 4) 4 (ob.drop 4) (by simp; omega) $$ O4 with ⟨O4, O8⟩
  mstep; mstep
  mstep [O4]
  mstep; mstep; mstep; mstep
  mstep [O8] with (simp [UInt32.toNat_add]; omega)
  mstep; mstep
  mstep [O0]
  repeat mstep
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  isplitr
  · ipureintro; trivial
  iframe Hb
  iapply res927_ok n out p len bs (by rw [hok', List.drop_eq_nil_of_le (by omega)]; simp [Utf8.utf8Ok])
  rw [show out.toNat + 4 + 4 = out.toNat + 8 by omega]
  iframe O0 O4 O8))

set_option hygiene false in
/-- The main loop's test `j < len` at its end (`hok'` for `j` in context): back to the invariant
at `j`, or out of the loop with `Ok` when `j = len`. -/
local macro "tail927 " j:term:max : tactic => `(tactic| (
  by_cases hj : $j < bs.length
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat $j) len) ≠ 0 := by
      rw [ltu_ofNat _ _ (by omega)]; simp; omega
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, hc⟩
    (try simp only [Post.mloop]); (try dsimp only); (try simp only [List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil, List.drop_length])
    iapply pure_pay_intro'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨by simp, by omega⟩
    inext
    iintro Hc
    iapply inv927_intro n inst mi Cg cfg.regularOpCost 100 70 R out p len _ a bs _ $j _ _ _ _ _ hj hok'
    iframe Hb Ho
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat $j) len) = 0 := by
      rw [ltu_ofNat _ _ (by omega)]; simp; omega
    brn hc
    mstep
    (try simp only [Post.mloop]); (try dsimp only); (try simp only [List.append_nil, List.nil_append])
    repeat mpay
    exit927))

set_option hygiene false in
/-- The byte loop at `k` on an ASCII byte `x` (`hxa`, `hokk'` for `k + 1`, `hZ'` in context): on to
`k + 1`, or out with `Ok` at the end. -/
local macro "bascii10" : tactic => `(tactic| (
  mstep; mstep
  have hn0 := sx_neg x
  rw [if_pos hxa] at hn0
  generalize sx x = sv at hn0 ⊢
  brn hn0
  clear hn0
  mstep; mstep; mstep; mstep; mstep; mstep
  rw [SerdeRead.ofNat_succ k (by omega)]
  by_cases hk1 : k + 1 < bs.length
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne len (UInt32.ofNat (k + 1))) ≠ 0 := by
      have hu : (UInt32.ofNat (k + 1)).toNat = k + 1 := by simp; omega
      generalize UInt32.ofNat (k + 1) = u at hu ⊢
      have : len ≠ u := fun e => by subst e; omega
      simp [Numeric.bool, Numeric.irelop32, this]
    iapply mwpi_cons
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, hc⟩
    mctrl_norm
    simp only [Post.mloop, List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil]
    iapply pure_pay_intro'
    isplitl [Hc]
    · iexact Hc
    isplitr
    · ipureintro; exact ⟨by simp, by omega⟩
    inext
    iintro Hc
    iapply invA_intro n inst mi Cg cfg.regularOpCost 104 186 R 1 out p len _ a s l8 l9 l10 bs i _ (k + 1) _
      (by omega) (by omega) hokk'
    iframe Hb Ho
    iapply BorrowMut.credits_le
    iframe Hc
    ipureintro
    rw [if_neg (by omega)]
    rw [show bs.length - (k + 1) = bs.length - (k + 1 + 1) + 1 by omega, Nat.mul_add, Nat.add_mul] at hZ'
    omega
  next =>
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.ne len (UInt32.ofNat (k + 1))) = 0 := by
      have hu : (UInt32.ofNat (k + 1)).toNat = k + 1 := by simp; omega
      generalize UInt32.ofNat (k + 1) = u at hu ⊢
      have : len = u := by apply UInt32.toNat_inj.mp; omega
      simp [Numeric.bool, Numeric.irelop32, this]
    brn hc
    mstep
    simp only [Post.mloop]
    mctrl_norm
    repeat mpay
    have hok' := hokk'
    exit927))

set_option hygiene false in
/-- The byte loop's body (`invA … 1`, entered at `i` whose byte `b` is ASCII: `hbk`, `hasc`). -/
local macro "body10" : tactic => `(tactic| (
  iintro %X %l HI
  iunfold invA at HI
  icases HI with ⟨%k, %l6', %⟨hX, hfr', hik, hkl, hokk⟩, Hc, Hb, Ho⟩
  subst hX
  rw [hfr']
  simp only [fr927]
  clear hfr'
  have hkb : k < bs.length := by omega
  ihave Hb := MemCpy.memBytes_pick n p.toNat k bs hkb $$ Hb
  icases Hb with ⟨B1, Bk, B2⟩
  obtain ⟨x, hxk⟩ : ∃ x, bs[k] = x := ⟨_, rfl⟩
  rw [hxk]
  have hdk : bs.drop k = x :: bs.drop (k + 1) := by rw [List.drop_eq_getElem_cons hkb, hxk]
  have esk : List.take k bs ++ x :: List.drop (k + 1) bs = bs := by rw [← hxk]; simp
  by_cases hki : k = i
  next =>
    rw [if_pos hki, show 100 * (bs.length - (k + 1)) * cfg.regularOpCost + 104 * cfg.regularOpCost + R =
      104 * cfg.regularOpCost + (100 * (bs.length - (k + 1)) * cfg.regularOpCost + R) by omega]
    generalize hZ' : 100 * (bs.length - (k + 1)) * cfg.regularOpCost = Z'
    mstep; mstep; mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    rw [load8s]
    ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    rw [esk]
    have hxa : x.toNat < 128 := by subst hki; rw [hbk] at hxk; subst hxk; exact hasc
    have hokk' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (k + 1)) := by
      rw [hokk, hdk, Utf8.utf8Ok_ascii x _ hxa]
    bascii10
  next =>
    rw [if_neg hki, show 100 * (bs.length - (k + 1)) * cfg.regularOpCost + 186 * cfg.regularOpCost + R =
      186 * cfg.regularOpCost + (100 * (bs.length - (k + 1)) * cfg.regularOpCost + R) by omega]
    generalize hZ' : 100 * (bs.length - (k + 1)) * cfg.regularOpCost = Z'
    mstep; mstep; mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    rw [load8s]
    ihave Hb := MemCpy.memBytes_unpick n p.toNat k (bs.take k) x (bs.drop (k + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    rw [esk]
    by_cases hxa : x.toNat < 128
    next =>
      have hokk' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (k + 1)) := by
        rw [hokk, hdk, Utf8.utf8Ok_ascii x _ hxa]
      bascii10
    next =>
      mstep; mstep
      have hn1 := sx_neg x
      rw [if_neg hxa] at hn1
      generalize sx x = sv at hn1 ⊢
      iapply mwpi_cons
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, by rw [hn1]; decide⟩
      mctrl_norm
      simp only [Post.mloop]
      mctrl_norm
      repeat mpay
      clear hn1
      have hok' := hokk
      have hZk : 100 * (bs.length - k) * cfg.regularOpCost = 100 * cfg.regularOpCost + Z' := by
        rw [← hZ', show bs.length - k = bs.length - (k + 1) + 1 by omega, Nat.mul_add, Nat.add_mul]; omega
      mstep; mstep; mstep
      by_cases hj : k < bs.length
      next =>
        have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat k) len) ≠ 0 := by
          rw [ltu_ofNat _ _ (by omega)]; simp; omega
        iapply mwpi_br_if_taken'
        isplitr
        · ipureintro; exact ⟨rfl, hc⟩
        dsimp only
        simp only [List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil]
        iapply pure_pay_intro'
        isplitl [Hc]
        · iexact Hc
        isplitr
        · ipureintro; exact ⟨by simp, by omega⟩
        inext
        iintro Hc
        iapply inv927_intro n inst mi Cg cfg.regularOpCost 100 70 R out p len _ a bs _ k _ _ _ _ _ hj hok'
        iframe Hb Ho
        iapply BorrowMut.credits_le
        iframe Hc
        ipureintro; omega
      next => exfalso; omega))

set_option hygiene false in
/-- After the word loop, at `j` (`hok'` for `j`, `hji : i ≤ j`, `j ≤ len`): `j < len` runs the byte
loop from `j`; `j = len` is `Ok`. -/
local macro "bytes10 " j:term:max : tactic => `(tactic| (
    have hg2 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat $j) len) = 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    brn hg2
    clear hg2
    iapply MemCpy.mwpi_loop0 (Cg := Cg)
      (R := 100 * (bs.length - ($j + 1)) * cfg.regularOpCost + (ite ($j = i) 104 186) * cfg.regularOpCost + R)
      (I := invA n inst mi Cg cfg.regularOpCost 104 186 R 1 out p len (UInt32.ofNat (len.toNat - 7)) a s l8 l9 l10
        bs i iprop(n ↦[wms][ out.toNat ] ob)) _ _ rfl
    isplitr
    · imodintro
      body10
    isplitl [Hc]
    · iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      split <;> omega
    inext
    iintro Hc
    iapply invA_intro n inst mi Cg cfg.regularOpCost 104 186 R 1 out p len _ a s l8 l9 l10 bs i _ $j _ hji
      (by omega) hok'
    iframe Hb Ho Hc))

set_option hygiene false in
/-- `after10` where `j < len`. -/
local macro "after10x " j:term:max : tactic => `(tactic| (
  mstep; mstep; mstep
  by_cases hjl : $j < bs.length
  next => bytes10 $j
  next => exfalso; omega))

set_option hygiene false in
local macro "after10 " j:term:max : tactic => `(tactic| (
  mstep; mstep; mstep
  by_cases hjl : $j < bs.length
  next => bytes10 $j
  next =>
    have hg2 : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat $j) len) ≠ 0 := by
      simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
    brt hg2
    clear hg2
    mstep; mstep; mstep
    have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat $j) len) = 0 := by
      rw [ltu_ofNat _ _ (by omega)]; simp; omega
    brn hc
    mstep
    exit927))

set_option hygiene false in
/-- The word loop's body at `j` (`j + 8 ≤ len`), the credits `D · c + (Zj + R)`. -/
local macro "word11" : tactic => `(tactic| (
  ihave Hb := window_split n p.toNat j bs hj8 $$ Hb
  icases Hb with ⟨W0, Wa, Wb, W2⟩
  mstep; mstep; mstep; mstep; mstep; mstep
  mstep [Wb] with (simp [UInt32.toNat_add]; omega)
  mstep
  mstep [Wa] with (simp [UInt32.toNat_add]; omega)
  ihave Hb := window_join n p.toNat j bs hj8 $$ [W0 Wa Wb W2]
  · iframe W0 Wa Wb W2
  mstep; mstep; mstep
  by_cases hm : (UInt32.ofNat (Memory.decodeLE (List.drop 4 (List.take 8 (List.drop j bs)))) |||
      UInt32.ofNat (Memory.decodeLE (List.take 4 (List.take 8 (List.drop j bs))))) &&& 2155905152 = 0
  · have h8 := window_ascii _ _ (by simp; omega) (by simp; omega) hm
    have hok8 : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (j + 8)) := by
      rw [hokj, utf8Ok_skip bs j 8 (by intro b hb; apply h8; rw [List.take_append_drop]; exact hb)]
    clear h8
    generalize (UInt32.ofNat (Memory.decodeLE (List.drop 4 (List.take 8 (List.drop j bs)))) |||
      UInt32.ofNat (Memory.decodeLE (List.take 4 (List.take 8 (List.drop j bs))))) &&& 2155905152 = mv at hm ⊢
    subst hm
    brn rfl
    mstep; mstep; mstep; mstep
    rw [show UInt32.ofNat j + 8 = UInt32.ofNat (j + 8) by
      apply UInt32.toNat_inj.mp; simp [UInt32.toNat_add] <;> omega]
    mstep; mstep
    by_cases hj16 : j + 8 + 8 ≤ bs.length
    · have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (j + 8)) (UInt32.ofNat (len.toNat - 7))) ≠ 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      iapply mwpi_br_if_taken'
      isplitr
      · ipureintro; exact ⟨rfl, hc⟩
      simp only [Post.mloop, List.reverse_nil, List.length_nil, Nat.sub_zero, List.drop_nil]
      iapply pure_pay_intro'
      isplitl [Hc]
      · iexact Hc
      isplitr
      · ipureintro; exact ⟨by simp, by omega⟩
      inext
      iintro Hc
      iapply invA_intro n inst mi Cg cfg.regularOpCost 124 210 R 8 out p len _ a s l8 l9 l10 bs i _ (j + 8) _
        (by omega) hj16 hok8
      iframe Hb Ho
      iapply BorrowMut.credits_le
      iframe Hc
      ipureintro
      rw [if_neg (by omega)]
      omega
    · have hc : Numeric.bool (Numeric.irelop32 IRelOp.lt_u (UInt32.ofNat (j + 8)) (UInt32.ofNat (len.toNat - 7))) = 0 := by
        simp [Numeric.bool, Numeric.irelop32, UInt32.lt_iff_toNat_lt]; omega
      brn hc
      mstep
      simp only [Post.mloop, List.append_nil]
      repeat mpay
      have hok' := hok8
      have hji' : i ≤ j + 8 := by omega
      clear hji
      have hji := hji'
      after10 (j + 8)
  · iapply mwpi_cons
    iapply mwpi_br_if_taken'
    isplitr
    · ipureintro; exact ⟨rfl, hm⟩
    mctrl_norm
    simp only [Post.mloop]
    mctrl_norm
    repeat mpay
    clear hm
    have hok' := hokj
    after10x j))

/-- `from_utf8`'s cost on `len` bytes, activation excluded. -/
def cost927 (len : Nat) : Nat := 100 + 100 * len

section L927

/-- 927's frame: `(out, p, len, i, wlim, align, b, sb, e1, e2, x)`. -/
def fr927 (inst : Nat) (mi : ModuleInst) (out p len i wl a l6 l7 : UInt32) (l8 l9 : UInt64) (l10 : UInt32) :
    Frame :=
  ⟨#[.i32 out, .i32 p, .i32 len, .i32 i, .i32 wl, .i32 a, .i32 l6, .i32 l7, .i64 l8, .i64 l9, .i32 l10], inst, mi⟩

variable {GF : BundledGFunctors} [WasmGS NearState GF] in
/-- The main loop's invariant: at `i < len`, the validity of the rest that of the whole. -/
def inv927 (n inst : Nat) (mi : ModuleInst) (Cg c₀ W E R : Nat) (out p len wl a : UInt32) (bs : List UInt8)
    (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (i : Nat) (l6 l7 : UInt32) (l8 l9 : UInt64) (l10 : UInt32), ⌜X = [] ∧
      g = fr927 inst mi out p len (UInt32.ofNat i) wl a l6 l7 l8 l9 l10 ∧ i < bs.length ∧
      Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop i)⌝ ∗
    credits Cg (W * (bs.length - i) * c₀ + E * c₀ + R) ∗ n ↦[wms][ p.toNat ] bs ∗ P)

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem inv927_intro (n inst : Nat) (mi : ModuleInst) (Cg c₀ W E R : Nat) (out p len wl a : UInt32)
    (bs : List UInt8) (P : IProp GF) (j : Nat) (l6 l7 : UInt32) (l8 l9 : UInt64) (l10 : UInt32)
    (hj : j < bs.length) (hok : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop j)) :
    credits Cg (W * (bs.length - j) * c₀ + E * c₀ + R) ∗ n ↦[wms][ p.toNat ] bs ∗ P ⊢
      inv927 n inst mi Cg c₀ W E R out p len wl a bs P []
        ⟨#[.i32 out, .i32 p, .i32 len, .i32 (UInt32.ofNat j), .i32 wl, .i32 a, .i32 l6, .i32 l7, .i64 l8, .i64 l9,
          .i32 l10], inst, mi⟩ := by
  iintro ⟨Hc, Hb, HP⟩
  iunfold inv927
  iexists j
  iexists l6
  iexists l7
  iexists l8
  iexists l9
  iexists l10
  iframe Hb HP
  iframe Hc
  ipureintro; exact ⟨rfl, rfl, hj, hok⟩

/-- The ASCII loops' invariant (the word loop: `k + 8 ≤ len`, `S = 8`; the byte loop: `k < len`,
`S = 1`), entered at `i`: `100` per byte left after the current one, `F` more at `k = i` (the
byte at `i`, ASCII, not yet read), `O` more after. -/
def invA (n inst : Nat) (mi : ModuleInst) (Cg c₀ F O R S : Nat) (out p len wl a l7 : UInt32) (l8 l9 : UInt64)
    (l10 : UInt32) (bs : List UInt8) (i : Nat) (P : IProp GF) : List Value → Frame → IProp GF := fun X g =>
  iprop(∃ (k : Nat) (l6 : UInt32), ⌜X = [] ∧ g = fr927 inst mi out p len (UInt32.ofNat k) wl a l6 l7 l8 l9 l10 ∧
      i ≤ k ∧ k + S ≤ bs.length ∧ Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop k)⌝ ∗
    credits Cg (100 * (bs.length - (k + 1)) * c₀ + (if k = i then F else O) * c₀ + R) ∗
    n ↦[wms][ p.toNat ] bs ∗ P)

theorem invA_intro (n inst : Nat) (mi : ModuleInst) (Cg c₀ F O R S : Nat) (out p len wl a l7 : UInt32)
    (l8 l9 : UInt64) (l10 : UInt32) (bs : List UInt8) (i : Nat) (P : IProp GF) (k : Nat) (l6 : UInt32)
    (hk : i ≤ k) (hkl : k + S ≤ bs.length) (hok : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop k)) :
    credits Cg (100 * (bs.length - (k + 1)) * c₀ + (if k = i then F else O) * c₀ + R) ∗ n ↦[wms][ p.toNat ] bs ∗ P ⊢
      invA n inst mi Cg c₀ F O R S out p len wl a l7 l8 l9 l10 bs i P []
        ⟨#[.i32 out, .i32 p, .i32 len, .i32 (UInt32.ofNat k), .i32 wl, .i32 a, .i32 l6, .i32 l7, .i64 l8, .i64 l9,
          .i32 l10], inst, mi⟩ := by
  iintro ⟨Hc, Hb, HP⟩
  iunfold invA
  iexists k
  iexists l6
  iframe Hb HP Hc
  ipureintro; exact ⟨rfl, rfl, hk, hkl, hok⟩

/-- The word loop's window: the 8 bytes from `j`, as two words. -/
theorem window_split (n a j : Nat) (bs : List UInt8) (hj : j + 8 ≤ bs.length) :
    memBytes (H := NearState) (GF := GF) n a bs ⊢
      n ↦[wms][ a ] bs.take j ∗ n ↦[wms][ a + j ] ((bs.drop j).take 8).take 4 ∗
        n ↦[wms][ a + j + 4 ] ((bs.drop j).take 8).drop 4 ∗ n ↦[wms][ a + j + 8 ] (bs.drop j).drop 8 := by
  iintro Hb
  icases U128From.memBytes_split (GF := GF) n a j bs (by omega) $$ Hb with ⟨W0, Hd⟩
  icases U128From.memBytes_split (GF := GF) n (a + j) 8 (bs.drop j) (by simp; omega) $$ Hd with ⟨Ww, W2⟩
  icases U128From.memBytes_split (GF := GF) n (a + j) 4 ((bs.drop j).take 8) (by simp; omega) $$ Ww with ⟨Wa, Wb⟩
  iframe W0 Wa Wb W2

theorem window_join (n a j : Nat) (bs : List UInt8) (hj : j + 8 ≤ bs.length) :
    memBytes (H := NearState) (GF := GF) n a (bs.take j) ∗ n ↦[wms][ a + j ] ((bs.drop j).take 8).take 4 ∗
        n ↦[wms][ a + j + 4 ] ((bs.drop j).take 8).drop 4 ∗ n ↦[wms][ a + j + 8 ] (bs.drop j).drop 8 ⊢
      n ↦[wms][ a ] bs := by
  iintro ⟨W0, Wa, Wb, W2⟩
  ihave Ww := U128From.memBytes_join (GF := GF) n (a + j) 4 (((bs.drop j).take 8).take 4) (((bs.drop j).take 8).drop 4) (by simp; omega) $$ [Wa Wb]
  · iframe Wa Wb
  rw [List.take_append_drop]
  ihave Hd := U128From.memBytes_join (GF := GF) n (a + j) 8 ((bs.drop j).take 8) ((bs.drop j).drop 8) (by simp; omega) $$ [Ww W2]
  · iframe Ww W2
  rw [List.take_append_drop]
  ihave Hb := U128From.memBytes_join (GF := GF) n a j (bs.take j) (bs.drop j) (by simp; omega) $$ [W0 Hd]
  · iframe W0 Hd
  rw [List.take_append_drop]
  iexact Hb

/-- `from_utf8`'s result at `out`: `Ok(&str)` (`(0, p, len)`) when `bs` is valid, else `Err` (1 and
the 8 bytes of a `Utf8Error`). -/
def res927 (n : Nat) (out p len : UInt32) (bs : List UInt8) : IProp GF :=
  if Utf8.utf8Ok bs then iprop(n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] len)
  else iprop(∃ eb : List UInt8, ⌜eb.length = 8⌝ ∗ n ↦[i32][ out.toNat ] 1 ∗ n ↦[wms][ out.toNat + 4 ] eb)

theorem res927_ok (n : Nat) (out p len : UInt32) (bs : List UInt8) (hok : Utf8.utf8Ok bs = true) :
    n ↦[i32][ out.toNat ] 0 ∗ n ↦[i32][ out.toNat + 4 ] p ∗ n ↦[i32][ out.toNat + 8 ] len ⊢ res927 (GF := GF) n out p len bs := by
  iintro H
  unfold res927
  rw [if_pos hok]
  iexact H

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`core::str::from_utf8(out, p, len)`** (927) on `bs` at `p`, every byte ASCII: `Ok(&str)`, at
`cost927 len`. -/
theorem f927_spec_ascii (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results = []) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (Cg : Nat) (out p len : UInt32) (ob bs : List UInt8)
    (hob : ob.length = 12) (hout : out.toNat + 12 ≤ 2 ^ 32) (hbs : bs.length = len.toNat)
    (hp : p.toNat + len.toNat ≤ 2 ^ 32)
    (hA : ∀ b ∈ bs, b.toNat < 128) :
    ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f927 Cg
        (fun args => iprop(⌜args = [.i32 out, .i32 p, .i32 len]⌝ ∗ n ↦[wms][ out.toNat ] ob ∗
          n ↦[wms][ p.toNat ] bs))
        (fun _ => cost927 len.toNat * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ n ↦[wms][ p.toNat ] bs ∗ res927 n out p len bs)) := by
  iapply MFunSpec_intro
  imodintro
  iintro %args %R HP Hc
  icases HP with ⟨%hargs, Ho, Hb⟩
  subst hargs
  simp only [f927, cost927]
  have hlt := len.toNat_lt
  by_cases hl0 : len.toNat = 0
  · have hl : len = 0 := by apply UInt32.toNat_inj.mp; simpa using hl0
    mstep; mstep; mstep
    mstep_taken with simp [hl, Numeric.bool]
    have hok' : Utf8.utf8Ok bs = Utf8.utf8Ok (List.drop 0 bs) := rfl
    exit927
  have hne : len ≠ 0 := fun e => by simp [e] at hl0
  rw [show (100 + 100 * len.toNat) * cfg.regularOpCost + R = 30 * cfg.regularOpCost + (70 * cfg.regularOpCost + 100 * len.toNat * cfg.regularOpCost + R) by rw [Nat.add_mul]; omega]
  generalize hM : 70 * cfg.regularOpCost + 100 * len.toNat * cfg.regularOpCost + R = M
  repeat mstep
  iapply mwpi_cons
  iapply mwpi_select'
  isplitl [Hc]
  · iexact Hc
  isplitr
  · ipureintro; omega
  inext
  iintro Hc
  rw [wlim_eq]
  mctrl_norm
  repeat mstep
  generalize ha : (p + 3 &&& 4294967292) - p = a
  iapply MemCpy.mwpi_loop0 (Cg := Cg) (R := M)
    (I := inv927 n inst mi Cg cfg.regularOpCost 100 70 R out p len (UInt32.ofNat (len.toNat - 7)) a bs
      iprop(n ↦[wms][ out.toNat ] ob)) _ _ rfl
  isplitr
  · imodintro
    iintro %X %l HI
    iunfold inv927 at HI
    icases HI with ⟨%i, %l6, %l7, %l8, %l9, %l10, %⟨hX, hfr, hi, hok⟩, Hc, Hb, Ho⟩
    subst hX
    rw [hfr]
    simp only [fr927]
    rw [show 100 * (bs.length - i) * cfg.regularOpCost + 70 * cfg.regularOpCost + R =
      170 * cfg.regularOpCost + (100 * (bs.length - (i + 1)) * cfg.regularOpCost + R) by
        rw [show 100 * (bs.length - i) = 100 + 100 * (bs.length - (i + 1)) by omega, Nat.add_mul]; omega]
    generalize hZ : 100 * (bs.length - (i + 1)) * cfg.regularOpCost = Z
    ihave Hb := MemCpy.memBytes_pick n p.toNat i bs (by omega) $$ Hb
    icases Hb with ⟨B1, Bk, B2⟩
    mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep; mstep
    mstep; mstep; mstep
    mstep [Bk] with (simp [UInt32.toNat_add]; omega)
    simp only [SerdeKey.load8]
    obtain ⟨b, hbk⟩ : ∃ b, bs[i] = b := ⟨_, rfl⟩
    rw [hbk]
    ihave Hb := MemCpy.memBytes_unpick n p.toNat i (bs.take i) b (bs.drop (i + 1)) (by simp; omega) $$ [B1 Bk B2]
    · iframe B1 Bk B2
    have es : List.take i bs ++ b :: List.drop (i + 1) bs = bs := by rw [← hbk]; simp
    rw [es]
    have hdrop : bs.drop i = b :: bs.drop (i + 1) := by rw [List.drop_eq_getElem_cons hi, hbk]
    mstep; mstep; mstep; mstep; mstep; mstep; mstep
    rw [show Numeric.intToUInt32 ((b.toUInt32 <<< ((24 : UInt32) % 32)).toIntS >>> ((24 : UInt32) % 32).toNat) = sb b from rfl]
    by_cases hasc : b.toNat < 128
    · have hn0 := sb_neg b
      rw [if_pos hasc] at hn0
      generalize sb b = s at hn0 ⊢
      mstep
      brn hn0
      clear hn0
      mstep; mstep; mstep
      have hok' : Utf8.utf8Ok bs = Utf8.utf8Ok (bs.drop (i + 1)) := by
        rw [hok, hdrop, Utf8.utf8Ok_ascii b _ hasc]
      by_cases ha1 : a = 4294967295
      · have he1 : Numeric.bool (Numeric.irelop32 IRelOp.ne a 4294967295) = 0 := by
          simp [Numeric.bool, Numeric.irelop32, ha1]
        clear ha1
        brn he1
        clear he1
        mstep
        mstep; mstep; mstep; mstep
        rw [SerdeRead.ofNat_succ i (by omega)]
        mstep; mstep; mstep
        tail927 (i + 1)
      · have hne1 : Numeric.bool (Numeric.irelop32 IRelOp.ne a 4294967295) ≠ 0 := by
          simp [Numeric.bool, Numeric.irelop32, ha1]
        brt hne1
        clear hne1
        mstep; mstep; mstep; mstep; mstep
        by_cases hal : (a - UInt32.ofNat i &&& 3) = 0
        · brn hal
          clear hal
          mstep
          mstep; mstep; mstep
          by_cases hw : i + 8 ≤ bs.length
          · have hg : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat (len.toNat - 7))) = 0 := by
              simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
            brn hg
            clear hg
            iapply MemCpy.mwpi_loop0 (Cg := Cg)
              (R := 100 * (bs.length - (i + 1)) * cfg.regularOpCost + 124 * cfg.regularOpCost + R)
              (I := invA n inst mi Cg cfg.regularOpCost 124 210 R 8 out p len (UInt32.ofNat (len.toNat - 7)) a s l8 l9 l10
                bs i iprop(n ↦[wms][ out.toNat ] ob)) _ _ rfl
            isplitr
            · imodintro
              iintro %X %l HI
              iunfold invA at HI
              icases HI with ⟨%j, %l6', %⟨hX, hfr', hji, hj8, hokj⟩, Hc, Hb, Ho⟩
              subst hX
              rw [hfr']
              simp only [fr927]
              clear hfr'
              have hZ8 : 100 * (bs.length - (j + 8 + 1)) * cfg.regularOpCost + 700 * cfg.regularOpCost ≤
                  100 * (bs.length - (j + 1)) * cfg.regularOpCost := by
                rw [← Nat.add_mul]; apply Nat.mul_le_mul_right; omega
              by_cases hjeq : j = i
              · rw [if_pos hjeq, show 100 * (bs.length - (j + 1)) * cfg.regularOpCost + 124 * cfg.regularOpCost + R =
                  124 * cfg.regularOpCost + (100 * (bs.length - (j + 1)) * cfg.regularOpCost + R) by omega]
                generalize hZj : 100 * (bs.length - (j + 1)) * cfg.regularOpCost = Zj at hZ8
                word11
              · rw [if_neg hjeq, show 100 * (bs.length - (j + 1)) * cfg.regularOpCost + 210 * cfg.regularOpCost + R =
                  210 * cfg.regularOpCost + (100 * (bs.length - (j + 1)) * cfg.regularOpCost + R) by omega]
                generalize hZj : 100 * (bs.length - (j + 1)) * cfg.regularOpCost = Zj at hZ8
                word11
            isplitl [Hc]
            · iapply BorrowMut.credits_le
              iframe Hc
              ipureintro; omega
            inext
            iintro Hc
            iapply invA_intro n inst mi Cg cfg.regularOpCost 124 210 R 8 out p len _ a s l8 l9 l10 bs i _ i _ le_rfl
              hw hok
            iframe Hb Ho
            rw [if_pos rfl]
            iframe Hc
          · have hg : Numeric.bool (Numeric.irelop32 IRelOp.ge_u (UInt32.ofNat i) (UInt32.ofNat (len.toNat - 7))) ≠ 0 := by
              simp [Numeric.bool, Numeric.irelop32, UInt32.le_iff_toNat_le]; omega
            brt hg
            clear hg
            have hok' := hok
            have hji : i ≤ i := le_rfl
            after10x i
        · brt hal
          mstep; mstep; mstep; mstep
          rw [SerdeRead.ofNat_succ i (by omega)]
          mstep; mstep; mstep
          tail927 (i + 1)
    · exact absurd (hA b (by rw [← hbk]; simp)) hasc
  isplitl [Hc]
  · iapply BorrowMut.credits_le
    iframe Hc
    ipureintro; omega
  inext
  iintro Hc
  iapply inv927_intro n inst mi Cg cfg.regularOpCost 100 70 R out p len _ a bs _ 0 _ _ _ _ _ (by omega) (by simp)
  iframe Hb Ho
  iapply BorrowMut.credits_le
  iframe Hc
  ipureintro
  rw [Nat.sub_zero, hbs, ← hM]; omega

end L927

end WNear.Binary.FromUtf8
