import Bridge.Functions.SerdeFromTrait
import Mathlib.Tactic.Ring

/-!
# The parser's accepting cost is linear in the input (M6, pure)

`SerdeFromTrait.cost66` is 66's cost on an accepted input, in terms of the costs `K646`, `K169`,
`K81` of the callees not proved yet. This file bounds it by `(K0 + K1 · len) · c + x` from linear
bounds on those costs, by the bytes each call reads (`Lin646`, `Lin169`, `Lin81`):

* a key read from `q` to `p` costs at most `(a646 + b646 · (p - q)) · c`;
* the account id read from `j` to `p`, at most `(a169 + b169 · (p - j)) · c + x` (`x` is the
  allocation of its `String`, which the allocator charges partly in other units);
* an ignored value read from `j` to `p`, at most `(a81 + b81 · (p - j)) · c`.

`objCost_le` is the object loop's bound, by induction over the members: a member reads at least five
bytes (the opening quote, its key's closing quote, the colon, a byte of its value, which reads at least
one (`JsonSuffix.valueR_strict`), and the comma or the struct's `{`), so its fixed cost
`972 + cost194 + a646 + b646 + a + b` must be at most `5 · K1` (`hM169`,
`hM81`). `cost66_le` adds the prologue, the array form and `end`.
-/

namespace WNear.Binary.SerdeCost

open Wasm Wasm.Near

open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel WNear.SerdeStructLoop WNear.JsonSuffix
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeNextKey (keyQ keyWs)
open WNear.Binary.SerdeStructObj (objCost costObj objCost_end objCost_field objCost_ign)

section Bounds

variable (c : Nat) (K646 K169 K81 : Nat → Nat) (dv : List UInt8 → Option (WNear.AccountId × List UInt8))
  (ign : List UInt8 → Option (Unit × List UInt8)) (bs : List UInt8)

/-- `K646` is at most `a + b` per byte of the key's body and closing quote. -/
def Lin646 (a b : Nat) : Prop :=
  ∀ q k r, q ≤ bs.length → stringBody (bs.drop q) [] = some (some k, r) →
    K646 q ≤ (a + b * (bs.length - r.length - q)) * c

/-- `K169` is at most `a + b` per byte of the account id's value, plus `x`. -/
def Lin169 (a b x : Nat) : Prop :=
  ∀ j a' r, j ≤ bs.length → dv (bs.drop j) = some (a', r) → K169 j ≤ (a + b * (bs.length - r.length - j)) * c + x

/-- `K81` is at most `a + b` per byte of the ignored value. -/
def Lin81 (a b : Nat) : Prop :=
  ∀ j r, j ≤ bs.length → ign (bs.drop j) = some ((), r) → K81 j ≤ (a + b * (bs.length - r.length - j)) * c

end Bounds

theorem loopRes_suf {α : Type} (key : String) (dv : List UInt8 → Option (α × List UInt8))
    (ign : List UInt8 → Option (Unit × List UInt8)) (hdvS : ∀ bs a r, dv bs = some (a, r) → r <:+ bs)
    (hignS : ∀ bs r, ign bs = some ((), r) → r <:+ bs) {N : Nat} {first : Bool} {seen : Option α}
    {rest : List UInt8} {res : Option α × List UInt8} (h : loopRes key dv ign N first seen rest = some res) :
    res.2 <:+ rest := by
  unfold loopRes at h
  split at h
  · exact objLoop_suf key dv ign hdvS hignS _ _ _ _ h
  · split at h
    · rename_i r hs
      exact (objLoop_suf key dv ign hdvS hignS _ _ _ _ h).trans (cons_suf hs)
    · rename_i r hs
      simp only [Option.some.injEq] at h
      subst h
      exact cons_suf hs
    · simp at h

theorem keyQ_pos {first : Bool} {bs : List UInt8} {i q : Nat} (h : keyQ first bs i = some q) :
    q = i + keyWs first bs i + (if first then 1 else 2) := by
  unfold keyQ at h
  unfold keyWs
  cases first <;> simp only [ite_true, Bool.false_eq_true, ite_false] at h ⊢
  · split at h
    · split at h
      · simp only [Option.some.injEq] at h; omega
      · simp at h
    · simp at h
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h

theorem drop_len {bs r : List UInt8} {p : Nat} (h : bs.drop p = r) (hp : p ≤ bs.length) :
    p = bs.length - r.length := by
  rw [← h]; simp; omega

section Loop

variable (c : Nat) (K646 K169 K81 : Nat → Nat) (dv : List UInt8 → Option (WNear.AccountId × List UInt8))
  (ign : List UInt8 → Option (Unit × List UInt8)) (bs : List UInt8)

/-- One member's arithmetic: the fixed cost and the bytes it reads. -/
theorem member_arith (K1 a646 b646 av bv kw w2 D1 D3 T s Fst C194 : Nat) (hK : 96 ≤ K1) (hb646 : b646 ≤ K1)
    (hbv : bv ≤ K1) (hD1 : 1 ≤ D1) (hD3 : 1 ≤ D3) (hM : 972 + C194 + a646 + b646 + av + bv ≤ 5 * K1) (hs : Fst + K1 * s = 2 * K1) :
    972 + 96 * (kw + w2) + C194 + a646 + b646 * D1 + av + bv * D3 + (300 + K1 * T) ≤
      Fst + 300 + K1 * (kw + s + D1 + w2 + 1 + D3 + T) := by
  obtain ⟨D1', rfl⟩ : ∃ D1', D1 = D1' + 1 := ⟨D1 - 1, by omega⟩
  obtain ⟨D3', rfl⟩ : ∃ D3', D3 = D3' + 1 := ⟨D3 - 1, by omega⟩
  have e1 : 96 * kw ≤ K1 * kw := Nat.mul_le_mul_right kw hK
  have e2 : 96 * w2 ≤ K1 * w2 := Nat.mul_le_mul_right w2 hK
  have e3 : b646 * D1' ≤ K1 * D1' := Nat.mul_le_mul_right D1' hb646
  have e4 : bv * D3' ≤ K1 * D3' := Nat.mul_le_mul_right D3' hbv
  have r1 : K1 * (kw + s + (D1' + 1) + w2 + 1 + (D3' + 1) + T) =
      K1 * kw + K1 * s + K1 * D1' + K1 + K1 * w2 + K1 + K1 * D3' + K1 + K1 * T := by ring
  have r2 : 96 * (kw + w2) = 96 * kw + 96 * w2 := by ring
  have r3 : b646 * (D1' + 1) = b646 * D1' + b646 := by ring
  have r4 : bv * (D3' + 1) = bv * D3' + bv := by ring
  rw [r1, r2, r3, r4]
  omega

set_option maxHeartbeats 4000000 in
/-- **The object loop's cost is linear**: from the loop head at `i` (`first`, the field read so far
`sA`), on members that `loopRes` accepts up to the rest `rF`, at most `K1` per byte read, plus `K1`
for the first member, `300` for the `}`, and `x` when the field is still to be read. -/
theorem objCost_le (K1 a646 b646 a169 b169 x a81 b81 : Nat)
    (h646 : Lin646 c K646 bs a646 b646) (h169 : Lin169 c K169 dv bs a169 b169 x) (h81 : Lin81 c K81 ign bs a81 b81)
    (hdvS : ∀ bs a r, dv bs = some (a, r) → r <:+ bs) (hignS : ∀ bs r, ign bs = some ((), r) → r <:+ bs)
    (hdvL : ∀ bs a r, dv bs = some (a, r) → r.length < bs.length)
    (hignL : ∀ bs r, ign bs = some ((), r) → r.length < bs.length)
    (hK : 96 ≤ K1) (hb646 : b646 ≤ K1) (hb169 : b169 ≤ K1) (hb81 : b81 ≤ K1)
    (hM169 : 972 + SerdeKey.cost194 + a646 + b646 + a169 + b169 ≤ 5 * K1)
    (hM81 : 972 + SerdeKey.cost194 + a646 + b646 + a81 + b81 ≤ 5 * K1) :
    ∀ (N : Nat) (first : Bool) (i : Nat) (sA : Option WNear.AccountId) (a : WNear.AccountId) (rF : List UInt8),
      i ≤ bs.length → loopRes "account_id" dv ign N first sA (bs.drop i) = some (some a, rF) →
      objCost c K646 K169 K81 dv ign bs N first i ≤
        ((if first then K1 else 0) + 300 + K1 * (bs.length - rF.length - i)) * c + (if sA.isNone then x else 0) := by
  intro N
  induction N with
  | zero =>
    intro first i sA a rF hi h
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨hf, -, -⟩ := loop_end "account_id" dv ign h hb
      subst hf
      have := loop_end "account_id" dv ign h hb
      obtain ⟨-, -, hrF⟩ := this
      have hl := SerdeNextKey.getElem_lt hb
      rw [objCost_end c K646 K169 K81 dv ign bs hb, hrF]
      simp only [Bool.false_eq_true, ite_false, List.length_drop]
      have hw : bs.length - (bs.length - (i + wsLen (bs.drop i) + 1)) - i = wsLen (bs.drop i) + 1 := by omega
      rw [hw]
      have : (300 + 96 * wsLen (bs.drop i)) * c ≤ (0 + 300 + K1 * (wsLen (bs.drop i) + 1)) * c := by
        apply Nat.mul_le_mul_right
        have := Nat.mul_le_mul_right (wsLen (bs.drop i)) hK
        rw [Nat.mul_add]; omega
      omega
    · obtain ⟨n, -, -, -, hN, -⟩ := loop_member "account_id" dv ign h hb
      simp at hN
  | succ n ih =>
    intro first i sA a rF hi h
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨hf, -, hrF⟩ := loop_end "account_id" dv ign h hb
      subst hf
      have hl := SerdeNextKey.getElem_lt hb
      rw [objCost_end c K646 K169 K81 dv ign bs hb, hrF]
      simp only [Bool.false_eq_true, ite_false, List.length_drop]
      have hw : bs.length - (bs.length - (i + wsLen (bs.drop i) + 1)) - i = wsLen (bs.drop i) + 1 := by omega
      rw [hw]
      have : (300 + 96 * wsLen (bs.drop i)) * c ≤ (0 + 300 + K1 * (wsLen (bs.drop i) + 1)) * c := by
        apply Nat.mul_le_mul_right
        have := Nat.mul_le_mul_right (wsLen (bs.drop i)) hK
        rw [Nat.mul_add]; omega
      omega
    · obtain ⟨n', q, k, rest1, hN, hq, hs, hdup, rest2, hc, hv⟩ := loop_member "account_id" dv ign h hb
      simp only [Nat.add_right_cancel_iff] at hN
      subst hN
      -- positions: the key's body at `q`, its end `p1`, the colon at `p1 + w2`, the value at `j`
      have hq' := keyQ_pos hq
      have hql := SerdeStructObj.keyQ_le hq
      have hs1 : rest1 <:+ bs.drop q := stringBody_suf' hs
      have hp1 := drop_suf' hs1
      have hlt1 := JsonFuel.stringBody_len hs
      simp only [List.length_drop] at hlt1
      generalize hP1 : bs.length - rest1.length = p1 at hp1
      have hc' : skipWhitespace (bs.drop p1) = 0x3A :: rest2 := by
        unfold colonAt at hc
        rw [hp1]
        split at hc
        · rename_i r' e; simp only [Option.some.injEq] at hc; subst hc; exact e
        · simp at hc
      obtain ⟨hcol, hr2⟩ := skip_drop_cons hc'
      have hcl := SerdeNextKey.getElem_lt hcol
      generalize hW2 : wsLen (bs.drop p1) = w2 at hcol hr2 hcl
      have hK646 := h646 q k rest1 hql hs
      rw [hP1] at hK646
      rcases hv with ⟨hk, a', r3, hd, hl⟩ | ⟨hk, r3, hd, hl⟩
      · -- the field: 169, then the loop with the field read
        have hsA : sA = none := by
          cases sA with
          | none => rfl
          | some _ => exact absurd ⟨hk, rfl⟩ hdup
        subst hsA
        rw [hr2] at hd
        have h3 := drop_suf' (hdvS _ _ _ hd)
        have hj3 : r3.length < bs.length - (p1 + w2 + 1) := by
          have := hdvL _ _ _ hd; simp at this; omega
        have hK169 := h169 _ a' r3 (by omega) hd
        have hrF := loopRes_suf "account_id" dv ign hdvS hignS hl
        simp only at hrF
        have hFl : rF.length ≤ r3.length := hrF.length_le
        have ih' := ih false (bs.length - r3.length) (some a') a rF (by omega) (by rw [h3]; exact hl)
        simp only [Bool.false_eq_true, ite_false, Option.isNone_some] at ih'
        rw [objCost_field c K646 K169 K81 dv ign bs hb hq hs hk (by rw [hP1, hW2]; exact hd), hP1, hW2]
        simp only [Option.isNone_none, ite_true]
        have hT := member_arith K1 a646 b646 a169 b169 (keyWs first bs i) w2 (p1 - q)
          (bs.length - r3.length - (p1 + w2 + 1)) (bs.length - rF.length - (bs.length - r3.length))
          (if first then 1 else 2) (if first then K1 else 0) SerdeKey.cost194 hK hb646 hb169 (by omega) (by omega) hM169
          (by cases first <;> simp <;> omega)
        have hsum : keyWs first bs i + (if first then 1 else 2) + (p1 - q) + w2 + 1 +
            (bs.length - r3.length - (p1 + w2 + 1)) + (bs.length - rF.length - (bs.length - r3.length)) =
            bs.length - rF.length - i := by
          cases first <;> simp at hq' ⊢ <;> omega
        rw [hsum] at hT
        have hT' := Nat.mul_le_mul_right c hT
        calc (972 + 96 * (keyWs first bs i + w2) + SerdeKey.cost194) * c + K646 q +
              (K169 (p1 + w2 + 1) + objCost c K646 K169 K81 dv ign bs _ false (bs.length - r3.length))
            ≤ (972 + 96 * (keyWs first bs i + w2) + SerdeKey.cost194) * c + (a646 + b646 * (p1 - q)) * c +
              (((a169 + b169 * (bs.length - r3.length - (p1 + w2 + 1))) * c + x) +
                (0 + 300 + K1 * (bs.length - rF.length - (bs.length - r3.length))) * c) := by omega
          _ = (972 + 96 * (keyWs first bs i + w2) + SerdeKey.cost194 + a646 + b646 * (p1 - q) + a169 +
                b169 * (bs.length - r3.length - (p1 + w2 + 1)) +
                (300 + K1 * (bs.length - rF.length - (bs.length - r3.length)))) * c + x := by ring
          _ ≤ ((if first then K1 else 0) + 300 + K1 * (bs.length - rF.length - i)) * c + x := by omega
      · -- another key: 81, then the loop
        rw [hr2] at hd
        have h3 := drop_suf' (hignS _ _ hd)
        have hj3 : r3.length < bs.length - (p1 + w2 + 1) := by
          have := hignL _ _ hd; simp at this; omega
        have hK81 := h81 _ r3 (by omega) hd
        have hrF := loopRes_suf "account_id" dv ign hdvS hignS hl
        simp only at hrF
        have hFl : rF.length ≤ r3.length := hrF.length_le
        have ih' := ih false (bs.length - r3.length) sA a rF (by omega) (by rw [h3]; exact hl)
        simp only [Bool.false_eq_true, ite_false] at ih'
        rw [objCost_ign c K646 K169 K81 dv ign bs hb hq hs hk (by rw [hP1, hW2]; exact hd), hP1, hW2]
        have hT := member_arith K1 a646 b646 a81 b81 (keyWs first bs i) w2 (p1 - q)
          (bs.length - r3.length - (p1 + w2 + 1)) (bs.length - rF.length - (bs.length - r3.length))
          (if first then 1 else 2) (if first then K1 else 0) SerdeKey.cost194 hK hb646 hb81 (by omega) (by omega) hM81
          (by cases first <;> simp <;> omega)
        have hsum : keyWs first bs i + (if first then 1 else 2) + (p1 - q) + w2 + 1 +
            (bs.length - r3.length - (p1 + w2 + 1)) + (bs.length - rF.length - (bs.length - r3.length)) =
            bs.length - rF.length - i := by
          cases first <;> simp at hq' ⊢ <;> omega
        rw [hsum] at hT
        have hT' := Nat.mul_le_mul_right c hT
        generalize (if sA.isNone = true then x else 0) = X at ih' ⊢
        calc (972 + 96 * (keyWs first bs i + w2) + SerdeKey.cost194) * c + K646 q +
              (K81 (p1 + w2 + 1) + objCost c K646 K169 K81 dv ign bs _ false (bs.length - r3.length))
            ≤ (972 + 96 * (keyWs first bs i + w2) + SerdeKey.cost194) * c + (a646 + b646 * (p1 - q)) * c +
              ((a81 + b81 * (bs.length - r3.length - (p1 + w2 + 1))) * c +
                ((0 + 300 + K1 * (bs.length - rF.length - (bs.length - r3.length))) * c + X)) := by omega
          _ = (972 + 96 * (keyWs first bs i + w2) + SerdeKey.cost194 + a646 + b646 * (p1 - q) + a81 +
                b81 * (bs.length - r3.length - (p1 + w2 + 1)) +
                (300 + K1 * (bs.length - rF.length - (bs.length - r3.length)))) * c + X := by ring
          _ ≤ ((if first then K1 else 0) + 300 + K1 * (bs.length - rF.length - i)) * c + X := by omega

end Loop


section Total

/-- **66's accepting cost is linear in the input**: on an input `Call.decode` reads as `ftBalanceOf a`,
with readers that agree with the model and callees within `Lin646`, `Lin169`, `Lin81`, `cost66` is at
most `(1725 + a169 + K1 · len) · c + x`, where `K1` pays for every byte: `96` (whitespace), the
callees' `b`s, and a member's fixed cost over its five bytes (`hM169`, `hM81`). -/
theorem cost66_le (cfg : WasmConfig) (K646 K169 K81 : Nat → Nat)
    (dv : List UInt8 → Option (WNear.AccountId × List UInt8)) (ign : List UInt8 → Option (Unit × List UInt8))
    (bs : List UInt8) (hdv : Agrees dv (valueAs WNear.account)) (hign : Agrees ign valueSkip)
    (a : WNear.AccountId) (hdec : WNear.Call.decode "ft_balance_of" bs = some (.ftBalanceOf a))
    (K1 a646 b646 a169 b169 x a81 b81 : Nat)
    (h646 : Lin646 cfg.regularOpCost K646 bs a646 b646) (h169 : Lin169 cfg.regularOpCost K169 dv bs a169 b169 x)
    (h81 : Lin81 cfg.regularOpCost K81 ign bs a81 b81)
    (hK : 96 ≤ K1) (hb646 : b646 ≤ K1) (hb169 : b169 ≤ K1) (hb81 : b81 ≤ K1)
    (hM169 : 972 + SerdeKey.cost194 + a646 + b646 + a169 + b169 ≤ 5 * K1)
    (hM81 : 972 + SerdeKey.cost194 + a646 + b646 + a81 + b81 ≤ 5 * K1) :
    SerdeFromTrait.cost66 cfg K646 K169 K81 dv ign bs ≤
      (1725 + a169 + K1 * bs.length) * cfg.regularOpCost + x := by
  obtain ⟨r, hS, hE⟩ := SerdeFromTrait.decode_struct hdv hign hdec
  obtain ⟨hdv0, hdvs, -, -, hdvS, hignS⟩ := SerdeFromTrait.reader_facts hdv hign bs
  have hdvL : ∀ bs a r, dv bs = some (a, r) → r.length < bs.length :=
    JsonSuffix.agrees_strict hdv (fun _ _ _ h => JsonSuffix.valueAs_strict _ h)
  have hignL : ∀ bs r, ign bs = some ((), r) → r.length < bs.length := fun bs r h =>
    JsonSuffix.agrees_strict hign (fun _ x _ h => by cases x; exact JsonSuffix.valueSkip_strict h) bs () r h
  have hsuf := JsonSuffix.structDe_suf "account_id" dv ign hdvS hignS hS
  have hrl : r.length ≤ bs.length := hsuf.length_le
  have hrest : SerdeFromTrait.restLen dv ign bs = r.length := by
    unfold SerdeFromTrait.restLen; rw [hS]
  unfold SerdeFromTrait.cost66 SerdeStruct78.costS
  rw [hrest]
  generalize hc : cfg.regularOpCost = c
  have e96 := Nat.mul_le_mul_right r.length hK
  rcases SerdeStruct78.structDe_cases hS hdv0 hdvs with ⟨ho, hl⟩ | ⟨r1, hok, hrr⟩
  · rw [if_pos ho]
    unfold costObj
    simp only [List.drop_zero, Nat.zero_add]
    rw [hc]
    have hw0 := SerdeNextKey.getElem_lt ho
    have hlb := objCost_le c K646 K169 K81 dv ign bs K1 a646 b646 a169 b169 x a81 b81 (hc ▸ h646) (hc ▸ h169)
      (hc ▸ h81) hdvS hignS hdvL hignL hK hb646 hb169 hb81 hM169 hM81 _ true (wsLen bs + 1) none a r (by omega)
      (by simpa [loopRes] using hl)
    simp only [ite_true, Option.isNone_none] at hlb
    have hrF : r.length ≤ bs.length - (wsLen bs + 1) := by
      have := (loopRes_suf "account_id" dv ign hdvS hignS (first := true) (seen := none)
        (by simpa [loopRes] using hl)).length_le
      simp at this; omega
    have e0 := Nat.mul_le_mul_right (wsLen bs) hK
    have hcoef : 400 + 96 * wsLen bs + (K1 + 300 + K1 * (bs.length - r.length - (wsLen bs + 1))) + 300 +
        (425 + 96 * r.length) ≤ 1725 + a169 + K1 * bs.length := by
      have hsplit : bs.length = (bs.length - r.length - (wsLen bs + 1)) + wsLen bs + 1 + r.length := by omega
      have : K1 * bs.length = K1 * (bs.length - r.length - (wsLen bs + 1)) + K1 * wsLen bs + K1 + K1 * r.length := by
        conv_lhs => rw [hsplit]
        ring
      omega
    have := Nat.mul_le_mul_right c hcoef
    calc (425 + 96 * r.length) * c + ((400 + 96 * wsLen bs) * c +
          objCost c K646 K169 K81 dv ign bs (bs.length - (wsLen bs + 1) + 1) true (wsLen bs + 1) + 300 * c)
        ≤ (425 + 96 * r.length) * c + ((400 + 96 * wsLen bs) * c +
          ((K1 + 300 + K1 * (bs.length - r.length - (wsLen bs + 1))) * c + x) + 300 * c) := by omega
      _ = (400 + 96 * wsLen bs + (K1 + 300 + K1 * (bs.length - r.length - (wsLen bs + 1))) + 300 +
            (425 + 96 * r.length)) * c + x := by ring
      _ ≤ (1725 + a169 + K1 * bs.length) * c + x := by omega
  · obtain ⟨hb0, -, hd, hb4⟩ := hok
    simp only [List.drop_zero, Nat.zero_add] at hb0 hd
    rw [if_neg (by rw [hb0]; decide), hd]
    unfold SerdeStructArr.costArr
    simp only [List.drop_zero, Nat.zero_add]
    rw [hc]
    have hw4 := SerdeNextKey.getElem_lt hb4
    have hr1 : r1 <:+ bs.drop (wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) := hdvS _ _ _ hd
    have hr1l : r1.length ≤ bs.length - (wsLen bs + 1 + wsLen (bs.drop (wsLen bs + 1))) := by
      have := hr1.length_le; simp at this; omega
    have hK169 := (hc ▸ h169) _ a r1 (by omega) hd
    have hrlen : r.length = bs.length - (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1) := by
      rw [hrr]; simp
    generalize wsLen bs = w0 at hr1l hK169 hrlen ⊢
    generalize wsLen (bs.drop (w0 + 1)) = w2 at hr1l hK169 hrlen ⊢
    generalize wsLen (bs.drop (bs.length - r1.length)) = w4 at hw4 hrlen ⊢
    have e0 := Nat.mul_le_mul_right w0 hK
    have e2 := Nat.mul_le_mul_right w2 hK
    have e4 := Nat.mul_le_mul_right w4 hK
    have eb := Nat.mul_le_mul_right (bs.length - r1.length - (w0 + 1 + w2)) hb169
    have hcoef : 1300 + 96 * (w0 + w2 + w4) + (a169 + b169 * (bs.length - r1.length - (w0 + 1 + w2))) +
        (425 + 96 * r.length) ≤ 1725 + a169 + K1 * bs.length := by
      have hsplit : bs.length = w0 + 1 + w2 + (bs.length - r1.length - (w0 + 1 + w2)) + w4 + 1 + r.length := by omega
      have : K1 * bs.length = K1 * w0 + K1 + K1 * w2 + K1 * (bs.length - r1.length - (w0 + 1 + w2)) + K1 * w4 + K1 +
          K1 * r.length := by
        conv_lhs => rw [hsplit]
        ring
      rw [Nat.mul_add 96, Nat.mul_add 96]
      omega
    have := Nat.mul_le_mul_right c hcoef
    calc (425 + 96 * r.length) * c + ((1300 + 96 * (w0 + w2 + w4)) * c + K169 (w0 + 1 + w2))
        ≤ (425 + 96 * r.length) * c + ((1300 + 96 * (w0 + w2 + w4)) * c +
          ((a169 + b169 * (bs.length - r1.length - (w0 + 1 + w2))) * c + x)) := by omega
      _ = (1300 + 96 * (w0 + w2 + w4) + (a169 + b169 * (bs.length - r1.length - (w0 + 1 + w2))) +
            (425 + 96 * r.length)) * c + x := by ring
      _ ≤ (1725 + a169 + K1 * bs.length) * c + x := by omega

end Total

end WNear.Binary.SerdeCost
