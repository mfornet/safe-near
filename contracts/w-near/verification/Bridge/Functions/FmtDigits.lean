import Bridge.Functions.Interface
import Bridge.Functions.U128From
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Formatting (milestone M5): decimal digits, and the design of the `Fmt*` files

`serde_json::to_vec(&U128)` (96) formats the `u128` with `to_string()` and
writes it as a JSON string. Its call graph, from the bodies:

```
96  to_vec(out, &u128)        Vec::with_capacity(128) (94); serialize(&u128, &mut &mut vec) (385);
                              Ok(vec) or, on an error, drop (68) and Err
385 U128::serialize           String::new() at sp+16 (ptr 1, cap 0, len 0);
                              Arguments { pieces: [""] (1051836, 1), fmt: None, args: [(&&u128, fn 92)] };
                              Write::write_fmt(&mut string, args) (746) → core::fmt::write (872)
                                with the `&mut String as Write` vtable 1065404 (write_str: table 157);
                              Result::expect (365); Vec::deref (779); serialize_str (383) into the
                              Vec; drop the String (321 → 778, 747)
872 core::fmt::write          fmt: None ⇒ for each argument: write_str(piece) through the vtable
                              (call_indirect, here the empty piece ""), then the argument's
                              formatter (call_indirect, table 92 → `<&u128 as Display>` → 901) with a
                              `Formatter { flags 0, fill ' ', align Unknown(3), width/precision None,
                              buf (data, vtable) }` at sp+8; then the trailing piece if any (none)
901 <u128 as Display>::fmt    fmt_u128(lo, hi, true, f) (902)
902 core::fmt::num::fmt_u128  buf[39] at sp+101, curr at sp+140 (39):
                              (n, rem) = udiv_1e19(n) (via __multi3, 954); parse_u64_into(rem) (900);
                              if n ≠ 0: memset '0' to position 20 (952), curr = 20, again with the
                              next 19 digits; if still ≠ 0: memset '0' to 1, buf[0] = n + '0', curr = 0;
                              Formatter::pad_integral(f, true, "", buf[curr..39]) (903)
900 parse_u64_into            the decimal digits of a u64, two at a time from DEC_DIGITS_LUT
                              (200 bytes at 1070974), backwards before `curr`, no loop
903 pad_integral              no width, no sign, no `#`: write_prefix (910) then write_str of the
                              digits through the vtable
```

So `fmt::write` is reached with a single `Display` argument, and the sink
is a `String` (not the serializer's `Vec`): the digits reach the output
`Vec` only through `serialize_str` (383, `format_escaped_str`). The
`String` starts empty (capacity 0): the empty piece's `write_str` reserves
nothing, and the digits' `write_str` grows it once (`RawVec::reserve` →
`finish_grow`, an allocation, not `__rust_realloc`, since the capacity is
0). The output `Vec` has capacity 128 ≥ 41, so `serialize_str` never
grows it.

## Design

* **Digits.** `decDigits n` is the ASCII decimal representation of `n`
  (no leading zeros, `"0"` for 0), `padDigits k m` the last `k` digits of
  `m` with leading zeros. Every digit-writing function is specified by them:
  `decDigits_split` (`n ≥ 10^k`: the leading digits, then `padDigits k n`)
  is the one fact the proofs of 900 and 902 compose.
* **The lookup table.** `lut` (the 200 bytes `"00" … "99"`) is owned as
  `n ↦[wms][ 1070974 ] lut`, threaded through the specs and returned
  unchanged; `lut_data` says the data segment initialises it. A two-digit
  load is `lut_focus` (the two bytes `padDigits 2 x` at `1070974 + 2x`).
* **Writing backwards.** The digit writers (900, 902) take the cursor
  `curr` by pointer and own exactly the bytes they write: the
  `(decDigits v).length` bytes before `curr`, which they return holding
  `decDigits v`, the cursor moved back by as much.
* **A `Write` sink appending to a `Vec<u8>`/`String`** (for `fmt::write`
  and `pad_integral`): the sink is a `dyn Write` pair `(data, vtable)`;
  its invariant `sink bs` says the `Vec` behind `data` holds `bs` (a live
  heap block when its capacity is nonzero, with the allocator's invariant);
  `write_str(data, p, k)` with the `k` bytes `s` at `p` returns `Ok` (0) and
  leaves `sink (bs ++ s)`, its cost a function of `k` and of whether the
  `Vec` grows. `fmt::write` with one `Display` argument whose `fmt` writes
  `t` through the formatter is then: `sink bs` to `sink (bs ++ piece ++ t)`.
-/

namespace WNear.Binary.FmtDigits

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-! ## Decimal digits -/

/-- The ASCII digit `d`. -/
def digit (d : Nat) : UInt8 := UInt8.ofNat (48 + d)

/-- The last `k` decimal digits of `m`, with leading zeros. -/
def padDigits : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, m => padDigits k (m / 10) ++ [digit (m % 10)]

/-- The decimal digits of `n`, without leading zeros (`"0"` for 0). -/
def decDigits (n : Nat) : List UInt8 :=
  if n < 10 then [digit n] else decDigits (n / 10) ++ [digit (n % 10)]
termination_by n
decreasing_by omega

@[simp] theorem padDigits_length (k m : Nat) : (padDigits k m).length = k := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih => simp [padDigits, ih]

theorem padDigits_add (a b m : Nat) :
    padDigits (a + b) m = padDigits a (m / 10 ^ b) ++ padDigits b m := by
  induction b generalizing m with
  | zero => simp [padDigits]
  | succ b ih =>
    rw [← Nat.add_assoc, padDigits, ih, padDigits, Nat.div_div_eq_div_mul, List.append_assoc,
      Nat.pow_succ, Nat.mul_comm (10 ^ b) 10]

theorem padDigits_mod (k m : Nat) : padDigits k (m % 10 ^ k) = padDigits k m := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    rw [padDigits, padDigits, ← ih ((m % 10 ^ (k + 1)) / 10), ← ih (m / 10), Nat.pow_succ',
      Nat.mod_mul_right_div_self, Nat.mod_mod, Nat.mod_mul_right_mod]

/-- The leading digits, then the last `k`: `n ≥ 10^k`. -/
theorem decDigits_split (k n : Nat) (h : 10 ^ k ≤ n) :
    decDigits n = decDigits (n / 10 ^ k) ++ padDigits k n := by
  induction k generalizing n with
  | zero => simp [padDigits]
  | succ k ih =>
    have h10 : ¬ n < 10 := by
      have : 10 ≤ 10 ^ (k + 1) := by
        calc 10 = 10 ^ 1 := rfl
          _ ≤ 10 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [decDigits]
    simp only [h10, ↓reduceIte]
    rw [ih (n / 10) (by
      rw [Nat.le_div_iff_mul_le (by norm_num)]; rw [Nat.pow_succ] at h; exact h),
      Nat.div_div_eq_div_mul, padDigits, List.append_assoc, Nat.pow_succ, Nat.mul_comm (10 ^ k) 10]

theorem decDigits_lt10 (n : Nat) (h : n < 10) : decDigits n = [digit n] := by
  rw [decDigits]; simp [h]

/-- Exactly `k + 1` digits. -/
theorem decDigits_eq_pad (k n : Nat) (h1 : 10 ^ k ≤ n) (h2 : n < 10 ^ (k + 1)) :
    decDigits n = padDigits (k + 1) n := by
  rw [decDigits_split k n h1, Nat.add_comm k 1, padDigits_add 1 k]
  have hq : n / 10 ^ k < 10 := by
    rw [Nat.div_lt_iff_lt_mul (by positivity)]; simpa [Nat.pow_succ, Nat.mul_comm] using h2
  rw [decDigits_lt10 _ hq]
  simp [padDigits, Nat.mod_eq_of_lt hq]

theorem decDigits_length_split (k n : Nat) (h : 10 ^ k ≤ n) :
    (decDigits n).length = (decDigits (n / 10 ^ k)).length + k := by
  rw [decDigits_split k n h]; simp

theorem decDigits_length_lt (k n : Nat) (h1 : 10 ^ k ≤ n) (h2 : n < 10 ^ (k + 1)) :
    (decDigits n).length = k + 1 := by
  rw [decDigits_eq_pad k n h1 h2]; simp

theorem decDigits_length_pos (n : Nat) : 1 ≤ (decDigits n).length := by
  rw [decDigits]; split <;> simp

/-- Two digits. -/
theorem padDigits_two (m : Nat) : padDigits 2 m = [digit (m / 10 % 10), digit (m % 10)] := by
  simp [padDigits]

/-! ## The two-digit lookup table (`DEC_DIGITS_LUT`) -/

/-- `"00010203…99"`. -/
def lut : List UInt8 := (List.range 100).flatMap (padDigits 2)

theorem lut_length : lut.length = 200 := by rfl

set_option maxRecDepth 100000 in
theorem lut_pair : ∀ x < 100, (lut.drop (2 * x)).take 2 = padDigits 2 x := by decide

set_option maxRecDepth 100000 in
/-- The data segment holds it at 1070974. -/
theorem lut_data :
    (List.range 200).map (fun k => wNearSource.read (159306 + (1070974 - 1048576) + k)) = lut := by
  decide

/-! ## Separation-logic helpers -/

section Mem

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- The `w` bytes at offset `k` of a range, apart, and the range back with
any `w` bytes there. -/
theorem memBytes_focus (n a k w : Nat) (l : List UInt8) (h : k + w ≤ l.length) :
    memBytes (H := NearState) (GF := GF) n a l ⊢
      n ↦[wms][ a + k ] (l.drop k).take w ∗
        (∀ bs : List UInt8, ⌜bs.length = w⌝ -∗ n ↦[wms][ a + k ] bs -∗
          n ↦[wms][ a ] (l.take k ++ bs ++ l.drop (k + w))) := by
  iintro H
  have e1 := (memBytes_append (GF := GF) (H := NearState) n a (l.take k) (l.drop k)).1
  rw [List.take_append_drop, List.length_take, show min k l.length = k by omega] at e1
  ihave H := e1 $$ H
  icases H with ⟨H1, H2⟩
  have e2 := (memBytes_append (GF := GF) (H := NearState) n (a + k) ((l.drop k).take w)
    ((l.drop k).drop w)).1
  rw [List.take_append_drop, List.length_take, List.length_drop,
    show min w (l.length - k) = w by omega] at e2
  ihave H2 := e2 $$ H2
  icases H2 with ⟨H2, H3⟩
  iframe H2
  iintro %bs %hbs Hb
  iapply (memBytes_append (GF := GF) (H := NearState) n a (l.take k ++ bs) (l.drop (k + w))).2
  rw [List.length_append, List.length_take, hbs, show min k l.length = k by omega]
  isplitr [H3]
  · iapply (memBytes_append (GF := GF) (H := NearState) n a (l.take k) bs).2
    rw [List.length_take, show min k l.length = k by omega]
    iframe H1 Hb
  · rw [List.drop_drop, ← Nat.add_assoc]; iexact H3

/-- The pair of digits `x` in the table. -/
theorem lut_focus (n x : Nat) (hx : x < 100) :
    memBytes (H := NearState) (GF := GF) n 1070974 lut ⊢
      n ↦[wms][ 1070974 + 2 * x ] padDigits 2 x ∗
        (n ↦[wms][ 1070974 + 2 * x ] padDigits 2 x -∗ n ↦[wms][ 1070974 ] lut) := by
  iintro H
  icases memBytes_focus n 1070974 (2 * x) 2 lut (by rw [lut_length]; omega) $$ H with ⟨H1, H2⟩
  rw [lut_pair x hx]
  iframe H1
  iintro H1
  have e : lut.take (2 * x) ++ padDigits 2 x ++ lut.drop (2 * x + 2) = lut := by
    rw [← lut_pair x hx, List.append_assoc, ← List.drop_drop, List.take_append_drop,
      List.take_append_drop]
  ispecialize H2 $$ %(padDigits 2 x)
  rw [e]
  iapply H2
  · ipureintro; simp
  · iexact H1

/-- A range in two. -/
theorem memBytes_split2 (n a k : Nat) (l : List UInt8) (h : k ≤ l.length) :
    memBytes (H := NearState) (GF := GF) n a l ⊢
      n ↦[wms][ a ] l.take k ∗ n ↦[wms][ a + k ] l.drop k := by
  have e := memBytes_append (GF := GF) (H := NearState) n a (l.take k) (l.drop k)
  rw [List.take_append_drop, List.length_take, show min k l.length = k by omega] at e
  exact e.1

/-- Two ranges in one. -/
theorem memBytes_join2 (n a k : Nat) (x y : List UInt8) (h : x.length = k) :
    n ↦[wms][ a ] x ∗ n ↦[wms][ a + k ] y ⊢ memBytes (H := NearState) (GF := GF) n a (x ++ y) := by
  have e := memBytes_append (GF := GF) (H := NearState) n a x y
  rw [h] at e
  exact e.2

/-- The same range at an equal address. -/
theorem memBytes_at (n : Nat) {a b : Nat} (l : List UInt8) (h : a = b) :
    memBytes (H := NearState) (GF := GF) n a l ⊢ n ↦[wms][ b ] l := by
  subst h; exact .rfl

end Mem

/-! ## Loads and stores of digits -/

/-- A 16-bit load stored back with a 16-bit store: the same two bytes. -/
theorem storeBytes_load16 (a b : UInt8) :
    storeBytes (loadValue NumType.i32 (some { bits := 16, signed := false })
      (Memory.decodeLE [a, b])) 2 = [a, b] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  simp [loadValue, storeBytes, storeRaw, Memory.decodeLE, List.range, List.range.loop]
  constructor <;> (apply UInt8.toNat_inj.mp; simp; try omega)

theorem storeBytes_load16' (bs : List UInt8) (h : bs.length = 2) :
    storeBytes (loadValue NumType.i32 (some { bits := 16, signed := false })
      (Memory.decodeLE bs)) 2 = bs := by
  match bs, h with
  | [a, b], _ => exact storeBytes_load16 a b

/-! ## Digits in pairs, and a bound -/

theorem pad_step (k m : Nat) : padDigits (k + 2) m = padDigits k (m / 100) ++ padDigits 2 (m % 100) := by
  rw [padDigits_add k 2, ← padDigits_mod 2 m]; rfl

theorem pad2_mod (m : Nat) : padDigits 2 m = padDigits 2 (m % 100) := (padDigits_mod 2 m).symm

theorem pad8 (m : Nat) : padDigits 8 m = padDigits 2 (m % 10 ^ 8 / 10 ^ 6 % 100) ++
    padDigits 2 (m % 10 ^ 8 / 10 ^ 4 % 100) ++ padDigits 2 (m % 10 ^ 8 / 10 ^ 2 % 100) ++
    padDigits 2 (m % 10 ^ 8 % 100) := by
  rw [pad_step 6, pad_step 4, pad_step 2, pad2_mod (m / 100 / 100 / 100)]
  have e1 : m / 100 / 100 / 100 % 100 = m % 10 ^ 8 / 10 ^ 6 % 100 := by omega
  have e2 : m / 100 / 100 % 100 = m % 10 ^ 8 / 10 ^ 4 % 100 := by omega
  have e3 : m / 100 % 100 = m % 10 ^ 8 / 10 ^ 2 % 100 := by omega
  have e4 : m % 100 = m % 10 ^ 8 % 100 := by omega
  rw [e1, e2, e3, e4]

theorem pad16 (m : Nat) : padDigits 16 m = padDigits 2 (m % 10 ^ 16 / 10 ^ 14 % 100) ++
    padDigits 2 (m % 10 ^ 16 / 10 ^ 12 % 100) ++ padDigits 2 (m % 10 ^ 16 / 10 ^ 10 % 100) ++
    padDigits 2 (m % 10 ^ 16 / 10 ^ 8 % 100) ++ padDigits 2 (m % 10 ^ 16 / 10 ^ 6 % 100) ++
    padDigits 2 (m % 10 ^ 16 / 10 ^ 4 % 100) ++ padDigits 2 (m % 10 ^ 16 / 10 ^ 2 % 100) ++
    padDigits 2 (m % 10 ^ 16 % 100) := by
  rw [pad_step 14, pad_step 12, pad_step 10, pad_step 8, pad_step 6, pad_step 4, pad_step 2,
    pad2_mod (m / 100 / 100 / 100 / 100 / 100 / 100 / 100)]
  have e1 : m / 100 / 100 / 100 / 100 / 100 / 100 / 100 % 100 = m % 10 ^ 16 / 10 ^ 14 % 100 := by omega
  have e2 : m / 100 / 100 / 100 / 100 / 100 / 100 % 100 = m % 10 ^ 16 / 10 ^ 12 % 100 := by omega
  have e3 : m / 100 / 100 / 100 / 100 / 100 % 100 = m % 10 ^ 16 / 10 ^ 10 % 100 := by omega
  have e4 : m / 100 / 100 / 100 / 100 % 100 = m % 10 ^ 16 / 10 ^ 8 % 100 := by omega
  have e5 : m / 100 / 100 / 100 % 100 = m % 10 ^ 16 / 10 ^ 6 % 100 := by omega
  have e6 : m / 100 / 100 % 100 = m % 10 ^ 16 / 10 ^ 4 % 100 := by omega
  have e7 : m / 100 % 100 = m % 10 ^ 16 / 10 ^ 2 % 100 := by omega
  have e8 : m % 100 = m % 10 ^ 16 % 100 := by omega
  rw [e1, e2, e3, e4, e5, e6, e7, e8]

theorem decDigits_length_le (k n : Nat) (hk : 1 ≤ k) (h : n < 10 ^ k) : (decDigits n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    by_cases h10 : n < 10
    · rw [decDigits_lt10 n h10]; simp
    · rw [decDigits]; simp only [h10, ↓reduceIte, List.length_append, List.length_singleton]
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp at h; omega
        · omega
      have := ih (n / 10) hk1 (by rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [Nat.pow_succ] at h; exact h)
      omega

end WNear.Binary.FmtDigits
