import Bridge.Functions.SerdeRead

/-!
# UTF-8 validation as `core::str::from_utf8` does it (M6)

`utf8Ok` is the validator of Rust's `core::str::run_utf8_validation` (the one `from_utf8`, 927,
runs), written on lists: one character at a time, by its first byte

* `00..7F`: one byte;
* `C2..DF`: one continuation byte (`80..BF`);
* `E0..EF`: a second byte in the range the first allows (`ok3`: `A0..BF` after `E0`, `80..9F`
  after `ED`, else `80..BF`), then one continuation byte;
* `F0..F4`: a second byte in its range (`ok4`: `90..BF` after `F0`, `80..8F` after `F4`, else
  `80..BF`), then two continuation bytes;
* anything else is invalid.

The width table 927 reads at 1071704 (`utf8Width`, `widthData_segment`) gives the classes.
-/

namespace WNear.Binary.Utf8

/-- A continuation byte, `80..BF`. -/
def cont (x : UInt8) : Bool := 128 ≤ x.toNat && x.toNat < 192

/-- The first byte of a two-byte character, `C2..DF`. -/
def lead2 (w : UInt8) : Bool := 0xC2 ≤ w.toNat && w.toNat ≤ 0xDF

/-- The first two bytes of a three-byte character (no overlong form, no surrogate). -/
def ok3 (w x : UInt8) : Bool :=
  (w.toNat == 0xE0 && 0xA0 ≤ x.toNat && x.toNat ≤ 0xBF) ||
  (0xE1 ≤ w.toNat && w.toNat ≤ 0xEC && cont x) ||
  (w.toNat == 0xED && 0x80 ≤ x.toNat && x.toNat ≤ 0x9F) ||
  (0xEE ≤ w.toNat && w.toNat ≤ 0xEF && cont x)

/-- The first two bytes of a four-byte character (no overlong form, at most `U+10FFFF`). -/
def ok4 (w x : UInt8) : Bool :=
  (w.toNat == 0xF0 && 0x90 ≤ x.toNat && x.toNat ≤ 0xBF) ||
  (0xF1 ≤ w.toNat && w.toNat ≤ 0xF3 && cont x) ||
  (w.toNat == 0xF4 && 0x80 ≤ x.toNat && x.toNat ≤ 0x8F)

/-- **Rust's UTF-8 validation**, one character at a time. -/
def utf8Ok : List UInt8 → Bool
  | [] => true
  | [w] => w.toNat < 128
  | w :: x :: rest =>
    if w.toNat < 128 then utf8Ok (x :: rest)
    else if lead2 w then cont x && utf8Ok rest
    else if ok3 w x then
      match rest with
      | y :: r => cont y && utf8Ok r
      | [] => false
    else if ok4 w x then
      match rest with
      | y :: z :: r => cont y && cont z && utf8Ok r
      | _ => false
    else false
termination_by l => l.length

theorem utf8Ok_ascii (w : UInt8) (rest : List UInt8) (h : w.toNat < 128) :
    utf8Ok (w :: rest) = utf8Ok rest := by
  cases rest with
  | nil => simp [utf8Ok, h]
  | cons x r => rw [utf8Ok.eq_def]; simp [h]

/-- Every byte below `0x80`: valid. -/
theorem utf8Ok_of_ascii (bs : List UInt8) (h : ∀ b ∈ bs, b.toNat < 128) : utf8Ok bs = true := by
  induction bs with
  | nil => simp [utf8Ok]
  | cons b bs ih =>
    rw [utf8Ok_ascii b bs (h b (by simp))]
    exact ih (fun x hx => h x (by simp [hx]))

end WNear.Binary.Utf8
