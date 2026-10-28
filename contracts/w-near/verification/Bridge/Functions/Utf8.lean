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

The width table 927 reads at 1071704 gives the first-byte classes (`0` for `80..C1` and
`F5..FF`).

`utf8Ok_iff_isValidUTF8`: `utf8Ok bs` holds exactly when `bs` is valid UTF-8 as Lean's
`ByteArray.IsValidUTF8` defines it, so `fromUTF8?_isSome`: `String.fromUTF8?`, which the model's
`stringBody` uses, succeeds exactly when `utf8Ok`. Both directions go through the numbers of each
character's encoding (`encNat`, `enc_nat`).
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


/-! ## `utf8Ok` is UTF-8 validity

`utf8Ok bs` holds exactly when `bs` is the UTF-8 encoding of a list of characters, that is,
`ByteArray.IsValidUTF8`, the condition of `String.fromUTF8?` (`utf8Ok_iff_isValidUTF8`,
`fromUTF8?_isSome`). The encoding is handled by its numbers (`encNat`): the core's
`String.utf8EncodeChar_eq_cons_cons…` give the bytes as bit operations, and `op1f`… `decide`
those over the 256 bytes. -/

theorem op1f (a : UInt8) : (a &&& 0x1f ||| 0xc0).toNat = 0xC0 + a.toNat % 32 := by
  revert a; exact SerdeRead.uint8_forall (by decide +kernel)
theorem op3f (a : UInt8) : (a &&& 0x3f ||| 0x80).toNat = 0x80 + a.toNat % 64 := by
  revert a; exact SerdeRead.uint8_forall (by decide +kernel)
theorem op0f (a : UInt8) : (a &&& 0x0f ||| 0xe0).toNat = 0xE0 + a.toNat % 16 := by
  revert a; exact SerdeRead.uint8_forall (by decide +kernel)
theorem op07 (a : UInt8) : (a &&& 0x07 ||| 0xf0).toNat = 0xF0 + a.toNat % 8 := by
  revert a; exact SerdeRead.uint8_forall (by decide +kernel)

theorem shr8 (v : UInt32) (k : Nat) (hk : k < 32) :
    ((v >>> UInt32.ofNat k).toUInt8).toNat = v.toNat / 2 ^ k % 256 := by
  rw [UInt32.toNat_toUInt8, UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
  simp [Nat.mod_eq_of_lt hk]

/-- The UTF-8 encoding of the code point `v`, as numbers. -/
def encNat (v : Nat) : List Nat :=
  if v < 0x80 then [v]
  else if v < 0x800 then [0xC0 + v / 64, 0x80 + v % 64]
  else if v < 0x10000 then [0xE0 + v / 4096, 0x80 + v / 64 % 64, 0x80 + v % 64]
  else [0xF0 + v / 262144, 0x80 + v / 4096 % 64, 0x80 + v / 64 % 64, 0x80 + v % 64]

theorem valid_nat (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  rcases c.valid with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem toNat_ofNat' (n : Nat) (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux, Char.toNat]

theorem enc_nat (c : Char) : (String.utf8EncodeChar c).map UInt8.toNat = encNat c.toNat := by
  have e0 : c.val.toUInt8.toNat = c.val.toNat % 256 := UInt32.toNat_toUInt8 _
  have e6 := shr8 c.val 6 (by decide)
  have e12 := shr8 c.val 12 (by decide)
  have e18 := shr8 c.val 18 (by decide)
  have hlt := valid_nat c
  rw [show c.toNat = c.val.toNat from rfl] at hlt ⊢
  simp only [UInt32.reduceOfNat] at e6 e12 e18
  rcases Char.utf8Size_eq c with h | h | h | h
  · rw [String.utf8EncodeChar_eq_singleton h]
    have hv := Char.utf8Size_eq_one_iff.mp h
    simp only [UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hv
    simp only [List.map_cons, List.map_nil, encNat, Char.toNat, e0]
    rw [if_pos (by omega)]; simp only [List.cons.injEq, and_true]; omega
  · rw [String.utf8EncodeChar_eq_cons_cons h]
    have hv := Char.utf8Size_eq_two_iff.mp h
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hv
    simp only [List.map_cons, List.map_nil, op1f, op3f, e0, e6, encNat, Char.toNat]
    rw [if_neg (by omega), if_pos (by omega), show (2:Nat) ^ 6 = 64 from rfl]
    simp only [List.cons.injEq, and_true]; constructor <;> omega
  · rw [String.utf8EncodeChar_eq_cons_cons_cons h]
    have hv := Char.utf8Size_eq_three_iff.mp h
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hv
    simp only [List.map_cons, List.map_nil, op0f, op3f, e0, e6, e12, encNat, Char.toNat]
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), show (2:Nat) ^ 6 = 64 from rfl,
      show (2:Nat) ^ 12 = 4096 from rfl]
    simp only [List.cons.injEq, and_true]; refine ⟨?_, ?_, ?_⟩ <;> omega
  · rw [String.utf8EncodeChar_eq_cons_cons_cons_cons h]
    have hv := Char.utf8Size_eq_four_iff.mp h
    simp only [UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le, UInt32.reduceToNat] at hv
    simp only [List.map_cons, List.map_nil, op07, op3f, e0, e6, e12, e18, encNat, Char.toNat]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), show (2:Nat) ^ 6 = 64 from rfl,
      show (2:Nat) ^ 12 = 4096 from rfl, show (2:Nat) ^ 18 = 262144 from rfl]
    simp only [List.cons.injEq, and_true]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

theorem map_toNat_inj {l l' : List UInt8} (h : l.map UInt8.toNat = l'.map UInt8.toNat) : l = l' :=
  List.map_injective_iff.mpr (fun _ _ e => UInt8.toNat_inj.mp e) h

/-- One character's encoding, then `rest`: valid exactly when `rest` is. -/
theorem utf8Ok_enc (c : Char) (rest : List UInt8) :
    utf8Ok (String.utf8EncodeChar c ++ rest) = utf8Ok rest := by
  have he := enc_nat c
  have hlt := valid_nat c
  generalize c.toNat = v at he hlt
  generalize String.utf8EncodeChar c = l at he
  simp only [encNat] at he
  split at he
  · rcases l with _ | ⟨w, _ | ⟨_, _⟩⟩ <;> simp at he
    rw [List.singleton_append, utf8Ok_ascii w rest (by omega)]
  split at he
  · rcases l with _ | ⟨w, _ | ⟨x, _ | ⟨_, _⟩⟩⟩ <;> simp at he
    obtain ⟨hw, hx⟩ := he
    simp only [List.cons_append, List.nil_append]
    have h128 : ¬ w.toNat < 128 := by omega
    have hl : lead2 w = true := by simp only [lead2, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hc : cont x = true := by simp only [cont, Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [utf8Ok.eq_def]
    simp only [h128, hl, hc, ↓reduceIte, Bool.true_and]
  split at he
  · rcases l with _ | ⟨w, _ | ⟨x, _ | ⟨y, _ | ⟨_, _⟩⟩⟩⟩ <;> simp at he
    obtain ⟨hw, hx, hy⟩ := he
    simp only [List.cons_append, List.nil_append]
    have h128 : ¬ w.toNat < 128 := by omega
    have hl : lead2 w = false := by
      simp only [lead2, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have h3 : ok3 w x = true := by
      simp only [ok3, cont, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rcases hlt with hlt | hlt <;> omega
    have hc : cont y = true := by simp only [cont, Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [utf8Ok.eq_def]
    simp only [h128, hl, h3, hc, ↓reduceIte, Bool.true_and, Bool.false_eq_true]
  · rcases l with _ | ⟨w, _ | ⟨x, _ | ⟨y, _ | ⟨z, _ | ⟨_, _⟩⟩⟩⟩⟩ <;> simp at he
    obtain ⟨hw, hx, hy, hz⟩ := he
    simp only [List.cons_append, List.nil_append]
    have h128 : ¬ w.toNat < 128 := by omega
    have hl : lead2 w = false := by
      simp only [lead2, Bool.and_eq_false_iff, decide_eq_false_iff_not]; omega
    have h3 : ok3 w x = false := by
      simp only [ok3, cont, Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne,
        ne_eq]
      omega
    have h4 : ok4 w x = true := by
      simp only [ok4, cont, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rcases hlt with hlt | hlt <;> omega
    have hcy : cont y = true := by simp only [cont, Bool.and_eq_true, decide_eq_true_eq]; omega
    have hcz : cont z = true := by simp only [cont, Bool.and_eq_true, decide_eq_true_eq]; omega
    rw [utf8Ok.eq_def]
    simp only [h128, hl, h3, h4, hcy, hcz, ↓reduceIte, Bool.true_and, Bool.false_eq_true]

/-- Valid encodings pass `utf8Ok`. -/
theorem utf8Ok_flatMap (m : List Char) : utf8Ok (m.flatMap String.utf8EncodeChar) = true := by
  induction m with
  | nil => simp [utf8Ok]
  | cons c m ih => rw [List.flatMap_cons, utf8Ok_enc, ih]

/-- The character of a valid code point `v` with the given bytes. -/
theorem enc_of (v : Nat) (hv : v.isValidChar) (l : List UInt8) (h : l.map UInt8.toNat = encNat v) :
    String.utf8EncodeChar (Char.ofNat v) = l := by
  apply map_toNat_inj
  rw [enc_nat, toNat_ofNat' v hv, h]

theorem cont_nat {x : UInt8} (h : cont x = true) : 128 ≤ x.toNat ∧ x.toNat < 192 := by
  simpa [cont] using h

/-- `utf8Ok` bytes are a valid encoding. -/
theorem flatMap_of_utf8Ok (bs : List UInt8) (h : utf8Ok bs = true) :
    ∃ m : List Char, bs = m.flatMap String.utf8EncodeChar := by
  induction bs using utf8Ok.induct with
  | case1 => exact ⟨[], rfl⟩
  | case2 w =>
    simp only [utf8Ok, decide_eq_true_eq] at h
    exact ⟨[Char.ofNat w.toNat], by
      rw [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        enc_of _ (Or.inl (by omega)) [w] (by simp [encNat, h])]⟩
  | case3 w x rest hw ih =>
    rw [utf8Ok_ascii w _ hw] at h
    obtain ⟨m, hm⟩ := ih h
    refine ⟨Char.ofNat w.toNat :: m, ?_⟩
    rw [List.flatMap_cons, ← hm, enc_of _ (Or.inl (by omega)) [w] (by simp [encNat, hw])]
    rfl
  | case4 w x rest hw h2 ih =>
    rw [utf8Ok.eq_def] at h
    simp only [hw, h2, ↓reduceIte, Bool.and_eq_true] at h
    obtain ⟨hx, hr⟩ := h
    obtain ⟨m, hm⟩ := ih hr
    have hx' := cont_nat hx
    simp only [lead2, Bool.and_eq_true, decide_eq_true_eq] at h2
    refine ⟨Char.ofNat ((w.toNat % 32) * 64 + x.toNat % 64) :: m, ?_⟩
    rw [List.flatMap_cons, ← hm, enc_of _ (Or.inl (by omega)) [w, x] (by
      simp only [List.map_cons, List.map_nil, encNat]
      rw [if_neg (by omega), if_pos (by omega)]
      simp only [List.cons.injEq, and_true]; constructor <;> omega)]
    rfl
  | case5 w x hw h2 h3 y r ih =>
    rw [utf8Ok.eq_def] at h
    simp only [hw, h2, h3, ↓reduceIte, Bool.and_eq_true, Bool.false_eq_true] at h
    obtain ⟨hy, hr⟩ := h
    obtain ⟨m, hm⟩ := ih hr
    have hy' := cont_nat hy
    simp only [ok3, cont, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h3
    simp only [lead2, Bool.and_eq_true, decide_eq_true_eq, not_and, Nat.not_le] at h2
    refine ⟨Char.ofNat ((w.toNat % 16) * 4096 + (x.toNat % 64) * 64 + y.toNat % 64) :: m, ?_⟩
    rw [List.flatMap_cons, ← hm, enc_of _ (by unfold Nat.isValidChar; omega) [w, x, y] (by
      simp only [List.map_cons, List.map_nil, encNat]
      rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]
      simp only [List.cons.injEq, and_true]; refine ⟨?_, ?_, ?_⟩ <;> omega)]
    rfl
  | case6 w x hw h2 h3 =>
    rw [utf8Ok.eq_def] at h
    simp [hw, h2, h3] at h
  | case7 w x hw h2 h3 h4 y z r ih =>
    rw [utf8Ok.eq_def] at h
    simp only [hw, h2, h3, h4, ↓reduceIte, Bool.and_eq_true, Bool.false_eq_true] at h
    obtain ⟨⟨hy, hz⟩, hr⟩ := h
    obtain ⟨m, hm⟩ := ih hr
    have hy' := cont_nat hy
    have hz' := cont_nat hz
    simp only [ok4, cont, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h4
    refine ⟨Char.ofNat ((w.toNat % 8) * 262144 + (x.toNat % 64) * 4096 + (y.toNat % 64) * 64 + z.toNat % 64) :: m, ?_⟩
    rw [List.flatMap_cons, ← hm, enc_of _ (by unfold Nat.isValidChar; omega) [w, x, y, z] (by
      simp only [List.map_cons, List.map_nil, encNat]
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      simp only [List.cons.injEq, and_true]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega)]
    rfl
  | case8 w x rest hw h2 h3 h4 hne =>
    rw [utf8Ok.eq_def] at h
    simp only [hw, h2, h3, h4, ↓reduceIte, Bool.false_eq_true] at h
  | case9 w x rest hw h2 h3 h4 =>
    rw [utf8Ok.eq_def] at h
    simp [hw, h2, h3, h4] at h

theorem mk_toArray (l : List UInt8) : (⟨l.toArray⟩ : ByteArray) = l.toByteArray := by
  apply ByteArray.ext; simp

/-- **`utf8Ok` is UTF-8 validity**, the condition of `String.fromUTF8?`. -/
theorem utf8Ok_iff_isValidUTF8 (bs : List UInt8) :
    utf8Ok bs = true ↔ ByteArray.IsValidUTF8 ⟨bs.toArray⟩ := by
  rw [mk_toArray]
  constructor
  · intro h
    obtain ⟨m, hm⟩ := flatMap_of_utf8Ok bs h
    exact ⟨m, by rw [hm]; rfl⟩
  · rintro ⟨m, hm⟩
    have e : bs = m.flatMap String.utf8EncodeChar := List.toByteArray_inj.mp hm
    rw [e]
    exact utf8Ok_flatMap m

/-- `String.fromUTF8?` (the model's decoding of a string) succeeds exactly when `utf8Ok`. -/
theorem fromUTF8?_isSome (bs : List UInt8) : (String.fromUTF8? ⟨bs.toArray⟩).isSome = utf8Ok bs := by
  by_cases h : ByteArray.IsValidUTF8 ⟨bs.toArray⟩
  · rw [(utf8Ok_iff_isValidUTF8 bs).mpr h]; simp [String.fromUTF8?, h]
  · have : utf8Ok bs = false := by
      cases e : utf8Ok bs
      · rfl
      · exact absurd ((utf8Ok_iff_isValidUTF8 bs).mp e) h
    rw [this]; simp [String.fromUTF8?, h]

end WNear.Binary.Utf8
