import Model.Args

/-!
# The canonical arguments of `ft_balance_of` parse (M6, the model's side)

near-sdk callers send `ft_balance_of` the bytes `{"account_id":"<a>"}`: serde_json's
serialisation of the arguments struct (an account id needs no escape: its bytes are
`[a-z0-9._-]`). `decode_balanceOfArgs`: the model's `Call.decode` reads them as the call
`ftBalanceOf a`, through every layer of `NearInterface.Json` (`parse`, `structFields`,
`required account`). This is the input the accepting direction of the parser's contract is
first proved on.

* `stringBody_plain`: a JSON string body of bytes `≥ 0x20` other than `"` and `\` is those
  bytes, up to the closing quote.
* `accountIdFormat_plain`: an account id's bytes are plain.
* `parse_balanceOfArgs`, `decode_balanceOfArgs`.
-/

namespace WNear.BalanceOfArgs

open NearInterface.Json Wasm.Near

/-- A byte a JSON string body takes as itself: not a control character, `"` or `\`. -/
def Plain (b : UInt8) : Prop := 0x20 ≤ b ∧ b ≠ 0x22 ∧ b ≠ 0x5C

theorem stringBody_cons_plain (b : UInt8) (rest acc : List UInt8) (hb : Plain b) :
    stringBody (b :: rest) acc = stringBody rest (b :: acc) := by
  obtain ⟨h1, h2, h3⟩ := hb
  have h1' : ¬ b < 0x20 := by
    intro h; exact absurd h1 (UInt8.not_le.mpr h)
  rw [stringBody.eq_def]
  split
  · rename_i heq; simp at heq
  · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h2
  · rename_i heq; simp only [List.cons.injEq] at heq; exact absurd heq.1 h3
  · rename_i heq; simp only [List.cons.injEq] at heq; obtain ⟨rfl, rfl⟩ := heq; simp [h1']

/-- A plain string body, then the closing quote. -/
theorem stringBody_plain (bs rest acc : List UInt8) (h : ∀ b ∈ bs, Plain b) :
    stringBody (bs ++ 0x22 :: rest) acc = some (String.fromUTF8? ⟨(acc.reverse ++ bs).toArray⟩, rest) := by
  induction bs generalizing acc with
  | nil =>
    simp only [List.nil_append, List.append_nil]
    rw [stringBody.eq_def]
    rfl
  | cons b bs ih =>
    rw [List.cons_append, stringBody_cons_plain b _ acc (h b (List.mem_cons_self ..)),
      ih (b :: acc) (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    simp

theorem plain_of (b : UInt8) (h : 45 ≤ b.toNat ∧ b.toNat ≤ 122 ∧ b.toNat ≠ 92) : Plain b := by
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt8.le_iff_toNat_le]; simp; omega
  · intro e; rw [e] at h; simp at h
  · intro e; rw [e] at h; simp at h

/-- An account id's bytes are plain. -/
theorem accountIdFormat_plain (p : Bool) (bs : List UInt8) (h : accountIdFormat p bs = true) :
    ∀ b ∈ bs, Plain b := by
  induction bs generalizing p with
  | nil => simp
  | cons b bs ih =>
    simp only [accountIdFormat] at h
    intro x hx
    split_ifs at h with h1 h2
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h1
        exact plain_of _ (by omega)
      · exact ih _ h x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h2
        exact plain_of _ (by omega)
      · exact ih true (by cases p <;> simp_all) x hx

/-- `account_id`. -/
def keyBytes : List UInt8 := [97, 99, 99, 111, 117, 110, 116, 95, 105, 100]

/-- `{"account_id":"<a>"}`. -/
def balanceOfArgs (a : AccountId) : List UInt8 :=
  0x7B :: 0x22 :: (keyBytes ++ 0x22 :: 0x3A :: 0x22 :: (a.val.toUTF8.toList ++ [0x22, 0x7D]))

theorem skip_of_not (b : UInt8) (rest : List UInt8) (h : isWhitespace b = false) :
    skipWhitespace (b :: rest) = b :: rest := by
  simp [skipWhitespace, h]

theorem fromUTF8_toUTF8 (s : String) : String.fromUTF8? ⟨s.toUTF8.toList.toArray⟩ = some s := by
  rw [Wasm.ByteEncoding.byteArray_of_toList, Wasm.ByteEncoding.string_fromUTF8_toUTF8]

theorem account_plain (a : AccountId) : ∀ b ∈ a.val.toUTF8.toList, Plain b := by
  have h := a.toNear.property
  simp only [validAccountIdBytes, Bool.and_eq_true] at h
  exact accountIdFormat_plain true _ h.2

theorem key_plain : ∀ b ∈ keyBytes, Plain b := by
  intro b hb
  simp only [keyBytes, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact plain_of _ (by decide)

/-- `{"account_id":"<A>"}` for plain UTF-8 bytes `A` of the string `s`. -/
theorem parse_args (A : List UInt8) (s : String) (hp : ∀ b ∈ A, Plain b)
    (hs : String.fromUTF8? ⟨A.toArray⟩ = some s) :
    parse (0x7B :: 0x22 :: (keyBytes ++ 0x22 :: 0x3A :: 0x22 :: (A ++ [0x22, 0x7D]))) =
      some (.obj [(some "account_id", .str s)]) := by
  have hsK : stringBody (keyBytes ++ 0x22 :: 0x3A :: 0x22 :: (A ++ [0x22, 0x7D])) [] =
      some (some "account_id", 0x3A :: 0x22 :: (A ++ [0x22, 0x7D])) := by
    rw [stringBody_plain _ _ _ key_plain]; rfl
  have hsA : stringBody (A ++ [0x22, 0x7D]) [] = some (some s, [0x7D]) := by
    rw [show A ++ [0x22, 0x7D] = A ++ 0x22 :: [0x7D] from rfl, stringBody_plain _ _ _ hp]
    simp [hs]
  unfold parse
  obtain ⟨k, hk⟩ : ∃ k, 2 * (0x7B :: 0x22 :: (keyBytes ++ 0x22 :: 0x3A :: 0x22 :: (A ++ [0x22, 0x7D]))).length + 2
      = k + 3 := ⟨2 * (0x7B :: 0x22 :: (keyBytes ++ 0x22 :: 0x3A :: 0x22 :: (A ++ [0x22, 0x7D]))).length - 1,
        by simp; omega⟩
  rw [hk]
  rw [value.eq_def]
  simp only [skip_of_not 0x7B _ rfl, skip_of_not 0x22 _ rfl]
  rw [members.eq_def]
  simp only [skip_of_not 0x22 _ rfl, hsK, skip_of_not 0x3A _ rfl, Option.bind_eq_bind, Option.bind_some]
  rw [value.eq_def]
  simp only [skip_of_not 0x22 _ rfl, hsA, Option.map_some]
  simp [skipWhitespace, isWhitespace]

/-- The canonical arguments, as bytes: `{"account_id":"<a>"}`. -/
theorem balanceOfArgs_eq (a : AccountId) :
    balanceOfArgs a =
      0x7B :: 0x22 :: (keyBytes ++ 0x22 :: 0x3A :: 0x22 :: (a.val.toUTF8.toList ++ [0x22, 0x7D])) :=
  rfl

/-- **The canonical arguments parse** as the object `{"account_id": a}`. -/
theorem parse_balanceOfArgs (a : AccountId) :
    parse (balanceOfArgs a) = some (.obj [(some "account_id", .str a.val)]) := by
  rw [balanceOfArgs_eq]
  exact parse_args _ _ (account_plain a) (fromUTF8_toUTF8 a.val)

/-- **The canonical arguments are the call `ftBalanceOf a`**: `Call.decode` reads them as it. -/
theorem decode_balanceOfArgs (a : AccountId) :
    Call.decode "ft_balance_of" (balanceOfArgs a) = some (.ftBalanceOf a) := by
  simp only [Call.decode, parse_balanceOfArgs, Option.bind_some, structFields]
  have hv : validAccountIdBytes a.val.toUTF8.toList = true := a.toNear.property
  simp only [String.toUTF8_eq_toByteArray] at hv
  simp [required, account, accountId, string, hv, AccountId.ofNear]

theorem parses_balanceOfArgs (a : AccountId) :
    Parses "ft_balance_of" (balanceOfArgs a) (.ftBalanceOf a) :=
  decode_balanceOfArgs a

end WNear.BalanceOfArgs
