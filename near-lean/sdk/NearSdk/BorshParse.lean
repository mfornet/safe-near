import NearSdk.Borsh

/-!
# Borsh parsing

Partial parsers for the Borsh fragment near-sdk state uses, each returning the
value and the unread bytes, and the facts that they invert the encoders.
-/

namespace NearSdk.BorshParse
open NearSdk.Borsh

abbrev Parser (α : Type) := Bytes → Option (α × Bytes)

def take (count : Nat) : Parser Bytes := fun input =>
  if count ≤ input.length then some (input.take count, input.drop count) else none

/-- A fixed-width little-endian natural number. -/
def natural (width : Nat) : Parser Nat := fun input => do
  let (bytes, rest) ← take width input
  pure (fromLE bytes, rest)

/-- Borsh `Vec<u8>`. -/
def bytes : Parser Bytes := fun input => do
  let (count, rest) ← natural 4 input
  take count rest

/-- Borsh `String`: the bytes must be UTF-8. -/
def text : Parser String := fun input => do
  let (raw, rest) ← bytes input
  let value ← String.fromUTF8? ⟨raw.toArray⟩
  pure (value, rest)

/-- Borsh `Option<String>`. -/
def optionalText : Parser (Option String) := fun input => do
  match input with
  | 0 :: rest => pure (none, rest)
  | 1 :: rest => do
    let (value, tail) ← text rest
    pure (some value, tail)
  | _ => none

/-- The whole input is one value. -/
def exact (parser : Parser α) (input : Bytes) : Option α := do
  let (value, rest) ← parser input
  if rest.isEmpty then some value else none

theorem borsh_take_append (width : Nat) (bytes rest : Bytes)
    (h : bytes.length = width) :
    take width (bytes ++ rest) = some (bytes, rest) := by
  simp [take, h]

theorem natural_encode (width n : Nat) (rest : Bytes) (h : n < 256 ^ width) :
    natural width (leBytes width n ++ rest) = some (n, rest) := by
  simp [natural, borsh_take_append, fromLE_leBytes, h]

theorem exact_natural_encode (width n : Nat) (h : n < 256 ^ width) :
    exact (natural width) (leBytes width n) = some n := by
  have hdecode := natural_encode width n [] h
  simpa [exact] using congrArg
    (fun result => result.bind fun parsed =>
      if parsed.2 = [] then some parsed.1 else none) hdecode

theorem bytes_encode (bytes rest : Bytes) (h : bytes.length < 256 ^ 4) :
    BorshParse.bytes (Borsh.bytes bytes ++ rest) = some (bytes, rest) := by
  simp [BorshParse.bytes, Borsh.bytes, u32, List.append_assoc,
    natural_encode, borsh_take_append, h]

end NearSdk.BorshParse
