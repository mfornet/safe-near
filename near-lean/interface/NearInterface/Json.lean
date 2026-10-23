import NearInterface.Raw
import NearInterface.Boundary

/-!
# JSON at the function-call boundary

Contracts built with near-sdk read their arguments with
`serde_json::from_slice` and write return values and cross-contract
arguments with `serde_json::to_vec`. A contract model states its `Parses`
relation on JSON values, not on bytes: `parse` is the byte-level layer,
written to accept exactly what serde_json 1.0.60 accepts, and the helpers
below are serde's derived `Deserialize` for structs and the near-sdk scalar
wrappers.

Acceptance, as serde_json does it and as checked on `contract.wasm`:

* RFC 8259 syntax with whitespace `' ' '\t' '\n' '\r'` around values and
  nothing after the top-level value; no trailing commas, no leading zeros.
* Strings: no raw control characters, the escapes `\" \\ \/ \b \f \n \r \t`
  and `\uXXXX`; surrogates only as a well-formed pair; the raw bytes must be
  UTF-8.
* Numbers are syntax only: no range check, since none of the typed fields we
  decode is a JSON number and ignored values are only scanned.
* No nesting limit: ignored values are skipped iteratively (checked to 129
  levels).
-/

namespace NearInterface.Json

open Wasm.Near

inductive Value
  | null
  | bool (b : Bool)
  /-- A JSON number, kept as its text. -/
  | number (text : String)
  | str (s : String)
  | arr (elements : List Value)
  /-- Members in input order, duplicates included. -/
  | obj (members : List (String × Value))
  deriving Repr, Inhabited

def isWhitespace (b : UInt8) : Bool := b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D

def skipWhitespace (bs : Bytes) : Bytes := bs.dropWhile isWhitespace

def isDigit (b : UInt8) : Bool := 0x30 ≤ b && b ≤ 0x39

def hexValue (b : UInt8) : Option Nat :=
  if 0x30 ≤ b && b ≤ 0x39 then some (b.toNat - 0x30)
  else if 0x61 ≤ b && b ≤ 0x66 then some (b.toNat - 0x61 + 10)
  else if 0x41 ≤ b && b ≤ 0x46 then some (b.toNat - 0x41 + 10)
  else none

/-- Four hex digits of a `\u` escape. -/
def hex4 : Bytes → Option (Nat × Bytes)
  | a :: b :: c :: d :: rest => do
    let a ← hexValue a; let b ← hexValue b; let c ← hexValue c; let d ← hexValue d
    pure (((a * 16 + b) * 16 + c) * 16 + d, rest)
  | _ => none

/-- The code point of a `\u` escape (the input starts after `\u`), joining a
surrogate pair. -/
def unicodeEscape (bs : Bytes) : Option (Char × Bytes) := do
  let (n, rest) ← hex4 bs
  if 0xD800 ≤ n && n < 0xDC00 then
    match rest with
    | 0x5C :: 0x75 :: rest => do
      let (m, rest) ← hex4 rest
      if 0xDC00 ≤ m && m < 0xE000 then
        let cp := 0x10000 + (n - 0xD800) * 0x400 + (m - 0xDC00)
        if cp.isValidChar then pure (Char.ofNat cp, rest)
        else none
      else none
    | _ => none
  else if 0xDC00 ≤ n && n < 0xE000 then none
  else if n.isValidChar then pure (Char.ofNat n, rest)
  else none

/-- The body of a string, after its opening quote. `acc` holds the UTF-8 bytes
decoded so far, in reverse. -/
def stringBody : Bytes → Bytes → Option (String × Bytes)
  | [], _ => none
  | 0x22 :: rest, acc => (String.fromUTF8? ⟨acc.reverse.toArray⟩).map (·, rest)
  | 0x5C :: e :: rest, acc =>
    let simple (b : UInt8) := stringBody rest (b :: acc)
    match e with
    | 0x22 => simple 0x22 | 0x5C => simple 0x5C | 0x2F => simple 0x2F
    | 0x62 => simple 0x08 | 0x66 => simple 0x0C | 0x6E => simple 0x0A
    | 0x72 => simple 0x0D | 0x74 => simple 0x09
    | 0x75 =>
      match unicodeEscape rest with
      | some (c, rest') =>
        if rest'.length < rest.length then
          stringBody rest' ((String.utf8EncodeChar c).reverse ++ acc)
        else none
      | none => none
    | _ => none
  | b :: rest, acc => if b < 0x20 then none else stringBody rest (b :: acc)
termination_by bs => bs.length

def digits (bs : Bytes) : Bytes × Bytes := (bs.takeWhile isDigit, bs.dropWhile isDigit)

/-- `-?(0|[1-9][0-9]*)(\.[0-9]+)?([eE][+-]?[0-9]+)?`, returning the rest. -/
def number (bs : Bytes) : Option (Bytes × Bytes) := do
  let (sign, bs) : Bytes × Bytes := match bs with
    | 0x2D :: rest => ([0x2D], rest)
    | _ => ([], bs)
  let (int, bs) ← (match bs with
    | 0x30 :: rest => some ([0x30], rest)
    | b :: _ => if isDigit b then some (digits bs) else none
    | [] => none : Option (Bytes × Bytes))
  let (frac, bs) ← match bs with
    | 0x2E :: rest =>
      let (ds, rest) := digits rest
      if ds.isEmpty then none else some (0x2E :: ds, rest)
    | _ => some ([], bs)
  let (exp, bs) ← match bs with
    | e :: rest =>
      if e == 0x65 || e == 0x45 then
        let (s, rest) : Bytes × Bytes := match rest with
          | 0x2B :: r => ([0x2B], r)
          | 0x2D :: r => ([0x2D], r)
          | r => ([], r)
        let (ds, rest) := digits rest
        if ds.isEmpty then none else some (e :: s ++ ds, rest)
      else some ([], bs)
    | [] => some ([], bs)
  pure (sign ++ int ++ frac ++ exp, bs)

mutual
/-- One value, after optional whitespace. `fuel` bounds the nesting depth. -/
def value : Nat → Bytes → Option (Value × Bytes)
  | 0, _ => none
  | fuel + 1, bs =>
    match skipWhitespace bs with
    | 0x6E :: 0x75 :: 0x6C :: 0x6C :: rest => some (.null, rest)
    | 0x74 :: 0x72 :: 0x75 :: 0x65 :: rest => some (.bool true, rest)
    | 0x66 :: 0x61 :: 0x6C :: 0x73 :: 0x65 :: rest => some (.bool false, rest)
    | 0x22 :: rest => (stringBody rest []).map fun (s, rest) => (.str s, rest)
    | 0x5B :: rest =>
      match skipWhitespace rest with
      | 0x5D :: rest => some (.arr [], rest)
      | _ => (elements fuel rest []).map fun (vs, rest) => (.arr vs, rest)
    | 0x7B :: rest =>
      match skipWhitespace rest with
      | 0x7D :: rest => some (.obj [], rest)
      | _ => (members fuel rest []).map fun (ms, rest) => (.obj ms, rest)
    | bs => (number bs).bind fun (text, rest) =>
      (String.fromUTF8? ⟨text.toArray⟩).map fun t => (.number t, rest)

/-- Array elements after `[` (or after a `,`), up to the closing `]`. -/
def elements : Nat → Bytes → List Value → Option (List Value × Bytes)
  | 0, _, _ => none
  | fuel + 1, bs, acc => do
    let (v, rest) ← value fuel bs
    match skipWhitespace rest with
    | 0x2C :: rest => elements fuel rest (v :: acc)
    | 0x5D :: rest => pure ((v :: acc).reverse, rest)
    | _ => none

/-- Object members after `{` (or after a `,`), up to the closing `}`. -/
def members : Nat → Bytes → List (String × Value) → Option (List (String × Value) × Bytes)
  | 0, _, _ => none
  | fuel + 1, bs, acc => do
    let (key, rest) ← match skipWhitespace bs with
      | 0x22 :: rest => stringBody rest []
      | _ => none
    let rest ← match skipWhitespace rest with
      | 0x3A :: rest => some rest
      | _ => none
    let (v, rest) ← value fuel rest
    match skipWhitespace rest with
    | 0x2C :: rest => members fuel rest ((key, v) :: acc)
    | 0x7D :: rest => pure (((key, v) :: acc).reverse, rest)
    | _ => none
end

/-- `serde_json::from_slice` acceptance: one value, then only whitespace.
Every nesting level consumes a byte, so the input length is enough fuel. -/
def parse (bs : Bytes) : Option Value :=
  match value (2 * bs.length + 2) bs with
  | some (v, rest) => if skipWhitespace rest = [] then some v else none
  | none => none

/-! ## serde's derived `Deserialize` and near-sdk's scalar wrappers -/

/-- A derived `Deserialize` for a struct with fields `names`: from an object
(each known field at most once, unknown fields ignored; an absent field is
`none`) or from an array of exactly one element per field, in order. -/
def structFields (names : List String) : Value → Option (List (Option Value))
  | .obj ms =>
    if names.all fun n => (ms.filter (·.1 == n)).length ≤ 1 then
      some (names.map fun n => (ms.find? (·.1 == n)).map (·.2))
    else none
  | .arr vs => if vs.length == names.length then some (vs.map some) else none
  | _ => none

/-- A required field. -/
def required (decode : Value → Option α) : Option Value → Option α
  | some v => decode v
  | none => none

/-- An `Option<T>` field: absent or `null` is `None`. -/
def optional (decode : Value → Option α) : Option Value → Option (Option α)
  | none | some .null => some none
  | some v => (decode v).map some

def string : Value → Option String
  | .str s => some s
  | _ => none

def bool : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- `u128::from_str_radix(s, 10)`: an optional `+`, then at least one ASCII digit. -/
def u128OfString (s : String) : Option Nat :=
  let cs := match s.toList with
    | '+' :: rest => rest
    | cs => cs
  if cs.isEmpty || !cs.all Char.isDigit then none
  else
    let n := cs.foldl (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
    if n < 2 ^ 128 then some n else none

/-- near-sdk 3.1.0 `U128`: a JSON string holding a decimal `u128`. -/
def u128 (v : Value) : Option Nat := (string v).bind u128OfString

/-- near-sdk 3.1.0 `ValidAccountId`: a JSON string that is a valid account id. -/
def accountId (v : Value) : Option AccountId := do
  let s ← string v
  if h : validAccountIdBytes s.toUTF8.toList = true then some ⟨s, h⟩ else none

/-! ## Output -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

/-- serde_json's string serialisation: escapes `"`, `\` and control
characters (short forms where they exist, else `\u00XX`), everything else raw. -/
def quote (s : String) : String :=
  let escape (c : Char) : String :=
    match c with
    | '"' => "\\\"" | '\\' => "\\\\"
    | '\n' => "\\n" | '\r' => "\\r" | '\t' => "\\t"
    | '\x08' => "\\b" | '\x0c' => "\\f"
    | c => if c.toNat < 0x20 then "\\u00" ++ String.ofList [hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]
      else String.singleton c
  "\"" ++ String.join (s.toList.map escape) ++ "\""

end NearInterface.Json
