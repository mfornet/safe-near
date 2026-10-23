/-!
# Borsh reference semantics

Encoders and decoders over `List UInt8`, written for clarity and proofs rather
than speed. `Impl` is the fast path over `ByteArray`; `NearNode.Borsh` builds
every codec once from combinators and keeps both interpretations together, so
an equivalence theorem per combinator would cover every type. Until it is
proved, `node-conformance-types` checks that they agree.

Decoders reject truncated input, invalid `bool`/`Option`/enum tags and invalid
UTF-8; `decodeAll` also rejects trailing bytes.
-/

namespace Near.Node.Borsh

/-- Decoding failures. -/
inductive Error where
  | eof
  | tag (what : String) (value : Nat)
  | bool (value : Nat)
  | utf8
  | invalid (what : String)
  | trailing (count : Nat)
  deriving Repr, BEq, Inhabited

/-- An unsigned 128-bit integer. Decoders produce values below `2^128`; encoding wraps. -/
structure U128 where
  val : Nat
  deriving BEq, Hashable, Inhabited, Repr, Ord

instance : OfNat U128 n :=
  ⟨⟨n⟩⟩

/-- `u128::MAX`. -/
def U128.max : U128 :=
  ⟨2 ^ 128 - 1⟩

namespace Spec

/-- An encoder and a decoder that returns the unread suffix. -/
structure Codec (α : Type) where
  enc : α → List UInt8
  dec : List UInt8 → Except Error (α × List UInt8)

/-- Little-endian bytes of `n` in `width` bytes. -/
def leBytes (width n : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (n / 256 ^ i)

/-- The value of little-endian bytes. -/
def leValue (bytes : List UInt8) : Nat :=
  bytes.foldr (fun b acc => acc * 256 + b.toNat) 0

/-- The first `n` bytes and the rest. -/
def take (n : Nat) (l : List UInt8) : Except Error (List UInt8 × List UInt8) :=
  let (a, b) := l.splitAt n
  if a.length < n then .error .eof else .ok (a, b)

/-- A little-endian unsigned integer of `width` bytes. -/
def nat (width : Nat) : Codec Nat where
  enc n := leBytes width n
  dec l := do
    let (b, r) ← take width l
    pure (leValue b, r)

def imap (c : Codec α) (f : α → β) (g : β → α) : Codec β where
  enc b := c.enc (g b)
  dec l := do
    let (a, r) ← c.dec l
    pure (f a, r)

/-- Like `imap`, with a decoder that may reject. -/
def tryMap (c : Codec α) (f : α → Except Error β) (g : β → α) : Codec β where
  enc b := c.enc (g b)
  dec l := do
    let (a, r) ← c.dec l
    pure (← f a, r)

def u8 : Codec UInt8 :=
  imap (nat 1) UInt8.ofNat UInt8.toNat

def u16 : Codec UInt16 :=
  imap (nat 2) UInt16.ofNat UInt16.toNat

def u32 : Codec UInt32 :=
  imap (nat 4) UInt32.ofNat UInt32.toNat

def u64 : Codec UInt64 :=
  imap (nat 8) UInt64.ofNat UInt64.toNat

def u128 : Codec U128 :=
  imap (nat 16) (fun n => ⟨n⟩) U128.val

def unit : Codec Unit where
  enc _ := []
  dec l := .ok ((), l)

/-- `bool` accepts only 0 and 1. -/
def bool : Codec Bool :=
  tryMap u8
    (fun v => if v == 0 then .ok false else if v == 1 then .ok true else .error (.bool v.toNat))
    (fun b => if b then 1 else 0)

/-- `[u8; n]`. -/
def fixed (n : Nat) : Codec ByteArray where
  enc b := b.toList
  dec l := do
    let (a, r) ← take n l
    pure (ByteArray.mk a.toArray, r)

/-- `Vec<u8>`: a `u32` length, then the bytes. -/
def bytes : Codec ByteArray where
  enc b := leBytes 4 b.size ++ b.toList
  dec l := do
    let (n, r) ← (nat 4).dec l
    let (a, r) ← take n r
    pure (ByteArray.mk a.toArray, r)

/-- Well-formed UTF-8 (Unicode, Table 3-7). -/
def utf8Valid : List UInt8 → Bool
  | [] => true
  | b :: r =>
    if b < 0x80 then utf8Valid r
    else
      if 0xC2 ≤ b && b ≤ 0xDF then
        match r with
        | c :: r' => (0x80 ≤ c && c ≤ 0xBF) && utf8Valid r'
        | _ => false
      else
        if 0xE0 ≤ b && b ≤ 0xEF then
          match r with
          | c :: d :: r' =>
            (if b == 0xE0 then 0xA0 ≤ c && c ≤ 0xBF
              else if b == 0xED then 0x80 ≤ c && c ≤ 0x9F else 0x80 ≤ c && c ≤ 0xBF) &&
              (0x80 ≤ d && d ≤ 0xBF) &&
              utf8Valid r'
          | _ => false
        else
          if 0xF0 ≤ b && b ≤ 0xF4 then
            match r with
            | c :: d :: e :: r' =>
              (if b == 0xF0 then 0x90 ≤ c && c ≤ 0xBF
                else if b == 0xF4 then 0x80 ≤ c && c ≤ 0x8F else 0x80 ≤ c && c ≤ 0xBF) &&
                (0x80 ≤ d && d ≤ 0xBF) &&
                (0x80 ≤ e && e ≤ 0xBF) &&
                utf8Valid r'
            | _ => false
          else false

/-- `String`: a `u32` byte length, then valid UTF-8. -/
def string : Codec String where
  enc s := leBytes 4 s.utf8ByteSize ++ s.toUTF8.toList
  dec l := do
    let (n, r) ← (nat 4).dec l
    let (a, r) ← take n r
    if !utf8Valid a then
      throw .utf8
    match String.fromUTF8? (ByteArray.mk a.toArray) with
    | some s =>
      pure (s, r)
    | none =>
      throw .utf8

def decodeMany (c : Codec α) : Nat → List UInt8 → Except Error (List α × List UInt8)
  | 0, l => .ok ([], l)
  | n + 1, l => do
    let (a, r) ← c.dec l
    let (as, r) ← decodeMany c n r
    pure (a :: as, r)

/-- `Vec<T>`: a `u32` count, then the elements. -/
def vec (c : Codec α) : Codec (Array α) where
  enc a := leBytes 4 a.size ++ a.toList.flatMap c.enc
  dec l := do
    let (n, r) ← (nat 4).dec l
    let (as, r) ← decodeMany c n r
    pure (as.toArray, r)

/-- `Option<T>`: tag 0 or 1. -/
def option (c : Codec α) : Codec (Option α) where
  enc
    | none => [0]
    | some a => 1 :: c.enc a
  dec l := do
    let (t, r) ← u8.dec l
    if t == 0 then
      pure (none, r)
    else if t == 1 then
      let (a, r) ← c.dec r
      pure (some a, r)
    else
      throw (.tag "Option" t.toNat)

/-- Concatenation, used for tuples and structs. -/
def pair (a : Codec α) (b : Codec β) : Codec (α × β) where
  enc x := a.enc x.1 ++ b.enc x.2
  dec l := do
    let (x, r) ← a.dec l
    let (y, r) ← b.dec r
    pure ((x, y), r)

/-- One enum variant: `enc` returns the payload bytes if the value belongs to it. -/
structure Case (α : Type) where
  tag : UInt8
  enc : α → Option (List UInt8)
  dec : List UInt8 → Except Error (α × List UInt8)

def Case.variant (tag : UInt8) (c : Codec β) (inj : β → α) (prj : α → Option β) : Case α where
  tag
  enc a := (prj a).map c.enc
  dec l := do
    let (b, r) ← c.dec l
    pure (inj b, r)

/-- An enum: a `u8` tag selects the variant. Unlisted tags are rejected. -/
def enum (what : String) (cases : List (Case α)) : Codec α where
  enc a := ((cases.findSome? fun c => (c.enc a).map (c.tag :: ·)).getD [])
  dec l := do
    let (t, r) ← u8.dec l
    match cases.find? (·.tag == t) with
    | some c =>
      c.dec r
    | none =>
      throw (.tag what t.toNat)

/-- Maps are a sorted vector of pairs. Duplicate keys keep the last value. -/
def normalize (cmp : K → K → Ordering) (entries : Array (K × V)) : Array (K × V) :=
  entries.foldl (init := #[]) fun acc e =>
    match acc.findIdx? (fun x => cmp x.1 e.1 != .lt) with
    | none => acc.push e
    | some i =>
      if (acc[i]?.map fun x => cmp x.1 e.1) == some .eq then acc.set! i e else acc.insertIdx! i e

/-- `BTreeMap<K, V>`: a vector of pairs, collected into a sorted map without an order check. -/
def btreeMap (cmp : K → K → Ordering) (k : Codec K) (v : Codec V) : Codec (Array (K × V)) :=
  let c := vec (pair k v)
  { enc := c.enc
    dec := fun l => do
      let (es, r) ← c.dec l
      pure (normalize cmp es, r) }

end Spec

/-- Decode a value and require that all input is consumed. -/
def Spec.Codec.decodeAll (c : Spec.Codec α) (l : List UInt8) : Except Error α := do
  let (a, r) ← c.dec l
  if r.isEmpty then
    pure a
  else
    throw (.trailing r.length)

end Near.Node.Borsh
