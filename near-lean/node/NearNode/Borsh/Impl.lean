import NearNode.Borsh.Spec

/-!
# Borsh fast path

The same combinators as `Spec` over `ByteArray`: encoders append to a unique
buffer and decoders carry an index, so no list is built per byte.
-/

namespace Near.Node.Borsh

namespace Impl

/-- A decoder result: the value and the next position, or an error. -/
inductive Res (α : Type) where
  | ok (a : α) (pos : Nat)
  | err (e : Error)

/-- Appends to a buffer; reads from a buffer at a position. -/
structure Codec (α : Type) where
  put : α → ByteArray → ByteArray
  get : ByteArray → Nat → Res α

@[inline]
def Res.map (f : α → β) : Res α → Res β
  | .ok a p => .ok (f a) p
  | .err e => .err e

def imap (c : Codec α) (f : α → β) (g : β → α) : Codec β where
  put b d := c.put (g b) d
  get d p := (c.get d p).map f

def tryMap (c : Codec α) (f : α → Except Error β) (g : β → α) : Codec β where
  put b d := c.put (g b) d
  get d p :=
    match c.get d p with
    | .ok a q =>
      match f a with
      | .ok b => .ok b q
      | .error e => .err e
    | .err e => .err e

def u8 : Codec UInt8 where
  put x d := d.push x
  get d p := if h : p < d.size then .ok d[p] (p + 1) else .err .eof

@[inline]
private def byteAt (d : ByteArray) (p i : Nat) : UInt64 :=
  (d.get! (p + i)).toUInt64 <<< (8 * i).toUInt64

def u16 : Codec UInt16 where
  put x d := d.push x.toUInt8 |>.push (x >>> 8).toUInt8
  get d p :=
    if p + 2 ≤ d.size then .ok (byteAt d p 0 ||| byteAt d p 1).toUInt16 (p + 2) else .err .eof

def u32 : Codec UInt32 where
  put x d :=
    d.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8
  get d p :=
    if p + 4 ≤ d.size then
      .ok (byteAt d p 0 ||| byteAt d p 1 ||| byteAt d p 2 ||| byteAt d p 3).toUInt32 (p + 4)
    else .err .eof

def u64 : Codec UInt64 where
  put x d :=
    d.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push
              (x >>> 24).toUInt8 |>.push
            (x >>> 32).toUInt8 |>.push
          (x >>> 40).toUInt8 |>.push
        (x >>> 48).toUInt8 |>.push
      (x >>> 56).toUInt8
  get d p :=
    if p + 8 ≤ d.size then
      .ok
        (byteAt d p 0 ||| byteAt d p 1 ||| byteAt d p 2 ||| byteAt d p 3 ||| byteAt d p 4 |||
          byteAt d p 5 |||
          byteAt d p 6 |||
          byteAt d p 7)
        (p + 8)
    else .err .eof

def u128 : Codec U128 where
  put x d := u64.put (UInt64.ofNat (x.val >>> 64)) (u64.put (UInt64.ofNat x.val) d)
  get d p :=
    match u64.get d p with
    | .ok lo q =>
      match u64.get d q with
      | .ok hi r => .ok ⟨hi.toNat <<< 64 ||| lo.toNat⟩ r
      | .err e => .err e
    | .err e => .err e

def unit : Codec Unit where
  put _ d := d
  get _ p := .ok () p

def bool : Codec Bool :=
  tryMap u8
    (fun v => if v == 0 then .ok false else if v == 1 then .ok true else .error (.bool v.toNat))
    (fun b => if b then 1 else 0)

/-- `[u8; n]`. -/
def fixed (n : Nat) : Codec ByteArray where
  put b d := d.append b
  get d p := if p + n ≤ d.size then .ok (d.extract p (p + n)) (p + n) else .err .eof

/-- `Vec<u8>`. -/
def bytes : Codec ByteArray where
  put b d := u32.put b.size.toUInt32 d |>.append b
  get d p :=
    match u32.get d p with
    | .ok n q =>
      if q + n.toNat ≤ d.size then .ok (d.extract q (q + n.toNat)) (q + n.toNat) else .err .eof
    | .err e => .err e

/-- `String`. -/
def string : Codec String where
  put s d := u32.put s.utf8ByteSize.toUInt32 d |>.append s.toUTF8
  get d p :=
    match u32.get d p with
    | .ok n q =>
      if q + n.toNat ≤ d.size then
        match String.fromUTF8? (d.extract q (q + n.toNat)) with
        | some s => .ok s (q + n.toNat)
        | none => .err .utf8
      else .err .eof
    | .err e => .err e

private def getMany (c : Codec α) (d : ByteArray) : Nat → Nat → Array α → Res (Array α)
  | 0, p, acc => .ok acc p
  | n + 1, p, acc =>
    match c.get d p with
    | .ok a q => getMany c d n q (acc.push a)
    | .err e => .err e

def vec (c : Codec α) : Codec (Array α) where
  put a d := a.foldl (fun d x => c.put x d) (u32.put a.size.toUInt32 d)
  get d p :=
    match u32.get d p with
    | .ok n q => getMany c d n.toNat q (Array.mkEmpty (min n.toNat 4096))
    | .err e => .err e

def option (c : Codec α) : Codec (Option α) where
  put
    | none, d => d.push 0
    | some a, d => c.put a (d.push 1)
  get d p :=
    match u8.get d p with
    | .ok 0 q => .ok none q
    | .ok 1 q => (c.get d q).map some
    | .ok t _ => .err (.tag "Option" t.toNat)
    | .err e => .err e

def pair (a : Codec α) (b : Codec β) : Codec (α × β) where
  put x d := b.put x.2 (a.put x.1 d)
  get d p :=
    match a.get d p with
    | .ok x q =>
      match b.get d q with
      | .ok y r => .ok (x, y) r
      | .err e => .err e
    | .err e => .err e

/-- One enum variant: `applies` selects it, `put` writes tag and payload. -/
structure Case (α : Type) where
  tag : UInt8
  applies : α → Bool
  put : α → ByteArray → ByteArray
  get : ByteArray → Nat → Res α

def Case.variant (tag : UInt8) (c : Codec β) (inj : β → α) (prj : α → Option β) : Case α where
  tag
  applies a := (prj a).isSome
  put a d :=
    match prj a with
    | some b => c.put b (d.push tag)
    | none => d
  get d p := (c.get d p).map inj

def enum (what : String) (cases : List (Case α)) : Codec α :=
  let table : Array (Option (Case α)) :=
    cases.foldl (fun t c => t.set! c.tag.toNat (some c)) (Array.replicate 256 none)
  { put := fun a d =>
      match cases.find? (·.applies a) with
      | some c => c.put a d
      | none => d
    get := fun d p =>
      match u8.get d p with
      | .ok t q =>
        match table[t.toNat]! with
        | some c => c.get d q
        | none => .err (.tag what t.toNat)
      | .err e => .err e }

private def ascending (cmp : K → K → Ordering) (es : Array (K × V)) : Bool :=
  (es.zip (es.extract 1 es.size)).all fun (a, b) => cmp a.1 b.1 == .lt

def btreeMap (cmp : K → K → Ordering) (k : Codec K) (v : Codec V) : Codec (Array (K × V)) :=
  let c := vec (pair k v)
  { put := c.put
    get := fun d p =>
      (c.get d p).map fun es => if ascending cmp es then es else Spec.normalize cmp es }

end Impl

/-- Decode a value and require that all input is consumed. -/
def Impl.Codec.decodeAll (c : Impl.Codec α) (d : ByteArray) : Except Error α :=
  match c.get d 0 with
  | .ok a p => if p == d.size then .ok a else .error (.trailing (d.size - p))
  | .err e => .error e

end Near.Node.Borsh
