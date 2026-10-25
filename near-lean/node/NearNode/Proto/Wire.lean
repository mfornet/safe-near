/-!
# Protocol Buffers wire format

A small generic codec for the proto3 wire format, in pure Lean: varints, zigzag, fixed-width
values, length-delimited fields, tags, packed and unpacked repeated fields, unknown-field skipping.
Messages are decoded in two steps. `parseFields` frames a message body into `Field`s and checks
everything the parser of `protobuf` 3.0.2 (the version nearcore pins) checks on the way, whether the
field is known or not; the typed readers (`Varint.toU32`, `readString`, ...) then interpret the
fields a message type knows. Where `protobuf` reads a known field with a rule that differs from the
generic one (a `uint32` has at most five bytes, a `bytes` length is a `u32`), the reader applies it.

Behaviour that matters to compatibility, all from `protobuf/src/coded_input_stream`:

* a tag is a `u32` varint, its wire type is at most 5 and its field number is not 0;
* a varint has at most ten bytes and the tenth is 0 or 1; a `u32` varint has at most five bytes and
  the fifth is at most `0x0f`;
* a group (wire type 3) is skipped up to its end marker, and a group inside a group is an error; a
  lone end marker is an error;
* a known field with another wire type is an unknown field; the last occurrence of a singular field
  wins and a repeated field accepts packed and unpacked occurrences;
* strings are valid UTF-8.
-/

namespace Near.Node.Proto

/-- Why a message does not decode. -/
inductive Error where
  | eof
  | varint
  | tag
  | wireType
  | length
  | utf8
  | value (what : String)
  | missing (what : String)
  | other (what : String)
  deriving Repr, BEq, Inhabited

/-- A decoded varint with the shape of its encoding, which the narrower integer types check. -/
structure Varint where
  val : UInt64
  /-- Number of bytes of the encoding. -/
  width : Nat
  /-- The last byte of the encoding. -/
  last : UInt8
  deriving Repr, BEq, Inhabited

/-- `protobuf`'s 32-bit varint rule: at most five bytes, the fifth at most `0x0f`. -/
def Varint.fitsU32 (v : Varint) : Bool :=
  v.width < 5 || (v.width == 5 && v.last ≤ 0x0f)

/-- A `uint32` field. -/
def Varint.toU32 (v : Varint) : Except Error UInt32 :=
  if v.fitsU32 then .ok v.val.toUInt32 else .error .varint

/-- A `bool` field: any nonzero varint is true. -/
def Varint.toBool (v : Varint) : Bool :=
  v.val != 0

/-- An `int32` field or an enum number: the varint read as `i64` must fit. -/
def Varint.toI32 (v : Varint) : Except Error Int :=
  let i := v.val.toInt64.toInt
  if -2147483648 ≤ i && i ≤ 2147483647 then .ok i else .error (.value "int32 overflow")

/-- An `int64` field. -/
def Varint.toI64 (v : Varint) : Int :=
  v.val.toInt64.toInt

/-- The payload of a field. A length-delimited payload that is a message may claim more bytes than
the input holds, and `protobuf` reads it as far as the input goes: `slack` is the number of bytes
it claims beyond `b`, which a message inside it can still claim. -/
inductive Value where
  | varint (v : Varint)
  | fixed64 (v : UInt64)
  | fixed32 (v : UInt32)
  | bytes (b : ByteArray) (slack : Nat)
  deriving Inhabited

/-- A field of a message body. -/
structure Field where
  num : Nat
  val : Value
  deriving Inhabited

/-- The largest field number. -/
def maxFieldNumber : Nat :=
  0x1fffffff

/-! ### Reading -/

/-- A varint of `d` at `pos`, read within `d[:stop]`; returns it and the next position. -/
def readVarint (d : ByteArray) (pos stop : Nat) : Except Error (Varint × Nat) := do
  let mut acc : UInt64 := 0
  for i in [0:10] do
    let p := pos + i
    if p ≥ stop || p ≥ d.size then
      throw .eof
    let b := d.get! p
    if i == 9 && (b &&& 0x7f) > 1 then
      throw .varint
    acc := acc ||| ((b &&& 0x7f).toUInt64 <<< (7 * i).toUInt64)
    if b < 0x80 then
      return ({ val := acc, width := i + 1, last := b }, p + 1)
  throw .varint

/-- A tag: field number and wire type, read as a `u32` varint. -/
def readTag (d : ByteArray) (pos stop : Nat) : Except Error (Nat × Nat × Nat) := do
  let (v, p) ← readVarint d pos stop
  if !v.fitsU32 then
    throw .varint
  let t := v.val.toNat
  let wire := t % 8
  let num := t / 8
  if wire > 5 || num == 0 then
    throw .tag
  pure (num, wire, p)

private def le (d : ByteArray) (p n : Nat) : UInt64 :=
  Id.run do
    let mut r : UInt64 := 0
    for i in [0:n] do
      r := r ||| ((d.get! (p + i)).toUInt64 <<< (8 * i).toUInt64)
    return r

/-- Skips one field of a group's body; `stop` is the end of what can be read. -/
private def skipField (d : ByteArray) (wire pos stop : Nat) : Except Error Nat :=
  match wire with
  | 0 => do
    let (_, p) ← readVarint d pos stop
    pure p
  | 1 => if pos + 8 ≤ stop then pure (pos + 8) else throw .eof
  | 5 => if pos + 4 ≤ stop then pure (pos + 4) else throw .eof
  | 2 => do
    let (n, p) ← readVarint d pos stop
    if !n.fitsU32 then
      throw .varint
    if p + n.val.toNat ≤ stop then
      pure (p + n.val.toNat)
    else
      throw .eof
  | _ => throw .wireType

/-- Skips a group's body up to its end marker; `pos` is just after the start marker. -/
private partial def skipGroup (d : ByteArray) (pos stop : Nat) : Except Error Nat := do
  let (_, wire, p) ← readTag d pos stop
  if wire == 4 then
    pure p
  else
    skipGroup d (← skipField d wire p stop) stop

/-- `u64::MAX`, the limit of the stream a message is parsed from. -/
def noLimit : Nat :=
  2 ^ 64 - 1

/-- Frames the body `d[pos:lim]` of a message into its fields, as the generated `merge_from` reads
them. `lim` is the limit that `protobuf` sets, which can lie beyond the end of `d`: the message is
read to the end of the input or the limit, whichever comes first. `wide` lists the field numbers
whose length-delimited payloads are messages or packed arrays, which `protobuf` reads with a 64-bit
length that sets a new limit; every other length is a `u32` and the bytes must be there. Groups are
skipped. -/
partial def parseRange (d : ByteArray) (pos lim : Nat) (wide : List Nat) :
    Except Error (Array Field) :=
  go pos #[]
where
  stop : Nat := min lim d.size
  go (pos : Nat) (acc : Array Field) : Except Error (Array Field) := do
    if pos ≥ stop then
      return acc
    let (num, wire, p) ← readTag d pos stop
    match wire with
    | 0 =>
      let (v, p) ← readVarint d p stop
      go p (acc.push ⟨num, .varint v⟩)
    | 1 =>
      if p + 8 ≤ stop then
        go (p + 8) (acc.push ⟨num, .fixed64 (le d p 8)⟩)
      else
        throw .eof
    | 5 =>
      if p + 4 ≤ stop then
        go (p + 4) (acc.push ⟨num, .fixed32 (le d p 4).toUInt32⟩)
      else
        throw .eof
    | 2 =>
      let (n, p) ← readVarint d p stop
      if wide.contains num then
        let newLim := p + n.val.toNat
        if newLim > noLimit || newLim > lim then
          throw .length
        let dataEnd := min newLim d.size
        go dataEnd (acc.push ⟨num, .bytes (d.extract p dataEnd) (newLim - dataEnd)⟩)
      else
        if !n.fitsU32 then
          throw .varint
        if p + n.val.toNat ≤ stop then
          go (p + n.val.toNat) (acc.push ⟨num, .bytes (d.extract p (p + n.val.toNat)) 0⟩)
        else
          throw .length
    | 3 =>
      go (← skipGroup d p stop) acc
    | _ =>
      throw .wireType

/-- Frames a whole message; `slack` is how far beyond `d` its limit lies. -/
def parseFields (d : ByteArray) (wide : List Nat := []) (slack : Nat := 0) :
    Except Error (Array Field) :=
  parseRange d 0 (d.size + slack) wide

/-- A packed array of `uint64` (or `bool`) varints. -/
partial def readPacked (b : ByteArray) : Except Error (Array UInt64) :=
  go 0 #[]
where go (pos : Nat) (acc : Array UInt64) : Except Error (Array UInt64) := do
    if pos ≥ b.size then
      return acc
    let (v, p) ← readVarint b pos b.size
    go p (acc.push v.val)

/-- A `string` field. -/
def readString (b : ByteArray) : Except Error String :=
  match String.fromUTF8? b with
  | some s => .ok s
  | none => .error .utf8

/-- The last field `n` for which `f` gives a value. -/
def lastOf (fs : Array Field) (f : Field → Except Error (Option α)) : Except Error (Option α) := do
  let mut r := none
  for x in fs do
    if let some v← f x then
      r := some v
  pure r

/-- A required value. -/
def required (what : String) : Option α → Except Error α
  | some a => .ok a
  | none => .error (.missing what)

/-! ### Schemas -/

/-- How `protobuf` reads a field: the checks it makes before the field is converted. -/
inductive Kind where
  | u32
  | u64
  | bool
  /-- An `enum` or `int32`: a varint read as a signed 32-bit number. -/
  | i32
  | i64
  | bytes
  | string
  /-- A repeated `uint64`, packed or not. -/
  | packed
  /-- An embedded message with its own fields. -/
  | msg (fields : List (Nat × Kind))

/-- The fields of a message type, by number. -/
abbrev Schema :=
  List (Nat × Kind)

/-- The field numbers whose length is a 64-bit varint: embedded messages and packed arrays. -/
def Schema.wide (s : Schema) : List Nat :=
  s.filterMap fun (n, k) =>
    match k with
    | .msg _ => some n
    | .packed => some n
    | _ => none

/-- Parses a message the way the generated `merge_from` does and checks every field it knows, and
every embedded message, whether or not a conversion later uses it: this is what
`parse_from_bytes` rejects. -/
partial def validate (s : Schema) (b : ByteArray) (slack : Nat := 0) : Except Error Unit := do
  let fs ← parseFields b s.wide slack
  for f in fs do
    match s.lookup f.num, f.val with
    | some .u32, .varint v =>
      discard v.toU32
    | some .i32, .varint v =>
      discard v.toI32
    | some .string, .bytes d _ =>
      discard (readString d)
    | some .packed, .bytes d _ =>
      discard (readPacked d)
    | some (.msg fields), .bytes d sl =>
      validate fields d sl
    | _, _ =>
      pure ()

/-! ### Writing -/

/-- Appends a varint. -/
partial def putVarint (d : ByteArray) (v : UInt64) : ByteArray :=
  if v < 0x80 then d.push v.toUInt8
  else putVarint (d.push ((v &&& 0x7f) ||| 0x80).toUInt8) (v >>> 7)

/-- Appends a tag. -/
def putTag (d : ByteArray) (num wire : Nat) : ByteArray :=
  putVarint d ((num <<< 3 ||| wire).toUInt64)

/-- `fixed32`. -/
def putFixed32 (d : ByteArray) (v : UInt32) : ByteArray :=
  d.push v.toUInt8 |>.push (v >>> 8).toUInt8 |>.push (v >>> 16).toUInt8 |>.push (v >>> 24).toUInt8

/-- `fixed64`. -/
def putFixed64 (d : ByteArray) (v : UInt64) : ByteArray :=
  Id.run do
    let mut d := d
    for i in [0:8] do
      d := d.push (v >>> (8 * i).toUInt64).toUInt8
    return d

/-- A varint field. -/
def putVarintField (d : ByteArray) (num : Nat) (v : UInt64) : ByteArray :=
  putVarint (putTag d num 0) v

/-- A length-delimited field (`bytes`, `string` or an embedded message). -/
def putBytesField (d : ByteArray) (num : Nat) (b : ByteArray) : ByteArray :=
  (putVarint (putTag d num 2) b.size.toUInt64).append b

/-- A `fixed32` field. -/
def putFixed32Field (d : ByteArray) (num : Nat) (v : UInt32) : ByteArray :=
  putFixed32 (putTag d num 5) v

/-- A `fixed64` field. -/
def putFixed64Field (d : ByteArray) (num : Nat) (v : UInt64) : ByteArray :=
  putFixed64 (putTag d num 1) v

/-- A packed repeated varint field; nothing for an empty array. -/
def putPackedField (d : ByteArray) (num : Nat) (vs : Array UInt64) : ByteArray :=
  if vs.isEmpty then d else putBytesField d num (vs.foldl putVarint ByteArray.empty)

/-- A repeated varint field, one tag per element (what `protobuf` 3.0.2 writes). -/
def putRepeatedField (d : ByteArray) (num : Nat) (vs : Array UInt64) : ByteArray :=
  vs.foldl (fun d v => putVarintField d num v) d

/-- Writes a scalar unless it is the proto3 default. -/
def putU64 (d : ByteArray) (num : Nat) (v : UInt64) : ByteArray :=
  if v == 0 then d else putVarintField d num v

def putU32 (d : ByteArray) (num : Nat) (v : UInt32) : ByteArray :=
  putU64 d num v.toUInt64

def putBool (d : ByteArray) (num : Nat) (v : Bool) : ByteArray :=
  if v then putVarintField d num 1 else d

def putBytes (d : ByteArray) (num : Nat) (b : ByteArray) : ByteArray :=
  if b.isEmpty then d else putBytesField d num b

def putString (d : ByteArray) (num : Nat) (s : String) : ByteArray :=
  putBytes d num s.toUTF8

/-- An embedded message is written when present, even if it is empty. -/
def putMessage (d : ByteArray) (num : Nat) (m : Option ByteArray) : ByteArray :=
  match m with
  | some b => putBytesField d num b
  | none => d

/-- An `int64` field. -/
def putI64 (d : ByteArray) (num : Nat) (v : Int) : ByteArray :=
  if v == 0 then d else putVarintField d num (Int64.ofInt v).toUInt64

/-! ### Zigzag -/

/-- Zigzag of a signed integer. -/
def zigzagEncode (n : Int) : Nat :=
  if n ≥ 0 then 2 * n.toNat else 2 * (-n).toNat - 1

/-- The signed integer of a zigzag value. -/
def zigzagDecode (n : Nat) : Int :=
  if n % 2 == 0 then Int.ofNat (n / 2) else -Int.ofNat ((n + 1) / 2)

end Near.Node.Proto
