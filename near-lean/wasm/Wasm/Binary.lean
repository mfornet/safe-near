import Wasm.Syntax

/-!
# Binary format decoder

`Wasm.Binary.decode` turns the bytes of a `.wasm` file into a `Module`,
following section 5 ("Binary Format") of the specification. It rejects
every malformed input the specification rejects (bad LEB128 encodings,
section size mismatches, inconsistent function and code sections, invalid
UTF-8 names, …) with `DecodeError.malformed`, and anything that uses a
feature outside our scope with `DecodeError.unsupported`. Validation
(section 3) is a separate pass; the decoder only knows the grammar.

The parser is a function from the input and a position to a result and the
next position. Every loop is bounded by a count read from the input or by the
number of bytes left, so the decoder is total.
-/

namespace Wasm.Binary

inductive DecodeError where
  /-- The input is not a well-formed module. -/
  | malformed (pos : Nat) (message : String)
  /-- The input uses a feature outside the supported set. -/
  | unsupported (pos : Nat) (feature : String)
deriving Repr, Inhabited

def DecodeError.message : DecodeError → String
  | .malformed pos msg => s!"malformed at byte {pos}: {msg}"
  | .unsupported pos feature => s!"unsupported feature at byte {pos}: {feature}"

/-- The bytes being decoded and the end of the region a parser may read. -/
structure Input where
  bytes : ByteArray
  limit : Nat

def Parser (α : Type) := Input → Nat → Except DecodeError (α × Nat)

namespace Parser

@[inline] protected def pure (a : α) : Parser α := fun _ pos => .ok (a, pos)

@[inline] protected def bind (p : Parser α) (f : α → Parser β) : Parser β := fun input pos =>
  match p input pos with
  | .ok (a, pos) => f a input pos
  | .error e => .error e

instance : Monad Parser where
  pure := Parser.pure
  bind := Parser.bind

@[inline] def fail (message : String) : Parser α := fun _ pos => .error (.malformed pos message)

@[inline] def unsupported (feature : String) : Parser α := fun _ pos =>
  .error (.unsupported pos feature)

@[inline] def position : Parser Nat := fun _ pos => .ok (pos, pos)

@[inline] def atEnd : Parser Bool := fun input pos => .ok (decide (pos ≥ input.limit), pos)

@[inline] def byte : Parser UInt8 := fun input pos =>
  if h : pos < input.limit ∧ pos < input.bytes.size then .ok (input.bytes[pos], pos + 1)
  else .error (.malformed pos "unexpected end")

@[inline] def peek? : Parser (Option UInt8) := fun input pos =>
  if h : pos < input.limit ∧ pos < input.bytes.size then .ok (some input.bytes[pos], pos)
  else .ok (none, pos)

/-- Read `n` raw bytes. -/
def bytes (n : Nat) : Parser ByteArray := fun input pos =>
  if pos + n ≤ input.limit ∧ pos + n ≤ input.bytes.size then
    .ok (input.bytes.extract pos (pos + n), pos + n)
  else .error (.malformed pos "unexpected end")

/-- Run `p` on exactly the next `n` bytes: it may not read past them and must
consume all of them. -/
def sized (n : Nat) (p : Parser α) : Parser α := fun input pos =>
  let stop := pos + n
  if stop > input.limit then .error (.malformed pos "unexpected end")
  else
    match p { input with limit := stop } pos with
    | .error e => .error e
    | .ok (a, pos') =>
      if pos' = stop then .ok (a, pos')
      else .error (.malformed pos' "section size mismatch")

/-- Skip to the end of the current region. -/
def skipToLimit : Parser Unit := fun input _ => .ok ((), input.limit)

/-- Repeat `p` exactly `n` times. -/
def count (n : Nat) (p : Parser α) : Parser (Array α) := do
  let mut out : Array α := Array.mkEmpty n
  for _ in [0:n] do
    out := out.push (← p)
  return out

/-! ## LEB128 -/

/-- Unsigned LEB128 of at most `bits` bits. -/
def uleb (bits : Nat) : Parser Nat :=
  go ((bits + 6) / 7) 0 0
where
  go : Nat → Nat → Nat → Parser Nat
    | 0, _, _ => fail "integer representation too long"
    | n + 1, shift, acc => do
      let b ← byte
      let payload := (b &&& 0x7F).toNat
      let acc := acc + (payload <<< shift)
      if b &&& 0x80 == 0 then
        if n == 0 && payload >>> (bits - shift) != 0 then fail "integer too large"
        else return acc
      else if n == 0 then fail "integer representation too long"
      else go n (shift + 7) acc

/-- Signed LEB128 of at most `bits` bits, as a mathematical integer. -/
def sleb (bits : Nat) : Parser Int :=
  go ((bits + 6) / 7) 0 0
where
  go : Nat → Nat → Nat → Parser Int
    | 0, _, _ => fail "integer representation too long"
    | n + 1, shift, acc => do
      let b ← byte
      let payload := (b &&& 0x7F).toNat
      let acc := acc + (payload <<< shift)
      if b &&& 0x80 == 0 then
        if n == 0 then
          -- Bits beyond the value's width must all equal its sign bit.
          let avail := bits - shift
          let top := payload >>> (avail - 1)
          let full := (1 <<< (8 - avail)) - 1
          if top != 0 && top != full then fail "integer too large"
        let value : Int := acc
        return if b &&& 0x40 != 0 then value - ((1 : Int) <<< (shift + 7)) else value
      else if n == 0 then fail "integer representation too long"
      else go n (shift + 7) acc

def u32 : Parser Nat := uleb 32

def s32 : Parser UInt32 := do
  let v ← sleb 32
  return UInt32.ofNat (v % ((1 : Int) <<< 32)).toNat

def s64 : Parser UInt64 := do
  let v ← sleb 64
  return UInt64.ofNat (v % ((1 : Int) <<< 64)).toNat

/-- A vector: a `u32` count followed by that many elements. -/
def vec (p : Parser α) : Parser (Array α) := do count (← u32) p

def name : Parser String := do
  let n ← u32
  let raw ← bytes n
  match String.fromUTF8? raw with
  | some s => return s
  | none => fail "malformed UTF-8 encoding"

def le32 : Parser UInt32 := do
  let b ← bytes 4
  return b[0]!.toUInt32 ||| (b[1]!.toUInt32 <<< 8) ||| (b[2]!.toUInt32 <<< 16) |||
    (b[3]!.toUInt32 <<< 24)

def le64 : Parser UInt64 := do
  let lo ← le32
  let hi ← le32
  return lo.toUInt64 ||| (hi.toUInt64 <<< 32)

/-! ## Types -/

def numType? : UInt8 → Option NumType
  | 0x7F => some .i32
  | 0x7E => some .i64
  | 0x7D => some .f32
  | 0x7C => some .f64
  | _ => none

def refType? : UInt8 → Option RefType
  | 0x70 => some .funcref
  | 0x6F => some .externref
  | _ => none

/-- Classify a type byte we do not support, so a module using it is reported
as out of scope rather than malformed. -/
def unsupportedType? : UInt8 → Option String
  | 0x7B => some "simd"
  | 0x78 => some "v128-packed"
  | 0x6B | 0x6A | 0x69 | 0x68 | 0x67 | 0x66 | 0x65 | 0x64 | 0x63 | 0x6E | 0x6D | 0x6C | 0x73 |
    0x72 | 0x71 => some "gc"
  | _ => none

def valType : Parser ValType := do
  let b ← byte
  if let some t := numType? b then return .num t
  if let some t := refType? b then return .ref t
  if let some f := unsupportedType? b then unsupported f
  fail "malformed value type"

def refType : Parser RefType := do
  let b ← byte
  if let some t := refType? b then return t
  if let some f := unsupportedType? b then unsupported f
  fail "malformed reference type"

def funcType : Parser FuncType := do
  let b ← byte
  match b with
  | 0x60 => return { params := (← vec valType).toList, results := (← vec valType).toList }
  | 0x4E | 0x50 | 0x5E | 0x5F => unsupported "gc"
  | _ => fail "malformed function type"

/-- Limits are `u64` in the binary format; validation bounds them. -/
def limits : Parser Limits := do
  let flags ← byte
  match flags with
  | 0x00 => return { min := ← uleb 64, max := none }
  | 0x01 => return { min := ← uleb 64, max := some (← uleb 64) }
  | 0x02 | 0x03 => unsupported "threads"
  | 0x04 | 0x05 | 0x06 | 0x07 => unsupported "memory64"
  | _ => fail "malformed limits flags"

def tableType : Parser TableType := do
  if (← peek?) == some 0x40 then unsupported "function-references"
  let elem ← refType
  return { elem, limits := ← limits }

def memType : Parser MemType := do
  return { limits := ← limits }

def globalType : Parser GlobalType := do
  let type ← valType
  let mutable ← match ← byte with
    | 0x00 => pure false
    | 0x01 => pure true
    | _ => fail "malformed mutability"
  return { type, mutable }

/-! ## Instructions -/

def blockType : Parser BlockType := do
  match ← peek? with
  | some 0x40 => let _ ← byte; return .empty
  | some b =>
    if (numType? b).isSome || (refType? b).isSome then return .val (← valType)
    else if let some f := unsupportedType? b then unsupported f
    else
      let i ← sleb 33
      if i < 0 then fail "malformed block type"
      return .index i.toNat
  | none => fail "unexpected end"

def memArg : Parser MemArg := do
  let align ← u32
  if align ≥ 64 then unsupported "multi-memory"
  return { align, offset := ← uleb 64 }

/-- The memory index of a memory instruction, which must be `0` without
multi-memory. -/
def zeroByte : Parser Unit := do
  if (← byte) != 0 then unsupported "multi-memory"

/-- Instructions with no immediates in the numeric range `0x45`–`0xC4`. -/
def numeric? (op : UInt8) : Option Instr :=
  let irel : List IRelOp := [.eq, .ne, .lt_s, .lt_u, .gt_s, .gt_u, .le_s, .le_u, .ge_s, .ge_u]
  let frel : List FRelOp := [.eq, .ne, .lt, .gt, .le, .ge]
  let iun : List IUnOp := [.clz, .ctz, .popcnt]
  let ibin : List IBinOp := [.add, .sub, .mul, .div_s, .div_u, .rem_s, .rem_u, .and, .or, .xor,
    .shl, .shr_s, .shr_u, .rotl, .rotr]
  let fun_ : List FUnOp := [.abs, .neg, .ceil, .floor, .trunc, .nearest, .sqrt]
  let fbin : List FBinOp := [.add, .sub, .mul, .div, .min, .max, .copysign]
  let cvt : List CvtOp := [.i32_wrap_i64, .i32_trunc_f32_s, .i32_trunc_f32_u, .i32_trunc_f64_s,
    .i32_trunc_f64_u, .i64_extend_i32_s, .i64_extend_i32_u, .i64_trunc_f32_s, .i64_trunc_f32_u,
    .i64_trunc_f64_s, .i64_trunc_f64_u, .f32_convert_i32_s, .f32_convert_i32_u,
    .f32_convert_i64_s, .f32_convert_i64_u, .f32_demote_f64, .f64_convert_i32_s,
    .f64_convert_i32_u, .f64_convert_i64_s, .f64_convert_i64_u, .f64_promote_f32,
    .i32_reinterpret_f32, .i64_reinterpret_f64, .f32_reinterpret_i32, .f64_reinterpret_i64]
  let pick {α : Type} (base : UInt8) (l : List α) (f : α → Instr) : Option Instr :=
    (l[(op - base).toNat]?).map f
  let n := op.toNat
  if n == 0x45 then some .i32_eqz
  else if n ≤ 0x4F then pick 0x46 irel .i32_relop
  else if n == 0x50 then some .i64_eqz
  else if n ≤ 0x5A then pick 0x51 irel .i64_relop
  else if n ≤ 0x60 then pick 0x5B frel .f32_relop
  else if n ≤ 0x66 then pick 0x61 frel .f64_relop
  else if n ≤ 0x69 then pick 0x67 iun .i32_unop
  else if n ≤ 0x78 then pick 0x6A ibin .i32_binop
  else if n ≤ 0x7B then pick 0x79 iun .i64_unop
  else if n ≤ 0x8A then pick 0x7C ibin .i64_binop
  else if n ≤ 0x91 then pick 0x8B fun_ .f32_unop
  else if n ≤ 0x98 then pick 0x92 fbin .f32_binop
  else if n ≤ 0x9F then pick 0x99 fun_ .f64_unop
  else if n ≤ 0xA6 then pick 0xA0 fbin .f64_binop
  else if n ≤ 0xBF then pick 0xA7 cvt .cvt
  else if n == 0xC0 then some (.i32_unop .extend8_s)
  else if n == 0xC1 then some (.i32_unop .extend16_s)
  else if n == 0xC2 then some (.i64_unop .extend8_s)
  else if n == 0xC3 then some (.i64_unop .extend16_s)
  else if n == 0xC4 then some (.i64_unop .extend32_s)
  else none

def memoryOp? (op : UInt8) : Option (MemArg → Instr) :=
  match op with
  | 0x28 => some (.load .i32 none)
  | 0x29 => some (.load .i64 none)
  | 0x2A => some (.load .f32 none)
  | 0x2B => some (.load .f64 none)
  | 0x2C => some (.load .i32 (some ⟨8, true⟩))
  | 0x2D => some (.load .i32 (some ⟨8, false⟩))
  | 0x2E => some (.load .i32 (some ⟨16, true⟩))
  | 0x2F => some (.load .i32 (some ⟨16, false⟩))
  | 0x30 => some (.load .i64 (some ⟨8, true⟩))
  | 0x31 => some (.load .i64 (some ⟨8, false⟩))
  | 0x32 => some (.load .i64 (some ⟨16, true⟩))
  | 0x33 => some (.load .i64 (some ⟨16, false⟩))
  | 0x34 => some (.load .i64 (some ⟨32, true⟩))
  | 0x35 => some (.load .i64 (some ⟨32, false⟩))
  | 0x36 => some (.store .i32 none)
  | 0x37 => some (.store .i64 none)
  | 0x38 => some (.store .f32 none)
  | 0x39 => some (.store .f64 none)
  | 0x3A => some (.store .i32 (some 8))
  | 0x3B => some (.store .i32 (some 16))
  | 0x3C => some (.store .i64 (some 8))
  | 0x3D => some (.store .i64 (some 16))
  | 0x3E => some (.store .i64 (some 32))
  | _ => none

/-- The `0xFC` prefixed instructions. -/
def prefixedFC : Parser Instr := do
  let sat : List CvtOp := [.i32_trunc_sat_f32_s, .i32_trunc_sat_f32_u, .i32_trunc_sat_f64_s,
    .i32_trunc_sat_f64_u, .i64_trunc_sat_f32_s, .i64_trunc_sat_f32_u, .i64_trunc_sat_f64_s,
    .i64_trunc_sat_f64_u]
  match ← u32 with
  | 8 => let d ← u32; zeroByte; return .memory_init d
  | 9 => return .data_drop (← u32)
  | 10 => zeroByte; zeroByte; return .memory_copy
  | 11 => zeroByte; return .memory_fill
  | 12 => let e ← u32; let t ← u32; return .table_init t e
  | 13 => return .elem_drop (← u32)
  | 14 => let dst ← u32; let src ← u32; return .table_copy dst src
  | 15 => return .table_grow (← u32)
  | 16 => return .table_size (← u32)
  | 17 => return .table_fill (← u32)
  | n =>
    match sat[n]? with
    | some op => return .cvt op
    | none => fail "illegal opcode"

/-- Terminator of an instruction sequence. -/
inductive Terminator where
  | «end» | «else»
deriving DecidableEq

mutual
/-- Decode one instruction whose opcode `op` has been read. `fuel` bounds the
nesting of structured instructions: each level spends one unit, and reads at
least one byte (its block type), so fuel that covers the remaining bytes never
runs out first. Spending it here makes `instr` and `seq` structurally
recursive, so the kernel can evaluate the decoder (proofs about modules as
decoded from their bytes rely on that). -/
def instr (fuel : Nat) (op : UInt8) : Parser Instr := do
  match op with
  | 0x00 => return .unreachable
  | 0x01 => return .nop
  | 0x02 =>
    let bt ← blockType
    match fuel with
    | 0 => fail "unexpected end"
    | fuel + 1 =>
      let (body, t) ← seq fuel #[]
      if t != .end then fail "END opcode expected"
      return .block bt body.toList
  | 0x03 =>
    let bt ← blockType
    match fuel with
    | 0 => fail "unexpected end"
    | fuel + 1 =>
      let (body, t) ← seq fuel #[]
      if t != .end then fail "END opcode expected"
      return .loop bt body.toList
  | 0x04 =>
    let bt ← blockType
    match fuel with
    | 0 => fail "unexpected end"
    | fuel + 1 =>
      let (thenBody, t) ← seq fuel #[]
      match t with
      | .end => return .«if» bt thenBody.toList []
      | .else =>
        let (elseBody, t) ← seq fuel #[]
        if t != .end then fail "END opcode expected"
        return .«if» bt thenBody.toList elseBody.toList
  | 0x0C => return .br (← u32)
  | 0x0D => return .br_if (← u32)
  | 0x0E =>
    let labels ← vec u32
    return .br_table labels.toList (← u32)
  | 0x0F => return .return
  | 0x10 => return .call (← u32)
  | 0x11 =>
    let type ← u32
    let table ← u32
    return .call_indirect type table
  | 0x1A => return .drop
  | 0x1B => return .select none
  | 0x1C => return .select (some (← vec valType).toList)
  | 0x20 => return .local_get (← u32)
  | 0x21 => return .local_set (← u32)
  | 0x22 => return .local_tee (← u32)
  | 0x23 => return .global_get (← u32)
  | 0x24 => return .global_set (← u32)
  | 0x25 => return .table_get (← u32)
  | 0x26 => return .table_set (← u32)
  | 0x3F => zeroByte; return .memory_size
  | 0x40 => zeroByte; return .memory_grow
  | 0x41 => return .i32_const (← s32)
  | 0x42 => return .i64_const (← s64)
  | 0x43 => return .f32_const (← le32)
  | 0x44 => return .f64_const (← le64)
  | 0xD0 => return .ref_null (← refType)
  | 0xD1 => return .ref_is_null
  | 0xD2 => return .ref_func (← u32)
  | 0xFC => prefixedFC
  | 0xFD => unsupported "simd"
  | 0xFE => unsupported "threads"
  | 0xFB => unsupported "gc"
  | 0x06 | 0x07 | 0x08 | 0x09 | 0x0A | 0x18 | 0x19 | 0x1F => unsupported "exceptions"
  | 0x12 | 0x13 => unsupported "tail-call"
  | 0x14 | 0x15 | 0xD3 | 0xD4 | 0xD5 | 0xD6 => unsupported "function-references"
  | _ =>
    if let some i := numeric? op then return i
    if let some mk := memoryOp? op then return mk (← memArg)
    fail "illegal opcode"

/-- Decode instructions up to and including an `end` or `else` opcode. -/
def seq (fuel : Nat) (acc : Array Instr) : Parser (Array Instr × Terminator) := do
  match fuel with
  | 0 => fail "unexpected end"
  | fuel + 1 =>
    match ← byte with
    | 0x0B => return (acc, .end)
    | 0x05 => return (acc, .else)
    | op => seq fuel (acc.push (← instr fuel op))
end

/-- An expression: instructions terminated by `end`. -/
def expr : Parser Expr := fun input pos => do
  let ((body, t), pos') ← seq (input.limit - pos) #[] input pos
  if t != .end then .error (.malformed pos' "END opcode expected")
  return (body.toList, pos')

/-! ## Sections -/

def importDesc : Parser ImportDesc := do
  match ← byte with
  | 0x00 => return .func (← u32)
  | 0x01 => return .table (← tableType)
  | 0x02 => return .mem (← memType)
  | 0x03 => return .global (← globalType)
  | 0x04 => unsupported "exceptions"
  | _ => fail "malformed import kind"

def import_ : Parser Import := do
  let module ← name
  let name ← name
  return { module, name, desc := ← importDesc }

def export_ : Parser Export := do
  let name ← name
  let desc ← match ← byte with
    | 0x00 => pure (ExportDesc.func (← u32))
    | 0x01 => pure (ExportDesc.table (← u32))
    | 0x02 => pure (ExportDesc.mem (← u32))
    | 0x03 => pure (ExportDesc.global (← u32))
    | _ => fail "malformed export kind"
  return { name, desc }

def global : Parser Global := do
  let type ← globalType
  return { type, init := ← expr }

def elemKind : Parser RefType := do
  if (← byte) != 0x00 then fail "malformed element kind"
  return .funcref

def funcIndices : Parser (List Expr) := do
  return (← vec u32).toList.map fun f => [.ref_func f]

def elem : Parser Elem := do
  match ← u32 with
  | 0 =>
    let offset ← expr
    return { type := .funcref, init := ← funcIndices, mode := .active 0 offset }
  | 1 =>
    let type ← elemKind
    return { type, init := ← funcIndices, mode := .passive }
  | 2 =>
    let table ← u32
    let offset ← expr
    let type ← elemKind
    return { type, init := ← funcIndices, mode := .active table offset }
  | 3 =>
    let type ← elemKind
    return { type, init := ← funcIndices, mode := .declarative }
  | 4 =>
    let offset ← expr
    return { type := .funcref, init := (← vec expr).toList, mode := .active 0 offset }
  | 5 =>
    let type ← refType
    return { type, init := (← vec expr).toList, mode := .passive }
  | 6 =>
    let table ← u32
    let offset ← expr
    let type ← refType
    return { type, init := (← vec expr).toList, mode := .active table offset }
  | 7 =>
    let type ← refType
    return { type, init := (← vec expr).toList, mode := .declarative }
  | _ => fail "malformed elements segment kind"

def data : Parser Data := do
  let mode ← match ← u32 with
    | 0 => pure (SegmentMode.active 0 (← expr))
    | 1 => pure SegmentMode.passive
    | 2 =>
      let mem ← u32
      pure (SegmentMode.active mem (← expr))
    | _ => fail "malformed data segment kind"
  let n ← u32
  return { init := ← bytes n, mode }

/-- A code entry: its locals and body, without the type index the function
section holds. -/
def code : Parser (List ValType × Expr) := do
  let size ← u32
  sized size do
    let groups ← vec do
      let n ← u32
      return (n, ← valType)
    let total := groups.foldl (fun acc (n, _) => acc + n) 0
    if total ≥ (1 <<< 32) then fail "too many locals"
    let locals := groups.toList.flatMap fun (n, t) => List.replicate n t
    return (locals, ← expr)

/-- Section ids in the order the specification requires. -/
def sectionRank : UInt8 → Option Nat
  | 1 => some 1 | 2 => some 2 | 3 => some 3 | 4 => some 4 | 5 => some 5 | 6 => some 6
  | 7 => some 7 | 8 => some 8 | 9 => some 9 | 12 => some 10 | 10 => some 11 | 11 => some 12
  | _ => none

/-- The sections of a module before they are assembled. -/
structure Sections where
  module : Module := {}
  funcTypes : Array Nat := #[]
  codes : Array (List ValType × Expr) := #[]
  dataCount : Option Nat := none
  lastRank : Nat := 0

def oneSection (s : Sections) : Parser Sections := do
  let id ← byte
  let size ← u32
  if id == 0 then
    sized size do
      let _ ← name
      skipToLimit
      return s
  else
    let rank ← match sectionRank id with
      | some r => pure r
      | none => if id == 13 then unsupported "exceptions" else fail "malformed section id"
    if rank ≤ s.lastRank then fail "unexpected content after last section"
    let s := { s with lastRank := rank }
    sized size do
      match id with
      | 1 => return { s with module.types := ← vec funcType }
      | 2 => return { s with module.imports := ← vec import_ }
      | 3 => return { s with funcTypes := ← vec u32 }
      | 4 => return { s with module.tables := (← vec tableType).map ({ type := · }) }
      | 5 => return { s with module.mems := (← vec memType).map ({ type := · }) }
      | 6 => return { s with module.globals := ← vec global }
      | 7 => return { s with module.exports := ← vec export_ }
      | 8 => return { s with module.start := some (← u32) }
      | 9 => return { s with module.elems := ← vec elem }
      | 12 => return { s with dataCount := some (← u32) }
      | 10 => return { s with codes := ← vec code }
      | _ => return { s with module.datas := ← vec data }

def sections (fuel : Nat) (s : Sections) : Parser Sections := do
  match fuel with
  | 0 => return s
  | fuel + 1 =>
    if ← atEnd then return s
    sections fuel (← oneSection s)

mutual
/-- Whether an instruction uses `memory.init` or `data.drop`, which the binary
format only permits when a data count section is present. -/
def usesDataIndex : Instr → Bool
  | .memory_init _ | .data_drop _ => true
  | .block _ body | .loop _ body => anyUsesDataIndex body
  | .«if» _ a b => anyUsesDataIndex a || anyUsesDataIndex b
  | _ => false

def anyUsesDataIndex : List Instr → Bool
  | [] => false
  | i :: rest => usesDataIndex i || anyUsesDataIndex rest
end

def module : Parser Module := do
  let magic ← bytes 4
  if magic.toList != [0x00, 0x61, 0x73, 0x6D] then fail "magic header not detected"
  let version ← bytes 4
  if version.toList != [0x01, 0x00, 0x00, 0x00] then fail "unknown binary version"
  let s ← fun input pos => sections (input.limit - pos) {} input pos
  if s.funcTypes.size != s.codes.size then
    fail "function and code section have inconsistent lengths"
  if let some n := s.dataCount then
    if n != s.module.datas.size then
      fail "data count and data section have inconsistent lengths"
  else
    if s.codes.any (fun (_, body) => anyUsesDataIndex body) then fail "data count section required"
  let funcs := s.funcTypes.zipWith (fun type (locals, body) => { type, locals, body : Func })
    s.codes
  return { s.module with funcs }

end Parser

/-- Decode a complete module from the bytes of a `.wasm` file. -/
def decode (input : ByteArray) : Except DecodeError Module :=
  match Parser.module { bytes := input, limit := input.size } 0 with
  | .ok (m, _) => .ok m
  | .error e => .error e

end Wasm.Binary
