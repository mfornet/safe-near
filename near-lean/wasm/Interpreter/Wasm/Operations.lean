import Interpreter.Wasm.Syntax
import Interpreter.Wasm.Float
import Interpreter.Wasm.Locals
import Interpreter.Wasm.Continuation
import Interpreter.Wasm.Host

/-!
# Shared executable WebAssembly operations

Numeric and GC primitives shared by the small-step machine and the legacy
big-step regression interpreter. Keeping these operations separate lets VM
execution import the machine without the legacy interpreter or its proof API.
-/

namespace Wasm

/-! ## Numeric helpers. -/

/-- Number of leading zero bits in a 32-bit word; 32 if zero. -/
def clz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 0x80000000 ≠ 0 then 32 - (k + 1) else clz32 k (a <<< 1)

/-- Number of trailing zero bits in a 32-bit word; 32 if zero. -/
def ctz32 : Nat → UInt32 → Nat
  | 0, _ => 32
  | k + 1, a => if a &&& 1 ≠ 0 then 32 - (k + 1) else ctz32 k (a >>> 1)

/-- Number of one bits in a 32-bit word. -/
def popcnt32 : Nat → UInt32 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt32 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Number of leading zero bits in a 64-bit word; 64 if zero. -/
def clz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 0x8000000000000000 ≠ 0 then 64 - (k + 1) else clz64 k (a <<< 1)

/-- Number of trailing zero bits in a 64-bit word; 64 if zero. -/
def ctz64 : Nat → UInt64 → Nat
  | 0, _ => 64
  | k + 1, a => if a &&& 1 ≠ 0 then 64 - (k + 1) else ctz64 k (a >>> 1)

/-- Number of one bits in a 64-bit word. -/
def popcnt64 : Nat → UInt64 → Nat → Nat
  | 0, _, acc => acc
  | k + 1, a, acc => popcnt64 k (a >>> 1) (acc + (a &&& 1).toNat)

/-- Sign-extend the low `bits` bits of `n` to a signed `Int`. -/
def signExtend (n : Nat) (bits : Nat) : Int :=
  let half := 2 ^ (bits - 1)
  let bound := 2 ^ bits
  if n ≥ half then (n : Int) - (bound : Int) else (n : Int)

/-- Whether `ht` is one of the abstract heap types in the `any` hierarchy
(the only ones a managed `anyref` can inhabit), as opposed to the
`func`/`extern` families. Concrete struct/array type indices also live
under `any`. -/
def GcHeapType.inAnyHierarchy : GcHeapType → Bool
  | .any | .eq | .i31 | .structT | .arrayT | .noneT | .concrete _ => true
  | _ => false

/-- Decide whether a (non-null) managed reference `r` is a subtype of the
abstract heap type `ht`. Concrete struct/array type indices are resolved
against the module's GC type definitions and their declared supertypes. -/
def AnyRef.matchesHeap (m : Module) (st : Store α) (ht : GcHeapType) : AnyRef → Bool
  | .host _ => ht == .any
  | .i31 _ => match ht with
    | .any | .eq | .i31 => true
    | _ => false
  | .struct addr => match ht with
    | .any | .eq | .structT => true
    | .concrete t => match st.gcHeap[addr]? with
      | some obj => m.gcTypeSubtype obj.typeIdx t
      | none     => false
    | _ => false
  | .array addr => match ht with
    | .any | .eq | .arrayT => true
    | .concrete t => match st.gcHeap[addr]? with
      | some obj => m.gcTypeSubtype obj.typeIdx t
      | none     => false
    | _ => false

/-- Whether reference value `v` matches the target reference type
`(ref null?ₙ ht)` used by `ref.test`/`ref.cast`/`br_on_cast`. The null
reference matches exactly when the target is nullable and `ht` is in the
same (any vs func vs extern) bottom family.

A non-null funcref matches the abstract `func` heap type always, and a
concrete target `(ref $ft)` when the function's declared type is a
subtype of `$ft` (issue #96). When the declared type is unrecorded
(`funcTypeIdx? = none`, hand-built modules) the check degrades to
structural equality of the function's signature against the target's
composite type, mirroring `Module.indirectCallTypeOk`. -/
def gcRefMatches (m : Module) (st : Store α) (nullable : Bool)
    (ht : GcHeapType) : Value → Bool
  | .anyref none      => nullable && ht.inAnyHierarchy
  | .anyref (some r)  => r.matchesHeap m st ht
  | .funcref none     =>
    nullable &&
    (ht == .func || ht == .noFunc ||
     -- Null also inhabits every nullable *concrete* function type: the
     -- null funcref has type `nofunc`, the bottom of the func family.
     (match ht with
      | .concrete t => match m.gcComposite? t with
        | some (.func _) => true
        | _ => false
      | _ => false))
  | .funcref (some f) => match ht with
    | .func       => true
    | .concrete t =>
      (match m.funcTypeIdx? f with
       | some src => m.gcTypeSubtype src t
       | none     => match m.funcSig? f, m.gcComposite? t with
         | some fn, some (.func ty) => fn == ty
         | _, _ => false)
    | _ => false
  | .externref none   => nullable && (ht == .extern || ht == .noExtern)
  | .externref (some _) => ht == .extern
  | _                 => false

/-- Truncate a value to a packed field's width when storing it (GC
proposal); non-packed fields store the value unchanged. -/
def FieldType.pack (ft : FieldType) (v : Value) : Value :=
  match ft.storage, v with
  | .packed 8,  .i32 x => .i32 (x &&& 0xff)
  | .packed 16, .i32 x => .i32 (x &&& 0xffff)
  | _,          _      => v

/-- Read a field/element with sign extension (`*.get_s`): a packed
`i8`/`i16` slot is sign-extended to `i32`; everything else is unchanged. -/
def FieldType.readS (ft : FieldType) (v : Value) : Value :=
  match ft.storage, v with
  | .packed 8,  .i32 x => .i32 (if x &&& 0x80 ≠ 0 then x ||| 0xffffff00 else x)
  | .packed 16, .i32 x => .i32 (if x &&& 0x8000 ≠ 0 then x ||| 0xffff0000 else x)
  | _,          _      => v

/-- Read `n` little-endian bytes from a byte list as a `Nat`. Missing bytes
read as 0 (callers bounds-check first). -/
def readBytesLE (bytes : List UInt8) (off n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => acc + (bytes[off + i]?.getD 0).toNat * 2 ^ (8 * i)) 0

/-- Read one storage-type element from a byte list (little-endian), for
`array.new_data` / `array.init_data`. -/
def readStorageLE (storage : StorageType) (bytes : List UInt8) (off : Nat) : Value :=
  let n := readBytesLE bytes off storage.byteSize
  match storage with
  | .packed _ => .i32 (UInt32.ofNat n)
  | .val .i32 => .i32 (UInt32.ofNat n)
  | .val .i64 => .i64 (UInt64.ofNat n)
  | .val .f32 => .f32 (UInt32.ofNat n)
  | .val .f64 => .f64 (UInt64.ofNat n)
  | .val _    => .i32 0

/-- Evaluate a simple element-segment item constant expression to its
reference value (GC proposal). Covers the forms element segments use:
`ref.func`; the null refs `ref.null func`/`extern`/`exn` and `ref.null`
of a GC heap type; the `i32`/`i64` scalar constants; and `ref.i31` of an
`i32.const`. Heap-allocating items (`struct.new`) are not handled here. -/
def evalConstRef : Program → Option Value
  | [.refFunc f]                 => some (.funcref (some f))
  | [.refNull _]                 => some (.funcref none)
  | [.refNullExtern _]           => some (.externref none)
  | [.refNullExn _]              => some (.exnref none)
  | [.gc (.refNullAny _)]        => some (.anyref none)
  | [.const n]                   => some (.i32 n)
  | [.constI64 n]                => some (.i64 n)
  | [.const n, .gc .refI31]      => some (.anyref (some (.i31 (n &&& 0x7fffffff))))
  | _                            => none

/-- The reference values a (passive, non-dropped) element segment yields,
preferring decoded GC const-expr items and falling back to funcref
indices. -/
def ElementSegment.values (seg : ElementSegment) : List Value :=
  if seg.exprs.isEmpty then seg.plainValues
  else seg.exprs.map (fun e => (evalConstRef e).getD (.anyref none))

/-- Host-supplied extern handles occupy the unsigned 64-bit range. Handles
at or above this boundary are deterministic encodings of Wasm-managed
references externalized by `extern.convert_any`. -/
def externInternalBase : Nat := 2 ^ 64

def AnyRef.toExternId : AnyRef → Nat
  | .host id => id
  | .i31 value => externInternalBase + 3 * value.toNat
  | .struct address => externInternalBase + 3 * address + 1
  | .array address => externInternalBase + 3 * address + 2

def anyRefOfExternId (id : Nat) : AnyRef :=
  if id < externInternalBase then .host id
  else
    let encoded := id - externInternalBase
    match encoded % 3 with
    | 0 => .i31 ((encoded / 3).toUInt32 &&& 0x7fffffff)
    | 1 => .struct (encoded / 3)
    | _ => .array (encoded / 3)

/-- Execute one GC-proposal instruction. These never consume fuel or
recurse into `exec`/`run` — `struct.new`/`array.new` allocate on
`st.gcHeap`, the accessors read/update it, and `ref.test`/`ref.cast` decide
subtyping via `gcRefMatches` — so they live outside the fuel-threaded
`execOne` mutual block, dispatched from it by a single `gc` arm. -/
def execGcOp (m : Module) (st : Store α) (s : Locals) : GcOp → Continuation α
  | .refNullAny _ =>
      .Fallthrough st { s with values := .anyref none :: s.values }
  | .refI31 => match s.values with
    | .i32 x :: vs =>
      .Fallthrough st { s with values := .anyref (some (.i31 (x &&& 0x7fffffff))) :: vs }
    | _ => .Invalid "refI31: ill-shaped operand stack"
  | .i31GetU => match s.values with
    | .anyref (some (.i31 n)) :: vs =>
      .Fallthrough st { s with values := .i32 n :: vs }
    | .anyref none :: _ => .Trap st "null i31 reference"
    | _ => .Invalid "i31GetU: ill-shaped operand stack"
  | .i31GetS => match s.values with
    | .anyref (some (.i31 n)) :: vs =>
      let signed := if n &&& 0x40000000 ≠ 0 then n ||| 0x80000000 else n
      .Fallthrough st { s with values := .i32 signed :: vs }
    | .anyref none :: _ => .Trap st "null i31 reference"
    | _ => .Invalid "i31GetS: ill-shaped operand stack"
  | .refEq => match s.values with
    | .anyref a :: .anyref b :: vs =>
      .Fallthrough st { s with values := .i32 (if a == b then 1 else 0) :: vs }
    | _ => .Invalid "refEq: ill-shaped operand stack"
  | .anyConvertExtern => match s.values with
    | .externref none :: vs =>
      .Fallthrough st { s with values := .anyref none :: vs }
    | .externref (some id) :: vs =>
      .Fallthrough st
        { s with values := .anyref (some (anyRefOfExternId id)) :: vs }
    | _ => .Invalid "any.convert_extern: expected externref"
  | .externConvertAny => match s.values with
    | .anyref none :: vs =>
      .Fallthrough st { s with values := .externref none :: vs }
    | .anyref (some ref) :: vs =>
      .Fallthrough st
        { s with values := .externref (some ref.toExternId) :: vs }
    | _ => .Invalid "extern.convert_any: expected anyref"
  | .refTest nullable ht => match s.values with
    | v :: vs => match v with
      | .anyref _ | .funcref _ | .externref _ | .exnref _ =>
        .Fallthrough st
          { s with values := .i32 (if gcRefMatches m st nullable ht v then 1 else 0) :: vs }
      | _ => .Invalid "refTest: non-reference operand"
    | _ => .Invalid "refTest: ill-shaped operand stack"
  | .refCast nullable ht => match s.values with
    | v :: vs => match v with
      | .anyref _ | .funcref _ | .externref _ | .exnref _ =>
        if gcRefMatches m st nullable ht v then
          .Fallthrough st { s with values := v :: vs }
        else .Trap st "cast failure"
      | _ => .Invalid "refCast: non-reference operand"
    | _ => .Invalid "refCast: ill-shaped operand stack"
  -- `br_on_cast`/`br_on_cast_fail`: the ref stays on the operand stack in
  -- both the taken and the fall-through case.
  | .brOnCast label nullable ht => match s.values with
    | v :: _ =>
      if gcRefMatches m st nullable ht v then .Break label st s else .Fallthrough st s
    | _ => .Invalid "brOnCast: ill-shaped operand stack"
  | .brOnCastFail label nullable ht => match s.values with
    | v :: _ =>
      if gcRefMatches m st nullable ht v then .Fallthrough st s else .Break label st s
    | _ => .Invalid "brOnCastFail: ill-shaped operand stack"
  -- Structs. `struct.new` pops one value per field (last field on top).
  | .structNew t => match m.structFields? t with
    | some fields =>
      let n := fields.length
      if s.values.length < n then .Invalid "structNew: operand stack underflow"
      else
        let args := (s.values.take n).reverse
        let packed := (fields.zip args).map (fun (ft, v) => ft.pack v)
        .Fallthrough { st with gcHeap := st.gcHeap ++ [.struct t packed] }
          { s with values := .anyref (some (.struct st.gcHeap.length)) :: s.values.drop n }
    | none => .Invalid "structNew: not a struct type"
  | .structNewDefault t => match m.structFields? t with
    | some fields =>
      .Fallthrough
        { st with gcHeap := st.gcHeap ++ [.struct t (fields.map (·.storage.zero))] }
        { s with values := .anyref (some (.struct st.gcHeap.length)) :: s.values }
    | none => .Invalid "structNewDefault: not a struct type"
  | .structGet _ f => match s.values with
    | .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct _ fields) => match fields[f]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Invalid "structGet: field index out of range"
      | _ => .Invalid "structGet: not a struct"
    | .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structGet: ill-shaped operand stack"
  | .structGetU _ f => match s.values with
    | .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct _ fields) => match fields[f]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Invalid "structGetU: field index out of range"
      | _ => .Invalid "structGetU: not a struct"
    | .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structGetU: ill-shaped operand stack"
  | .structGetS t f => match s.values with
    | .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct _ fields) => match fields[f]?, m.structField? t f with
        | some v, some ft => .Fallthrough st { s with values := ft.readS v :: vs }
        | _, _ => .Invalid "structGetS: field index out of range"
      | _ => .Invalid "structGetS: not a struct"
    | .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structGetS: ill-shaped operand stack"
  | .structSet t f => match s.values with
    | val :: .anyref (some (.struct addr)) :: vs => match st.gcHeap[addr]? with
      | some (.struct ty fields) =>
        let pval := match m.structField? t f with | some ft => ft.pack val | none => val
        .Fallthrough { st with gcHeap := st.gcHeap.set addr (.struct ty (fields.set f pval)) }
          { s with values := vs }
      | _ => .Invalid "structSet: not a struct"
    | _ :: .anyref none :: _ => .Trap st "null structure reference"
    | _ => .Invalid "structSet: ill-shaped operand stack"
  -- Arrays.
  | .arrayNew t => match s.values with
    | .i32 len :: init :: vs =>
      let pinit := match m.arrayElem? t with | some ft => ft.pack init | none => init
      .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t (List.replicate len.toNat pinit)] }
        { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
    | _ => .Invalid "arrayNew: ill-shaped operand stack"
  | .arrayNewDefault t => match s.values with
    | .i32 len :: vs =>
      let z := match m.arrayElem? t with | some ft => ft.storage.zero | none => .i32 0
      .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t (List.replicate len.toNat z)] }
        { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
    | _ => .Invalid "arrayNewDefault: ill-shaped operand stack"
  | .arrayNewFixed t n =>
    if s.values.length < n then .Invalid "arrayNewFixed: operand stack underflow"
    else
      let elems := (s.values.take n).reverse
      let pelems := match m.arrayElem? t with | some ft => elems.map ft.pack | none => elems
      .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t pelems] }
        { s with values := .anyref (some (.array st.gcHeap.length)) :: s.values.drop n }
  | .arrayGet _ => match s.values with
    | .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) => match elems[idx.toNat]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Trap st "out of bounds array access"
      | _ => .Invalid "arrayGet: not an array"
    | _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayGet: ill-shaped operand stack"
  | .arrayGetU _ => match s.values with
    | .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) => match elems[idx.toNat]? with
        | some v => .Fallthrough st { s with values := v :: vs }
        | none   => .Trap st "out of bounds array access"
      | _ => .Invalid "arrayGetU: not an array"
    | _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayGetU: ill-shaped operand stack"
  | .arrayGetS t => match s.values with
    | .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) => match elems[idx.toNat]?, m.arrayElem? t with
        | some v, some ft => .Fallthrough st { s with values := ft.readS v :: vs }
        | _, _ => .Trap st "out of bounds array access"
      | _ => .Invalid "arrayGetS: not an array"
    | _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayGetS: ill-shaped operand stack"
  | .arraySet t => match s.values with
    | val :: .i32 idx :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array ty elems) =>
        if idx.toNat ≥ elems.length then .Trap st "out of bounds array access"
        else
          let pval := match m.arrayElem? t with | some ft => ft.pack val | none => val
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty (elems.set idx.toNat pval)) }
            { s with values := vs }
      | _ => .Invalid "arraySet: not an array"
    | _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arraySet: ill-shaped operand stack"
  | .arrayLen => match s.values with
    | .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array _ elems) =>
        .Fallthrough st { s with values := .i32 (UInt32.ofNat elems.length) :: vs }
      | _ => .Invalid "arrayLen: not an array"
    | .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayLen: ill-shaped operand stack"
  -- `array.fill $t`: [arrayref, d, val, n] → fill elems[d..d+n) with val.
  | .arrayFill t => match s.values with
    | .i32 n :: val :: .i32 d :: .anyref (some (.array addr)) :: vs => match st.gcHeap[addr]? with
      | some (.array ty elems) =>
        if d.toNat + n.toNat > elems.length then .Trap st "out of bounds array access"
        else
          let pval := match m.arrayElem? t with | some ft => ft.pack val | none => val
          let elems' := (List.range elems.length).map fun i =>
            if d.toNat ≤ i && i < d.toNat + n.toNat then pval else elems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty elems') } { s with values := vs }
      | _ => .Invalid "arrayFill: not an array"
    | _ :: _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayFill: ill-shaped operand stack"
  -- `array.copy $dt $st`: [dst, dstD, src, srcD, n] → copy elements.
  | .arrayCopy _ _ => match s.values with
    | .i32 n :: .i32 srcD :: .anyref (some (.array srcAddr)) :: .i32 dstD
        :: .anyref (some (.array dstAddr)) :: vs =>
      match st.gcHeap[srcAddr]?, st.gcHeap[dstAddr]? with
      | some (.array _ srcElems), some (.array dty dstElems) =>
        if srcD.toNat + n.toNat > srcElems.length || dstD.toNat + n.toNat > dstElems.length then
          .Trap st "out of bounds array access"
        else
          let dstElems' := (List.range dstElems.length).map fun i =>
            if dstD.toNat ≤ i && i < dstD.toNat + n.toNat then srcElems[srcD.toNat + (i - dstD.toNat)]!
            else dstElems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set dstAddr (.array dty dstElems') } { s with values := vs }
      | _, _ => .Invalid "arrayCopy: not an array"
    -- A null source or destination array reference traps, even when n = 0,
    -- mirroring every other array op (arrayGet/Set/Fill/...).
    | .i32 _ :: .i32 _ :: .anyref none :: _ => .Trap st "null array reference"
    | .i32 _ :: .i32 _ :: _ :: .i32 _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayCopy: ill-shaped operand stack"
  -- `array.new_data $t $d`: [off, n] → array of n elements read from data
  -- segment `d` (little-endian, sized by the element storage type).
  | .arrayNewData t d => match s.values with
    | .i32 n :: .i32 off :: vs => match m.arrayElem? t, st.dataSegments[d]? with
      | some ft, some (some bytes) =>
        let sz := ft.storage.byteSize
        if off.toNat + n.toNat * sz > bytes.length then .Trap st "out of bounds memory access"
        else
          let elems := (List.range n.toNat).map fun i => readStorageLE ft.storage bytes (off.toNat + i * sz)
          .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t elems] }
            { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
      | _, _ => .Trap st "out of bounds memory access"
    | _ => .Invalid "arrayNewData: ill-shaped operand stack"
  -- `array.init_data $t $d`: [arrayref, d, off, n] → write into existing array.
  | .arrayInitData t d => match s.values with
    | .i32 n :: .i32 off :: .i32 dstD :: .anyref (some (.array addr)) :: vs =>
      match m.arrayElem? t, st.gcHeap[addr]?, st.dataSegments[d]? with
      | some ft, some (.array ty elems), some segment =>
        let sz := ft.storage.byteSize
        let bytes := segment.getD []
        if dstD.toNat + n.toNat > elems.length then
          .Trap st "out of bounds array access"
        else if off.toNat + n.toNat * sz > bytes.length then
          .Trap st "out of bounds memory access"
        else
          let elems' := (List.range elems.length).map fun i =>
            if dstD.toNat ≤ i && i < dstD.toNat + n.toNat then
              readStorageLE ft.storage bytes (off.toNat + (i - dstD.toNat) * sz)
            else elems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty elems') } { s with values := vs }
      | _, _, _ => .Trap st "out of bounds memory access"
    | _ :: _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayInitData: ill-shaped operand stack"
  -- `array.new_elem`/`array.init_elem`: element-segment-sourced arrays. Only
  -- funcref segments (stored as func indices) are modelled.
  | .arrayNewElem t e => match s.values with
    | .i32 n :: .i32 off :: vs =>
      match st.elementSegments[e]?, st.elementValues[e]? with
      | some status, some cached =>
        let refs := if status.isSome then cached.getD [] else []
        if off.toNat + n.toNat > refs.length then .Trap st "out of bounds table access"
        else
          let elems := (List.range n.toNat).map fun i => refs[off.toNat + i]!
          .Fallthrough { st with gcHeap := st.gcHeap ++ [.array t elems] }
            { s with values := .anyref (some (.array st.gcHeap.length)) :: vs }
      | _, _ => .Trap st "out of bounds table access"
    | _ => .Invalid "arrayNewElem: ill-shaped operand stack"
  | .arrayInitElem _ e => match s.values with
    | .i32 n :: .i32 off :: .i32 dstD :: .anyref (some (.array addr)) :: vs =>
      match st.gcHeap[addr]?, st.elementSegments[e]?, st.elementValues[e]? with
      | some (.array ty elems), some status, some cached =>
        let refs := if status.isSome then cached.getD [] else []
        if dstD.toNat + n.toNat > elems.length then
          .Trap st "out of bounds array access"
        else if off.toNat + n.toNat > refs.length then
          .Trap st "out of bounds table access"
        else
          let elems' := (List.range elems.length).map fun i =>
            if dstD.toNat ≤ i && i < dstD.toNat + n.toNat then refs[off.toNat + (i - dstD.toNat)]!
            else elems[i]!
          .Fallthrough { st with gcHeap := st.gcHeap.set addr (.array ty elems') } { s with values := vs }
      | _, _, _ => .Trap st "out of bounds table access"
    | _ :: _ :: _ :: .anyref none :: _ => .Trap st "null array reference"
    | _ => .Invalid "arrayInitElem: ill-shaped operand stack"


end Wasm
