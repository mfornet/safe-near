/-!
# Wasm abstract syntax

The structure of a module as the WebAssembly core specification defines it
(section 2, "Structure"), restricted to the features nearcore enables: the
MVP, mutable globals, sign extension, saturating truncation, reference types
and bulk memory. There is one memory and any number of tables; `memory64`,
multi-memory, SIMD, exceptions, tail calls, GC and function references are
not representable.

Multi-value is not enabled either, but block types still carry a type index
(`BlockType.index`): the binary format allows it, and rejecting `[] -> [t]`
blocks written that way, or multi-value signatures, is the validator's job,
where the feature flags live.
-/

namespace Wasm

/-! ## Types -/

/-- Number types. -/
inductive NumType where
  | i32 | i64 | f32 | f64
deriving Repr, DecidableEq, Inhabited

/-- Size in bytes of a value of the type. -/
def NumType.byteWidth : NumType → Nat
  | .i32 | .f32 => 4
  | .i64 | .f64 => 8

/-- Reference types. -/
inductive RefType where
  | funcref | externref
deriving Repr, DecidableEq, Inhabited

/-- Value types. -/
inductive ValType where
  | num (t : NumType)
  | ref (t : RefType)
deriving Repr, DecidableEq, Inhabited

namespace ValType
abbrev i32 : ValType := .num .i32
abbrev i64 : ValType := .num .i64
abbrev f32 : ValType := .num .f32
abbrev f64 : ValType := .num .f64
abbrev funcref : ValType := .ref .funcref
abbrev externref : ValType := .ref .externref
end ValType

/-- Function types: parameters and results. -/
structure FuncType where
  params : List ValType
  results : List ValType
deriving Repr, DecidableEq, Inhabited

/-- Limits of a memory or table: a minimum and an optional maximum. -/
structure Limits where
  min : Nat
  max : Option Nat
deriving Repr, DecidableEq, Inhabited

structure TableType where
  elem : RefType
  limits : Limits
deriving Repr, DecidableEq, Inhabited

/-- Memory types. Limits are in pages of 64 KiB. -/
structure MemType where
  limits : Limits
deriving Repr, DecidableEq, Inhabited

structure GlobalType where
  type : ValType
  mutable : Bool
deriving Repr, DecidableEq, Inhabited

/-! ## Instructions -/

/-- The result type of a structured instruction. -/
inductive BlockType where
  | empty
  | val (t : ValType)
  /-- A type index into the module's types. -/
  | index (i : Nat)
deriving Repr, DecidableEq, Inhabited

/-- Integer unary operators (both widths). -/
inductive IUnOp where
  | clz | ctz | popcnt
  | extend8_s | extend16_s
  /-- `i64` only. -/
  | extend32_s
deriving Repr, DecidableEq, Inhabited

/-- Integer binary operators. -/
inductive IBinOp where
  | add | sub | mul | div_s | div_u | rem_s | rem_u
  | and | or | xor | shl | shr_s | shr_u | rotl | rotr
deriving Repr, DecidableEq, Inhabited

/-- Integer comparison operators. -/
inductive IRelOp where
  | eq | ne | lt_s | lt_u | gt_s | gt_u | le_s | le_u | ge_s | ge_u
deriving Repr, DecidableEq, Inhabited

/-- Floating-point unary operators. -/
inductive FUnOp where
  | abs | neg | ceil | floor | trunc | nearest | sqrt
deriving Repr, DecidableEq, Inhabited

/-- Floating-point binary operators. -/
inductive FBinOp where
  | add | sub | mul | div | min | max | copysign
deriving Repr, DecidableEq, Inhabited

/-- Floating-point comparison operators. -/
inductive FRelOp where
  | eq | ne | lt | gt | le | ge
deriving Repr, DecidableEq, Inhabited

/-- Conversions between number types. The first type is the result, the
second the operand, following the instruction names (`i32.wrap_i64`). -/
inductive CvtOp where
  | i32_wrap_i64
  | i32_trunc_f32_s | i32_trunc_f32_u | i32_trunc_f64_s | i32_trunc_f64_u
  | i64_extend_i32_s | i64_extend_i32_u
  | i64_trunc_f32_s | i64_trunc_f32_u | i64_trunc_f64_s | i64_trunc_f64_u
  | f32_convert_i32_s | f32_convert_i32_u | f32_convert_i64_s | f32_convert_i64_u
  | f32_demote_f64
  | f64_convert_i32_s | f64_convert_i32_u | f64_convert_i64_s | f64_convert_i64_u
  | f64_promote_f32
  | i32_reinterpret_f32 | i64_reinterpret_f64 | f32_reinterpret_i32 | f64_reinterpret_i64
  | i32_trunc_sat_f32_s | i32_trunc_sat_f32_u | i32_trunc_sat_f64_s | i32_trunc_sat_f64_u
  | i64_trunc_sat_f32_s | i64_trunc_sat_f32_u | i64_trunc_sat_f64_s | i64_trunc_sat_f64_u
deriving Repr, DecidableEq, Inhabited

/-- Memory access immediate: alignment exponent and offset. -/
structure MemArg where
  align : Nat
  offset : Nat
deriving Repr, DecidableEq, Inhabited

/-- Width and signedness of a narrow load (`i32.load8_s` is `(8, true)`). -/
structure Packed where
  bits : Nat
  signed : Bool
deriving Repr, DecidableEq, Inhabited

inductive Instr where
  -- Control
  | unreachable
  | nop
  | block (bt : BlockType) (body : List Instr)
  | loop (bt : BlockType) (body : List Instr)
  | «if» (bt : BlockType) (thenBody elseBody : List Instr)
  | br (label : Nat)
  | br_if (label : Nat)
  | br_table (labels : List Nat) (default : Nat)
  | «return»
  | call (func : Nat)
  | call_indirect (type : Nat) (table : Nat)
  -- Reference
  | ref_null (t : RefType)
  | ref_is_null
  | ref_func (func : Nat)
  -- Parametric
  | drop
  /-- `select` with an optional explicit result type list. -/
  | select (types : Option (List ValType))
  -- Variable
  | local_get (i : Nat)
  | local_set (i : Nat)
  | local_tee (i : Nat)
  | global_get (i : Nat)
  | global_set (i : Nat)
  -- Table
  | table_get (table : Nat)
  | table_set (table : Nat)
  | table_size (table : Nat)
  | table_grow (table : Nat)
  | table_fill (table : Nat)
  | table_copy (dst src : Nat)
  | table_init (table elem : Nat)
  | elem_drop (elem : Nat)
  -- Memory
  /-- `t.load` when `packed = none`, else `t.loadN_sx`. -/
  | load (t : NumType) (packed : Option Packed) (arg : MemArg)
  /-- `t.store` when `bits = none`, else `t.storeN`. -/
  | store (t : NumType) (bits : Option Nat) (arg : MemArg)
  | memory_size
  | memory_grow
  | memory_fill
  | memory_copy
  | memory_init (data : Nat)
  | data_drop (data : Nat)
  -- Numeric
  | i32_const (n : UInt32)
  | i64_const (n : UInt64)
  /-- Bit pattern of the `f32`. -/
  | f32_const (bits : UInt32)
  /-- Bit pattern of the `f64`. -/
  | f64_const (bits : UInt64)
  | i32_eqz
  | i64_eqz
  | i32_unop (op : IUnOp)
  | i64_unop (op : IUnOp)
  | i32_binop (op : IBinOp)
  | i64_binop (op : IBinOp)
  | i32_relop (op : IRelOp)
  | i64_relop (op : IRelOp)
  | f32_unop (op : FUnOp)
  | f64_unop (op : FUnOp)
  | f32_binop (op : FBinOp)
  | f64_binop (op : FBinOp)
  | f32_relop (op : FRelOp)
  | f64_relop (op : FRelOp)
  | cvt (op : CvtOp)
deriving Repr, Inhabited

/-- A sequence of instructions. Constant expressions are the same type; the
validator restricts them. -/
abbrev Expr := List Instr

/-! ## Modules -/

structure Func where
  type : Nat
  locals : List ValType
  body : Expr
deriving Repr, Inhabited

structure Table where
  type : TableType
deriving Repr, Inhabited

structure Mem where
  type : MemType
deriving Repr, Inhabited

structure Global where
  type : GlobalType
  init : Expr
deriving Repr, Inhabited

/-- Where an element or data segment is placed. -/
inductive SegmentMode where
  | passive
  | active (index : Nat) (offset : Expr)
  /-- Element segments only: usable by `ref.func`, never instantiated. -/
  | declarative
deriving Repr, Inhabited

structure Elem where
  type : RefType
  /-- One constant expression per element. -/
  init : List Expr
  mode : SegmentMode
deriving Repr, Inhabited

structure Data where
  init : ByteArray
  mode : SegmentMode
deriving Inhabited

inductive ImportDesc where
  | func (type : Nat)
  | table (type : TableType)
  | mem (type : MemType)
  | global (type : GlobalType)
deriving Repr, Inhabited

structure Import where
  module : String
  name : String
  desc : ImportDesc
deriving Repr, Inhabited

inductive ExportDesc where
  | func (i : Nat)
  | table (i : Nat)
  | mem (i : Nat)
  | global (i : Nat)
deriving Repr, DecidableEq, Inhabited

structure Export where
  name : String
  desc : ExportDesc
deriving Repr, Inhabited

structure Module where
  types : Array FuncType := #[]
  funcs : Array Func := #[]
  tables : Array Table := #[]
  mems : Array Mem := #[]
  globals : Array Global := #[]
  elems : Array Elem := #[]
  datas : Array Data := #[]
  start : Option Nat := none
  imports : Array Import := #[]
  exports : Array Export := #[]
deriving Inhabited

namespace Module

/-- The function index an export names. -/
def exportFunc? (m : Module) (name : String) : Option Nat :=
  m.exports.findSome? fun e =>
    match e.desc with
    | .func i => if e.name == name then some i else none
    | _ => none

/-- The type of the function at index `i`, imported functions first. -/
def funcType? (m : Module) (i : Nat) : Option FuncType :=
  let imported := m.imports.filterMap fun imp => match imp.desc with
    | .func ty => m.types[ty]?
    | _ => none
  if h : i < imported.size then some imported[i]
  else (m.funcs[i - imported.size]?).bind fun f => m.types[f.type]?

/-- The function imports, in order, with their types. -/
def importedFuncTypes (m : Module) : List (String × String × FuncType) :=
  m.imports.toList.filterMap fun imp => match imp.desc with
    | .func ty => m.types[ty]?.map fun ft => (imp.module, imp.name, ft)
    | _ => none

end Module

end Wasm
