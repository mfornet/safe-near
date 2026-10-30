import Wasm.Syntax

/-!
# Validation

Section 3 of the specification, implemented with the algorithm of appendix
A.3: an operand stack of value types (or `unknown` after unconditional
control transfer) and a control stack of frames. Modules that pass are
wrapped as `ValidModule`, which instantiation and execution accept.

Every check carries a feature switch when the specification's version
depends on it (`Features`). The spec testsuite runs with every supported
feature on; `Features.nearcore` is what nearcore accepts.
-/

namespace Wasm

/-- Which optional features validation accepts. All are implemented by the
runtime; switching one off rejects modules that use it, as a reference
engine configured without it would. -/
structure Features where
  multiValue : Bool := true
  referenceTypes : Bool := true
  bulkMemory : Bool := true
  signExtension : Bool := true
  saturatingFloatToInt : Bool := true
  mutableGlobals : Bool := true
  /-- Constant expressions may `global.get` any earlier immutable global, not
  only imported ones (Wasm 3.0). -/
  constGlobalGet : Bool := true
deriving Repr, Inhabited

namespace Features
/-- Everything the runtime implements. -/
def all : Features := {}
/-- What nearcore enables, with `reftypes_bulk_memory` as a parameter. -/
def nearcore (reftypesBulkMemory : Bool) : Features :=
  { multiValue := false, referenceTypes := reftypesBulkMemory, bulkMemory := reftypesBulkMemory,
    constGlobalGet := false }
end Features

inductive ValidationError where
  /-- The module is invalid. -/
  | invalid (message : String)
  /-- The module uses a feature `Features` does not enable. -/
  | unsupported (feature : String)
deriving Repr, Inhabited

def ValidationError.message : ValidationError → String
  | .invalid m => m
  | .unsupported f => s!"unsupported feature: {f}"

namespace Validate

/-- A value type on the operand stack, or `unknown` below an unconditional
branch where any type is acceptable. -/
inductive OpType where
  | known (t : ValType)
  | unknown
deriving Repr, DecidableEq, Inhabited

inductive FrameKind where
  | block | loop | «if» | «else» | func
deriving Repr, DecidableEq

structure Frame where
  kind : FrameKind
  startTypes : List ValType
  endTypes : List ValType
  /-- Operand stack height at entry. -/
  height : Nat
  unreachable : Bool
deriving Repr

/-- The label types of a frame: what a branch to it carries. -/
def Frame.labelTypes (f : Frame) : List ValType :=
  if f.kind == .loop then f.startTypes else f.endTypes

/-- The static context of a function body. -/
structure Context where
  features : Features
  types : Array FuncType
  funcs : Array FuncType
  tables : Array TableType
  mems : Array MemType
  globals : Array GlobalType
  elems : Array RefType
  datas : Nat
  locals : Array ValType
  /-- Functions `ref.func` may name: those in element segments, exports and
  global initialisers. -/
  refs : Array Bool
  /-- The function's result types; `none` in constant expressions. -/
  «return» : Option (List ValType)

structure State where
  vals : Array OpType := #[]
  ctrls : Array Frame := #[]

abbrev M := StateT State (Except ValidationError)

def fail (message : String) : M α := throw (.invalid message)
def unsupported (feature : String) : M α := throw (.unsupported feature)

def require (b : Bool) (message : String) : M Unit := if b then pure () else fail message

def requireFeature (b : Bool) (feature : String) : M Unit :=
  if b then pure () else unsupported feature

/-! ## Operand and control stacks -/

def pushVal (t : OpType) : M Unit := modify fun s => { s with vals := s.vals.push t }

def pushType (t : ValType) : M Unit := pushVal (.known t)

def topFrame : M Frame := do
  match (← get).ctrls.back? with
  | some f => return f
  | none => fail "control stack empty"

def popVal : M OpType := do
  let s ← get
  let frame ← topFrame
  if s.vals.size = frame.height then
    if frame.unreachable then return .unknown else fail "type mismatch: stack underflow"
  let t := s.vals.back!
  set { s with vals := s.vals.pop }
  return t

def popExpect (expect : OpType) : M OpType := do
  let actual ← popVal
  if actual != expect && actual != .unknown && expect != .unknown then
    fail s!"type mismatch: expected {repr expect}, got {repr actual}"
  return actual

def popType (t : ValType) : M Unit := do let _ ← popExpect (.known t)

def pushTypes (ts : List ValType) : M Unit := ts.forM pushType

def popTypes (ts : List ValType) : M Unit := ts.reverse.forM popType

def pushCtrl (kind : FrameKind) (startTypes endTypes : List ValType) : M Unit := do
  let s ← get
  let frame : Frame := { kind, startTypes, endTypes, height := s.vals.size, unreachable := false }
  set { s with ctrls := s.ctrls.push frame }
  pushTypes startTypes

def popCtrl : M Frame := do
  let frame ← topFrame
  popTypes frame.endTypes
  let s ← get
  require (s.vals.size == frame.height) "type mismatch: values remain on the stack"
  set { s with ctrls := s.ctrls.pop }
  return frame

def labelTypes (label : Nat) : M (List ValType) := do
  let s ← get
  if h : label < s.ctrls.size then
    return (s.ctrls[s.ctrls.size - 1 - label]).labelTypes
  else fail "unknown label"

def markUnreachable : M Unit := do
  let s ← get
  let frame ← topFrame
  let ctrls := s.ctrls.set! (s.ctrls.size - 1) { frame with unreachable := true }
  set { s with vals := s.vals.shrink frame.height, ctrls }

/-! ## Helpers -/

def blockFuncType (ctx : Context) : BlockType → M FuncType
  | .empty => return { params := [], results := [] }
  | .val t => return { params := [], results := [t] }
  | .index i => do
    match ctx.types[i]? with
    | some ft => return ft
    | none => fail "unknown type"

def checkMultiValue (ctx : Context) (ft : FuncType) : M Unit :=
  requireFeature (ctx.features.multiValue || (ft.params.isEmpty && ft.results.length ≤ 1))
    "multi-value"

def checkRefFeature (ctx : Context) : M Unit :=
  requireFeature ctx.features.referenceTypes "reference-types"

def checkBulkFeature (ctx : Context) : M Unit :=
  requireFeature ctx.features.bulkMemory "bulk-memory"

def funcType (ctx : Context) (i : Nat) : M FuncType := do
  match ctx.funcs[i]? with
  | some ft => return ft
  | none => fail "unknown function"

def tableType (ctx : Context) (i : Nat) : M TableType := do
  match ctx.tables[i]? with
  | some t => return t
  | none => fail "unknown table"

def requireMemory (ctx : Context) : M Unit :=
  require (ctx.mems.size > 0) "unknown memory"

def globalType (ctx : Context) (i : Nat) : M GlobalType := do
  match ctx.globals[i]? with
  | some g => return g
  | none => fail "unknown global"

def localType (ctx : Context) (i : Nat) : M ValType := do
  match ctx.locals[i]? with
  | some t => return t
  | none => fail "unknown local"

/-- The operand and result types of a conversion. -/
def cvtTypes : CvtOp → NumType × NumType
  | .i32_wrap_i64 => (.i64, .i32)
  | .i32_trunc_f32_s | .i32_trunc_f32_u | .i32_trunc_sat_f32_s | .i32_trunc_sat_f32_u
  | .i32_reinterpret_f32 => (.f32, .i32)
  | .i32_trunc_f64_s | .i32_trunc_f64_u | .i32_trunc_sat_f64_s | .i32_trunc_sat_f64_u => (.f64, .i32)
  | .i64_extend_i32_s | .i64_extend_i32_u => (.i32, .i64)
  | .i64_trunc_f32_s | .i64_trunc_f32_u | .i64_trunc_sat_f32_s | .i64_trunc_sat_f32_u => (.f32, .i64)
  | .i64_trunc_f64_s | .i64_trunc_f64_u | .i64_trunc_sat_f64_s | .i64_trunc_sat_f64_u
  | .i64_reinterpret_f64 => (.f64, .i64)
  | .f32_convert_i32_s | .f32_convert_i32_u | .f32_reinterpret_i32 => (.i32, .f32)
  | .f32_convert_i64_s | .f32_convert_i64_u => (.i64, .f32)
  | .f32_demote_f64 => (.f64, .f32)
  | .f64_convert_i32_s | .f64_convert_i32_u => (.i32, .f64)
  | .f64_convert_i64_s | .f64_convert_i64_u | .f64_reinterpret_i64 => (.i64, .f64)
  | .f64_promote_f32 => (.f32, .f64)

def _root_.Wasm.CvtOp.isSaturating : CvtOp → Bool
  | .i32_trunc_sat_f32_s | .i32_trunc_sat_f32_u | .i32_trunc_sat_f64_s | .i32_trunc_sat_f64_u
  | .i64_trunc_sat_f32_s | .i64_trunc_sat_f32_u | .i64_trunc_sat_f64_s | .i64_trunc_sat_f64_u => true
  | _ => false

/-- Alignment may not exceed the access width. -/
def checkAlign (align width : Nat) : M Unit :=
  require ((1 <<< align) ≤ width) "alignment must not be larger than natural"

def OpType.isNum : OpType → Bool
  | .known (.num _) | .unknown => true
  | _ => false

def OpType.isRef : OpType → Bool
  | .known (.ref _) | .unknown => true
  | _ => false

/-! ## Instructions -/

mutual
/-- Type-check one instruction in the current state. -/
def instr (ctx : Context) : Instr → M Unit
  | .unreachable => markUnreachable
  | .nop => pure ()
  | .block bt body => do
    let ft ← blockFuncType ctx bt
    checkMultiValue ctx ft
    popTypes ft.params
    pushCtrl .block ft.params ft.results
    seq ctx body
    let frame ← popCtrl
    pushTypes frame.endTypes
  | .loop bt body => do
    let ft ← blockFuncType ctx bt
    checkMultiValue ctx ft
    popTypes ft.params
    pushCtrl .loop ft.params ft.results
    seq ctx body
    let frame ← popCtrl
    pushTypes frame.endTypes
  | .«if» bt thenBody elseBody => do
    let ft ← blockFuncType ctx bt
    checkMultiValue ctx ft
    popType .i32
    popTypes ft.params
    pushCtrl .if ft.params ft.results
    seq ctx thenBody
    let frame ← popCtrl
    if elseBody.isEmpty then
      require (frame.startTypes == frame.endTypes) "type mismatch: if without else"
    else
      pushCtrl .else frame.startTypes frame.endTypes
      seq ctx elseBody
      let _ ← popCtrl
    pushTypes frame.endTypes
  | .br l => do
    popTypes (← labelTypes l)
    markUnreachable
  | .br_if l => do
    popType .i32
    let ts ← labelTypes l
    popTypes ts
    pushTypes ts
  | .br_table ls d => do
    popType .i32
    let dts ← labelTypes d
    for l in ls do
      let ts ← labelTypes l
      require (ts.length == dts.length) "type mismatch: br_table arity"
      -- Pop against the label's types and push back what was found, so an
      -- `unknown` operand stays `unknown` for the next label.
      let popped ← ts.reverse.mapM fun t => popExpect (.known t)
      popped.reverse.forM pushVal
    popTypes dts
    markUnreachable
  | .return => do
    match ctx.return with
    | some ts => popTypes ts; markUnreachable
    | none => fail "return outside a function"
  | .call f => do
    let ft ← funcType ctx f
    popTypes ft.params
    pushTypes ft.results
  | .call_indirect ty table => do
    let tt ← tableType ctx table
    require (tt.elem == .funcref) "type mismatch: call_indirect on a non-funcref table"
    let ft ← match ctx.types[ty]? with
      | some ft => pure ft
      | none => fail "unknown type"
    popType .i32
    popTypes ft.params
    pushTypes ft.results
  | .ref_null t => do checkRefFeature ctx; pushType (.ref t)
  | .ref_is_null => do
    checkRefFeature ctx
    let t ← popVal
    require t.isRef "type mismatch: ref.is_null expects a reference"
    pushType .i32
  | .ref_func f => do
    checkRefFeature ctx
    let _ ← funcType ctx f
    require (ctx.refs[f]?.getD false) "undeclared function reference"
    pushType .funcref
  | .drop => do let _ ← popVal
  | .select none => do
    popType .i32
    let t1 ← popVal
    let t2 ← popVal
    require (t1.isNum && t2.isNum) "type mismatch: select without a type needs numbers"
    require (t1 == t2 || t1 == .unknown || t2 == .unknown) "type mismatch: select operands"
    pushVal (if t1 == .unknown then t2 else t1)
  | .select (some ts) => do
    checkRefFeature ctx
    match ts with
    | [t] =>
      popType .i32
      popType t
      popType t
      pushType t
    | _ => fail "invalid result arity"
  | .local_get i => do pushType (← localType ctx i)
  | .local_set i => do popType (← localType ctx i)
  | .local_tee i => do
    let t ← localType ctx i
    popType t
    pushType t
  | .global_get i => do pushType (← globalType ctx i).type
  | .global_set i => do
    let g ← globalType ctx i
    require g.mutable "global is immutable"
    popType g.type
  | .table_get t => do
    checkRefFeature ctx
    let tt ← tableType ctx t
    popType .i32
    pushType (.ref tt.elem)
  | .table_set t => do
    checkRefFeature ctx
    let tt ← tableType ctx t
    popType (.ref tt.elem)
    popType .i32
  | .table_size t => do
    checkRefFeature ctx
    let _ ← tableType ctx t
    pushType .i32
  | .table_grow t => do
    checkRefFeature ctx
    let tt ← tableType ctx t
    popType .i32
    popType (.ref tt.elem)
    pushType .i32
  | .table_fill t => do
    checkRefFeature ctx
    let tt ← tableType ctx t
    popType .i32
    popType (.ref tt.elem)
    popType .i32
  | .table_copy dst src => do
    checkBulkFeature ctx
    let d ← tableType ctx dst
    let s ← tableType ctx src
    require (d.elem == s.elem) "type mismatch: table.copy element types"
    popType .i32; popType .i32; popType .i32
  | .table_init t e => do
    checkBulkFeature ctx
    let tt ← tableType ctx t
    match ctx.elems[e]? with
    | some et => require (et == tt.elem) "type mismatch: table.init element types"
    | none => fail "unknown elem segment"
    popType .i32; popType .i32; popType .i32
  | .elem_drop e => do
    checkBulkFeature ctx
    require (e < ctx.elems.size) "unknown elem segment"
  | .load t packed arg => do
    requireMemory ctx
    let width := match packed with
      | some p => p.bits / 8
      | none => t.byteWidth
    checkAlign arg.align width
    require (arg.offset < 2 ^ 32) "offset out of range"
    popType .i32
    pushType (.num t)
  | .store t bits arg => do
    requireMemory ctx
    let width := match bits with
      | some b => b / 8
      | none => t.byteWidth
    checkAlign arg.align width
    require (arg.offset < 2 ^ 32) "offset out of range"
    popType (.num t)
    popType .i32
  | .memory_size => do requireMemory ctx; pushType .i32
  | .memory_grow => do requireMemory ctx; popType .i32; pushType .i32
  | .memory_fill => do
    checkBulkFeature ctx
    requireMemory ctx
    popType .i32; popType .i32; popType .i32
  | .memory_copy => do
    checkBulkFeature ctx
    requireMemory ctx
    popType .i32; popType .i32; popType .i32
  | .memory_init d => do
    checkBulkFeature ctx
    requireMemory ctx
    require (d < ctx.datas) "unknown data segment"
    popType .i32; popType .i32; popType .i32
  | .data_drop d => do
    checkBulkFeature ctx
    require (d < ctx.datas) "unknown data segment"
  | .i32_const _ => pushType .i32
  | .i64_const _ => pushType .i64
  | .f32_const _ => pushType .f32
  | .f64_const _ => pushType .f64
  | .i32_eqz => do popType .i32; pushType .i32
  | .i64_eqz => do popType .i64; pushType .i32
  | .i32_unop op => do
    if op matches .extend8_s | .extend16_s then
      requireFeature ctx.features.signExtension "sign-extension"
    if op == .extend32_s then fail "i32.extend32_s does not exist"
    popType .i32; pushType .i32
  | .i64_unop op => do
    if op matches .extend8_s | .extend16_s | .extend32_s then
      requireFeature ctx.features.signExtension "sign-extension"
    popType .i64; pushType .i64
  | .i32_binop _ => do popType .i32; popType .i32; pushType .i32
  | .i64_binop _ => do popType .i64; popType .i64; pushType .i64
  | .i32_relop _ => do popType .i32; popType .i32; pushType .i32
  | .i64_relop _ => do popType .i64; popType .i64; pushType .i32
  | .f32_unop _ => do popType .f32; pushType .f32
  | .f64_unop _ => do popType .f64; pushType .f64
  | .f32_binop _ => do popType .f32; popType .f32; pushType .f32
  | .f64_binop _ => do popType .f64; popType .f64; pushType .f64
  | .f32_relop _ => do popType .f32; popType .f32; pushType .i32
  | .f64_relop _ => do popType .f64; popType .f64; pushType .i32
  | .cvt op => do
    if op.isSaturating then
      requireFeature ctx.features.saturatingFloatToInt "saturating-float-to-int"
    let (from_, to) := cvtTypes op
    popType (.num from_)
    pushType (.num to)

def seq (ctx : Context) : List Instr → M Unit
  | [] => pure ()
  | i :: rest => do instr ctx i; seq ctx rest
end

/-- Check a function body: locals are in scope, the body leaves exactly the
results. -/
def body (ctx : Context) (results : List ValType) (code : Expr) : Except ValidationError Unit := do
  let run : M Unit := do
    pushCtrl .func [] results
    seq ctx code
    let _ ← popCtrl
  let _ ← run.run {}

/-! ## Constant expressions -/

/-- Constant expressions may only use constants, `ref.null`, `ref.func` and
`global.get` of an immutable global among the first `visibleGlobals`: the
imported ones, or with `Features.constGlobalGet` every earlier one. -/
def constInstr (importedGlobals visibleGlobals : Nat) (ctx : Context) : Instr → M Unit
  | .i32_const _ | .i64_const _ | .f32_const _ | .f64_const _ | .ref_null _ | .ref_func _ => pure ()
  | .global_get i => do
    require (i < visibleGlobals) "unknown global: constant expression"
    requireFeature (i < importedGlobals || ctx.features.constGlobalGet) "const-global-get"
    let g ← globalType ctx i
    require (!g.mutable) "constant expression required: mutable global"
  | .i32_binop op | .i64_binop op =>
    if op matches .add | .sub | .mul then unsupported "extended-const"
    else fail "constant expression required"
  | _ => fail "constant expression required"

def constExpr (importedGlobals visibleGlobals : Nat) (ctx : Context) (t : ValType) (code : Expr) :
    Except ValidationError Unit := do
  let run : M Unit := do
    code.forM (constInstr importedGlobals visibleGlobals ctx)
    pushCtrl .func [] [t]
    seq ctx code
    let _ ← popCtrl
  let _ ← run.run {}

/-! ## Module -/

def limitsOk (l : Limits) (range : Nat) (what : String) : Except ValidationError Unit := do
  if l.min > range then throw (.invalid s!"{what} size must be at most {range}")
  if let some max := l.max then
    if max > range then throw (.invalid s!"{what} size must be at most {range}")
    if max < l.min then throw (.invalid s!"size minimum must not be greater than maximum")

def tableTypeOk (f : Features) (t : TableType) : Except ValidationError Unit := do
  if t.elem != .funcref && !f.referenceTypes then throw (.unsupported "reference-types")
  limitsOk t.limits (2 ^ 32 - 1) "table"

def memTypeOk (t : MemType) : Except ValidationError Unit :=
  limitsOk t.limits 65536 "memory"

def globalTypeOk (f : Features) (g : GlobalType) : Except ValidationError Unit := do
  if let .ref _ := g.type then
    if !f.referenceTypes then throw (.unsupported "reference-types")

/-- Functions that `ref.func` may name. -/
def declaredRefs (m : Module) (funcCount : Nat) : Array Bool := Id.run do
  let mut refs := Array.replicate funcCount false
  let mark (refs : Array Bool) : Expr → Array Bool
    | [.ref_func f] => if f < refs.size then refs.set! f true else refs
    | _ => refs
  for e in m.elems do
    for init in e.init do refs := mark refs init
  for g in m.globals do refs := mark refs g.init
  for e in m.exports do
    if let .func f := e.desc then
      if f < refs.size then refs := refs.set! f true
  return refs

/-- Validate everything in a module but its function bodies, and give the
context the bodies are checked in. -/
def moduleContext (features : Features) (m : Module) : Except ValidationError Context := do
  -- Types.
  for ft in m.types do
    if !features.multiValue && ft.results.length > 1 then throw (.unsupported "multi-value")
    for t in ft.params ++ ft.results do
      if let .ref _ := t then if !features.referenceTypes then throw (.unsupported "reference-types")
  -- Imports contribute to the index spaces before the module's own definitions.
  let mut funcs : Array FuncType := #[]
  let mut tables : Array TableType := #[]
  let mut mems : Array MemType := #[]
  let mut globals : Array GlobalType := #[]
  for imp in m.imports do
    match imp.desc with
    | .func ty =>
      match m.types[ty]? with
      | some ft => funcs := funcs.push ft
      | none => throw (.invalid "unknown type")
    | .table tt => tableTypeOk features tt; tables := tables.push tt
    | .mem mt => memTypeOk mt; mems := mems.push mt
    | .global gt =>
      globalTypeOk features gt
      if gt.mutable && !features.mutableGlobals then throw (.unsupported "mutable-globals")
      globals := globals.push gt
  let importedGlobals := globals.size
  for f in m.funcs do
    match m.types[f.type]? with
    | some ft => funcs := funcs.push ft
    | none => throw (.invalid "unknown type")
  for t in m.tables do tableTypeOk features t.type; tables := tables.push t.type
  for mem in m.mems do memTypeOk mem.type; mems := mems.push mem.type
  for g in m.globals do globalTypeOk features g.type; globals := globals.push g.type
  if mems.size > 1 then throw (.unsupported "multi-memory")
  if tables.size > 1 && !features.referenceTypes then throw (.unsupported "reference-types")
  let ctx : Context := {
    features, types := m.types, funcs, tables, mems, globals,
    elems := m.elems.map (·.type), datas := m.datas.size, locals := #[],
    refs := declaredRefs m funcs.size, «return» := none }
  -- Globals: constant initialisers of the declared type, seeing earlier globals.
  for h : i in [0:m.globals.size] do
    let g := m.globals[i]
    constExpr importedGlobals (importedGlobals + i) ctx g.type.type g.init
  let allGlobals := globals.size
  -- Element segments.
  for e in m.elems do
    if e.type != .funcref && !features.referenceTypes then throw (.unsupported "reference-types")
    for init in e.init do constExpr importedGlobals allGlobals ctx (.ref e.type) init
    match e.mode with
    | .active table offset =>
      match tables[table]? with
      | some tt =>
        if tt.elem != e.type then throw (.invalid "type mismatch: element segment type")
      | none => throw (.invalid "unknown table")
      constExpr importedGlobals allGlobals ctx .i32 offset
    | .passive | .declarative => if !features.bulkMemory then throw (.unsupported "bulk-memory")
  -- Data segments.
  for d in m.datas do
    match d.mode with
    | .active mem offset =>
      if mem ≥ mems.size then throw (.invalid "unknown memory")
      constExpr importedGlobals allGlobals ctx .i32 offset
    | .passive => if !features.bulkMemory then throw (.unsupported "bulk-memory")
    | .declarative => throw (.invalid "declarative data segment")
  -- Start function.
  if let some s := m.start then
    match funcs[s]? with
    | some ft =>
      if !(ft.params.isEmpty && ft.results.isEmpty) then
        throw (.invalid "start function must have type [] -> []")
    | none => throw (.invalid "unknown function")
  -- Exports: unique names, indices in range.
  let mut names : Array String := #[]
  for e in m.exports do
    if names.contains e.name then throw (.invalid "duplicate export name")
    names := names.push e.name
    let ok := match e.desc with
      | .func i => i < funcs.size
      | .table i => i < tables.size
      | .mem i => i < mems.size
      | .global i => i < globals.size
    if !ok then throw (.invalid s!"unknown export index: {e.name}")
  return ctx

/-- Validate one function body in the module context. -/
def funcOk (ctx : Context) (f : Func) : Except ValidationError Unit := do
  let ft := ctx.types[f.type]!
  for t in f.locals do
    if let .ref _ := t then if !ctx.features.referenceTypes then throw (.unsupported "reference-types")
  body { ctx with locals := (ft.params ++ f.locals).toArray, «return» := some ft.results }
    ft.results f.body

/-- Validate a module. -/
def module (features : Features) (m : Module) : Except ValidationError Unit := do
  let ctx ← moduleContext features m
  -- Function bodies.
  for f in m.funcs do funcOk ctx f

end Validate

/-- A module that passed validation. Only `Module.validate` builds one. -/
structure ValidModule where
  private mk ::
  module : Module
  features : Features

def Module.validate (features : Features) (m : Module) : Except ValidationError ValidModule := do
  Validate.module features m
  return ⟨m, features⟩

namespace Validate

theorem forIn_ok {α ε : Type} (l : List α) (g : α → Except ε Unit) (h : ∀ x ∈ l, g x = .ok ()) :
    (forIn l PUnit.unit fun x _ => do g x; pure (ForInStep.yield PUnit.unit) : Except ε PUnit) =
      .ok PUnit.unit := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.forIn_cons, h x List.mem_cons_self]
    exact ih fun y hy => h y (List.mem_cons_of_mem x hy)

/-- A module validates when everything but its bodies does, and each body
does in the context that gives. -/
theorem module_ok {features : Features} {m : Module} {ctx : Context}
    (hc : moduleContext features m = .ok ctx) (hf : ∀ f ∈ m.funcs.toList, funcOk ctx f = .ok ()) :
    module features m = .ok () := by
  unfold module
  rw [hc]
  simp only [bind, Except.bind, ← Array.forIn_toList]
  have := forIn_ok _ _ hf
  simp only [bind, Except.bind] at this
  rw [this]
  rfl

end Validate

theorem Module.validate_ok {features : Features} {m : Module} (h : Validate.module features m = .ok ()) :
    ∃ vm, m.validate features = .ok vm ∧ vm.module = m :=
  ⟨⟨m, features⟩, by simp [Module.validate, h, bind, Except.bind, pure, Except.pure], rfl⟩

end Wasm
