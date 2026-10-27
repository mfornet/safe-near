import Wasm.Exec
import Wasm.Validate

/-!
# Instantiation and linking

Section 4.5 of the specification. `instantiateModule` takes a validated module
and one extern value per import, allocates its instances in the store,
evaluates its global initialisers and runs its active segments, and returns
the module instance; `instantiate` also runs the start function. Imports are
checked against the import declarations (`LinkError.incompatible`), which is
what `assert_unlinkable` tests.

Allocation is written as folds over the module's sections so that proofs
can follow it (`Wasm.LinkInvariant`): instantiation adds Wasm functions
only, and never touches the host state.

`Registry` is the name resolution the testsuite's `register` and ordinary
two-level import names need: a list of named module instances, host modules
included, whose exports imports resolve to.
-/

namespace Wasm

inductive LinkError (H : Type) where
  | unknownImport (module name : String)
  | incompatible (module name : String) (reason : String)
  /-- Instantiation trapped (an active segment out of bounds, or the start
  function). The store carries the effects up to the trap, which persist. -/
  | trap (reason : Trap) (store : Store H)
  | internal (message : String)

def LinkError.message : LinkError H → String
  | .unknownImport m n => s!"unknown import: {m}.{n}"
  | .incompatible m n r => s!"incompatible import type: {m}.{n}: {r}"
  | .trap t _ => t.message
  | .internal m => m

namespace Link

/-- Allocate a host module in the store; its exports resolve imports. -/
def allocateHost (store : Store H) (hm : HostModule H) : Store H × ModuleInst := Id.run do
  let mut store := store
  let mut inst : ModuleInst := {}
  for (name, fn) in hm.funcs do
    let (s, addr) := store.allocFunc (.host fn)
    store := s
    inst := { inst with funcAddrs := inst.funcAddrs.push addr,
                        exports := inst.exports.push (name, .func addr) }
  for (name, type, value) in hm.globals do
    let (s, addr) := store.allocGlobal { type, value }
    store := s
    inst := { inst with globalAddrs := inst.globalAddrs.push addr,
                        exports := inst.exports.push (name, .global addr) }
  for (name, tt) in hm.tables do
    let table : TableInst :=
      { elemType := tt.elem, elems := Array.replicate tt.limits.min (.null tt.elem),
        max := tt.limits.max }
    let (s, addr) := store.allocTable table
    store := s
    inst := { inst with tableAddrs := inst.tableAddrs.push addr,
                        exports := inst.exports.push (name, .table addr) }
  for (name, mt) in hm.mems do
    let (s, addr) := store.allocMem (Memory.new mt.limits.min mt.limits.max)
    store := s
    inst := { inst with memAddrs := inst.memAddrs.push addr,
                        exports := inst.exports.push (name, .mem addr) }
  let (store', _) := store.allocModule inst
  return (store', inst)

/-- Evaluate a constant expression. -/
def evalConst (store : Store H) (inst : ModuleInst) : Expr → Except (LinkError H) Value
  | [.i32_const n] => .ok (.i32 n)
  | [.i64_const n] => .ok (.i64 n)
  | [.f32_const b] => .ok (.f32 b)
  | [.f64_const b] => .ok (.f64 b)
  | [.ref_null t] => .ok (.ref (.null t))
  | [.ref_func f] =>
    match inst.funcAddrs[f]? with
    | some addr => .ok (.ref (.func addr))
    | none => .error (.internal "ref.func: unknown function")
  | [.global_get g] =>
    match inst.globalAddrs[g]?.bind (store.globals[·]?) with
    | some gi => .ok gi.value
    | none => .error (.internal "global.get: unknown global")
  | _ => .error (.internal "unsupported constant expression")

def limitsMatch (actual : Limits) (declared : Limits) : Bool :=
  actual.min ≥ declared.min &&
    (match declared.max with
      | none => true
      | some dm => actual.max.any (· ≤ dm))

/-- Check one extern value against an import declaration of module `m`. -/
def checkImport (store : Store H) (m : Module) (imp : Import) (ext : ExternVal) :
    Except (LinkError H) Unit := do
  let bad (r : String) : Except (LinkError H) Unit := .error (.incompatible imp.module imp.name r)
  match imp.desc, ext with
  | .func ty, .func addr =>
    match store.funcs[addr]?, m.types[ty]? with
    | some fn, some ft => if fn.type == ft then pure () else bad "function type"
    | _, _ => bad "function"
  | .table tt, .table addr =>
    match store.tables[addr]? with
    | some t =>
      if t.elemType != tt.elem then bad "table element type"
      else if !limitsMatch { min := t.elems.size, max := t.max } tt.limits then bad "table limits"
      else pure ()
    | none => bad "dangling table"
  | .mem mt, .mem addr =>
    match store.mems[addr]? with
    | some mem =>
      if !limitsMatch { min := mem.size, max := mem.max } mt.limits then bad "memory limits"
      else pure ()
    | none => bad "dangling memory"
  | .global gt, .global addr =>
    match store.globals[addr]? with
    | some g => if g.type == gt then pure () else bad "global type"
    | none => bad "dangling global"
  | _, _ => bad "kind"

def checkImports (store : Store H) (m : Module) : List (Import × ExternVal) →
    Except (LinkError H) Unit
  | [] => .ok ()
  | (imp, ext) :: rest => do
    checkImport store m imp ext
    checkImports store m rest

/-! ## Allocation, one section at a time -/

/-- The imported addresses, by index space. -/
def importAddrs (imports : List ExternVal) : ModuleInst :=
  imports.foldl (init := {}) fun inst ext =>
    match ext with
    | .func a => { inst with funcAddrs := inst.funcAddrs.push a }
    | .table a => { inst with tableAddrs := inst.tableAddrs.push a }
    | .mem a => { inst with memAddrs := inst.memAddrs.push a }
    | .global a => { inst with globalAddrs := inst.globalAddrs.push a }

def allocFuncs (store : Store H) (types : Array FuncType) (instAddr : Nat) (funcs : List Func) :
    Store H × Array Nat :=
  funcs.foldl (init := (store, #[])) fun (store, addrs) f =>
    let (store, addr) := store.allocFunc (.wasm types[f.type]! instAddr f)
    (store, addrs.push addr)

def allocTables (store : Store H) (tables : List Table) : Store H × Array Nat :=
  tables.foldl (init := (store, #[])) fun (store, addrs) t =>
    let tt := t.type
    let table : TableInst :=
      { elemType := tt.elem, elems := Array.replicate tt.limits.min (.null tt.elem),
        max := tt.limits.max }
    let (store, addr) := store.allocTable table
    (store, addrs.push addr)

def allocMems (store : Store H) (mems : List Mem) : Store H × Array Nat :=
  mems.foldl (init := (store, #[])) fun (store, addrs) mem =>
    let (store, addr) := store.allocMem (Memory.new mem.type.limits.min mem.type.limits.max)
    (store, addrs.push addr)

/-- Globals see the imports and the globals allocated before them. -/
def allocGlobals (store : Store H) (inst : ModuleInst) : List Global →
    Except (LinkError H) (Store H × ModuleInst)
  | [] => .ok (store, inst)
  | g :: rest =>
    match evalConst store inst g.init with
    | .error e => .error e
    | .ok value =>
      let (store, addr) := store.allocGlobal { type := g.type, value }
      allocGlobals store { inst with globalAddrs := inst.globalAddrs.push addr } rest

def evalRefs (store : Store H) (inst : ModuleInst) : List Expr → Except (LinkError H) (List Ref)
  | [] => .ok []
  | init :: rest =>
    match evalConst store inst init with
    | .error e => .error e
    | .ok (.ref r) => (evalRefs store inst rest).map (r :: ·)
    | .ok _ => .error (.internal "element initialiser is not a reference")

def allocElems (store : Store H) (inst : ModuleInst) : List Elem →
    Except (LinkError H) (Store H × Array Nat)
  | [] => .ok (store, #[])
  | e :: rest =>
    match evalRefs store inst e.init with
    | .error err => .error err
    | .ok refs =>
      let (store, addr) := store.allocElem { elems := refs.toArray }
      match allocElems store inst rest with
      | .error err => .error err
      | .ok (store, addrs) => .ok (store, #[addr] ++ addrs)

def allocDatas (store : Store H) (datas : List Data) : Store H × Array Nat :=
  datas.foldl (init := (store, #[])) fun (store, addrs) d =>
    let (store, addr) := store.allocData { bytes := d.init }
    (store, addrs.push addr)

def exportsOf (inst : ModuleInst) (exports : Array Export) : Array (String × ExternVal) :=
  exports.map fun e => (e.name, match e.desc with
    | .func i => .func inst.funcAddrs[i]!
    | .table i => .table inst.tableAddrs[i]!
    | .mem i => .mem inst.memAddrs[i]!
    | .global i => .global inst.globalAddrs[i]!)

/-! ## Segment initialisation -/

/-- Write an active element segment into its table, or drop a declarative one.
A trap leaves the store as it is. -/
def initElem (store : Store H) (inst : ModuleInst) (i : Nat) (e : Elem) :
    Except (LinkError H) (Store H) :=
  match e.mode with
  | .active table offset =>
    match evalConst store inst offset with
    | .error err => .error err
    | .ok off =>
      let seg := store.elems[inst.elemAddrs[i]!]!
      match Exec.tableOf store inst table with
      | none => .error (.internal "unknown table")
      | some (addr, t) =>
        let o := (Exec.i32 off).toNat
        if o + seg.elems.size > t.elems.size then .error (.trap .outOfBoundsTableAccess store)
        else
          let elems := (List.range seg.elems.size).foldl
            (fun es k => es.set! (o + k) seg.elems[k]!) t.elems
          let store := Exec.setTable store addr { t with elems }
          .ok { store with elems := store.elems.set! inst.elemAddrs[i]! { elems := #[] } }
  | .declarative => .ok { store with elems := store.elems.set! inst.elemAddrs[i]! { elems := #[] } }
  | .passive => .ok store

def initElems (store : Store H) (inst : ModuleInst) : List (Nat × Elem) →
    Except (LinkError H) (Store H)
  | [] => .ok store
  | (i, e) :: rest =>
    match initElem store inst i e with
    | .error err => .error err
    | .ok store => initElems store inst rest

/-- Write an active data segment into memory. A trap leaves the store as it is. -/
def initData (store : Store H) (inst : ModuleInst) (i : Nat) (d : Data) :
    Except (LinkError H) (Store H) :=
  match d.mode with
  | .active _ offset =>
    match evalConst store inst offset with
    | .error err => .error err
    | .ok off =>
      match store.memOf inst with
      | none => .error (.internal "no memory")
      | some mem =>
        match mem.writeBytes (Exec.i32 off).toNat d.init with
        | none => .error (.trap .outOfBoundsMemoryAccess store)
        | some mem =>
          let store := store.setMemOf inst mem
          .ok { store with
            datas := store.datas.set! inst.dataAddrs[i]! { bytes := ByteArray.empty } }
  | _ => .ok store

def initDatas (store : Store H) (inst : ModuleInst) : List (Nat × Data) →
    Except (LinkError H) (Store H)
  | [] => .ok store
  | (i, d) :: rest =>
    match initData store inst i d with
    | .error err => .error err
    | .ok store => initDatas store inst rest

def indexed (xs : Array α) : List (Nat × α) := (List.range xs.size).zip xs.toList

/-! ## Instantiation -/

/-- Instantiate a module given its imports, in order, without running its
start function. -/
def instantiateModuleOf (store : Store H) (m : Module) (imports : List ExternVal) :
    Except (LinkError H) (Store H × ModuleInst) :=
  if imports.length != m.imports.size then
    .error (.internal s!"expected {m.imports.size} imports, got {imports.length}")
  else
  match checkImports store m (m.imports.toList.zip imports) with
  | .error e => .error e
  | .ok () =>
  -- Imports first, so that index spaces start with them; then the module's
  -- slot, which its functions refer to.
  let inst := { importAddrs imports with types := m.types }
  let r0 := store.allocModule inst
  let instAddr := r0.2
  let r1 := allocFuncs r0.1 m.types instAddr m.funcs.toList
  let inst := { inst with funcAddrs := inst.funcAddrs ++ r1.2 }
  let r2 := allocTables r1.1 m.tables.toList
  let inst := { inst with tableAddrs := inst.tableAddrs ++ r2.2 }
  let r3 := allocMems r2.1 m.mems.toList
  let inst := { inst with memAddrs := inst.memAddrs ++ r3.2 }
  match allocGlobals r3.1 inst m.globals.toList with
  | .error e => .error e
  | .ok (store, inst) =>
  match allocElems store inst m.elems.toList with
  | .error e => .error e
  | .ok (store, elemAddrs) =>
  let inst := { inst with elemAddrs := elemAddrs }
  let r4 := allocDatas store m.datas.toList
  let inst := { inst with dataAddrs := r4.2 }
  let inst := { inst with exports := exportsOf inst m.exports }
  let store := r4.1.setModule instAddr inst
  match initElems store inst (indexed m.elems) with
  | .error e => .error e
  | .ok store =>
  match initDatas store inst (indexed m.datas) with
  | .error e => .error e
  | .ok store => .ok (store, inst)

/-- Instantiate a validated module given its imports, in order, without
running its start function. -/
def instantiateModule (store : Store H) (vm : ValidModule) (imports : List ExternVal) :
    Except (LinkError H) (Store H × ModuleInst) :=
  instantiateModuleOf store vm.module imports

/-- Run the start function to completion. -/
def runStart (store : Store H) (limits : ExecLimits) (fuel : Nat) (m : Module) (inst : ModuleInst) :
    Except (LinkError H) (Store H) :=
  match m.start with
  | none => .ok store
  | some s =>
    match Exec.invoke store limits fuel inst.funcAddrs[s]! [] with
    | .done _ store => .ok store
    | .trap reason store => .error (.trap reason store)
    | .outOfFuel _ => .error (.internal "start function ran out of fuel")

/-- Instantiate a validated module given its imports, in order, and run its
start function. -/
def instantiate (store : Store H) (limits : ExecLimits) (vm : ValidModule)
    (imports : List ExternVal) (fuel : Nat := 1000000000) : Except (LinkError H) (Store H × ModuleInst) := do
  let (store, inst) ← instantiateModule store vm imports
  let store ← runStart store limits fuel vm.module inst
  return (store, inst)

/-- Named module instances that imports resolve against. -/
abbrev Registry := List (String × ModuleInst)

def resolve (registry : Registry) (m : Module) : Except (LinkError H) (List ExternVal) :=
  m.imports.toList.mapM fun imp =>
    match registry.find? (·.1 == imp.module) with
    | none => .error (.unknownImport imp.module imp.name)
    | some (_, inst) =>
      match inst.export? imp.name with
      | some ext => .ok ext
      | none => .error (.unknownImport imp.module imp.name)

/-- Resolve imports by name, instantiate, and run the start function. -/
def instantiateWith (store : Store H) (limits : ExecLimits) (registry : Registry)
    (vm : ValidModule) : Except (LinkError H) (Store H × ModuleInst) := do
  instantiate store limits vm (← resolve (H := H) registry vm.module)

end Link

end Wasm
