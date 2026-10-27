import Wasm.Validate

/-! Compositional certificates for the actual module validator. The prelude
checks every static module condition and assembles the actual body context;
individual function checks can be certified separately and recombined. -/
namespace Wasm.Validate.Certificate
open Wasm.Validate

def prelude (features : Features) (m : Module) : Except ValidationError Context := do
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

def checkFunction (features : Features) (m : Module) (ctx : Context) (f : Func) : Except ValidationError Unit := do
  let ft := m.types[f.type]!
  for t in f.locals do
    if let .ref _ := t then if !features.referenceTypes then throw (.unsupported "reference-types")
  body {ctx with locals := (ft.params ++ f.locals).toArray, «return» := some ft.results}
    ft.results f.body

def checkBodies (features : Features) (m : Module) (ctx : Context) : Except ValidationError Unit := do
  for f in m.funcs do checkFunction features m ctx f

theorem module_eq_prelude (features : Features) (m : Module) :
    Validate.module features m = (prelude features m >>= checkBodies features m) := by
  unfold Validate.module prelude checkBodies checkFunction
  simp only [bind_assoc]
  congr 1
  funext unused
  congr 1
  funext imported
  congr 1
  funext funcs
  congr 1
  funext tables
  congr 1
  funext mems
  congr 1
  funext globals
  by_cases hm : mems.size > 1
  · simp only [ite_eq_left hm]
    rfl
  · simp only [ite_eq_right hm]
    by_cases ht : (decide (tables.size > 1) && !features.referenceTypes) = true
    · simp only [ite_eq_left ht]
      rfl
    · simp only [ite_eq_right ht, bind_assoc]
      congr 1
      funext unusedGlobals
      try simp only [bind_assoc]
      congr 1
      funext unusedElems
      try simp only [bind_assoc]
      congr 1
      funext unusedDatas
      cases m.start with
      | none =>
        simp only [bind_assoc, pure_bind]
        congr 1
      | some s =>
        dsimp only
        cases funcs[s]? with
        | none => dsimp only; rfl
        | some ft =>
          dsimp only
          by_cases hp : (!(ft.params.isEmpty && ft.results.isEmpty)) = true
          · simp only [ite_eq_left hp]; rfl
          · simp only [ite_eq_right hp, bind_assoc, pure_bind]
            congr 1

/-- Combine independently checked bodies; static validation is kept separate. -/
theorem checkBodies_ok (features : Features) (m : Module) (ctx : Context)
    (hbody : ∀ f ∈ m.funcs, checkFunction features m ctx f = .ok ()) :
    checkBodies features m ctx = .ok () := by
  unfold checkBodies
  rw [← Array.forIn_toList]
  have hv : ∀ f ∈ m.funcs.toList, checkFunction features m ctx f = .ok () := by
    simpa using hbody
  generalize m.funcs.toList = fs at hv ⊢
  induction fs with
  | nil => rfl
  | cons f fs ih =>
    rw [List.forIn_cons]
    simp only [hv f (by simp), Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ih (fun g hg => hv g (by simp [hg]))

/-- Static checks and local body certificates imply the actual validator result.
No whole-validator success is assumed. -/
theorem module_ok (features : Features) (m : Module) (ctx : Context)
    (hstatic : prelude features m = .ok ctx)
    (hbody : ∀ f ∈ m.funcs, checkFunction features m ctx f = .ok ()) :
    Validate.module features m = .ok () := by
  rw [module_eq_prelude, hstatic]
  exact checkBodies_ok features m ctx hbody

end Wasm.Validate.Certificate
