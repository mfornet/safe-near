import Binary.Module
import Wasm.ValidateCertificate

/-! Static metadata for chunked validation of the deployed module. Function
bodies and data payloads are not reduced by these certificates.
The section certificates are separate: this file does not yet assert success
of the assembled static prelude. A concrete-context assembly attempt exceeded
50 GB during kernel conversion; the remaining assembly should use generic
stages rather than duplicate this concrete context through every clause. -/
namespace WNear.Binary.ValidationPrelude
open Wasm
set_option maxRecDepth 4096
set_option maxHeartbeats 200000

private theorem entry_types (ts : List Nat) (cs : List (Nat × List ValType × Expr))
    (hlen : ts.length = cs.length) :
    (List.zipWith Wasm.Binary.Parser.entryFunc ts cs).map (·.type) = ts := by
  induction ts generalizing cs with
  | nil => cases cs <;> simp_all
  | cons t ts ih =>
    cases cs with
    | nil => simp at hlen
    | cons c cs =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
      simpa only [List.zipWith_cons_cons, List.map_cons, Wasm.Binary.Parser.entryFunc]
        using congrArg (List.cons t) (ih cs hlen)

set_option maxHeartbeats 200000 in
private theorem type_count : funcTypesList.length = 907 := by decide +kernel

set_option maxHeartbeats 200000 in
private theorem code_count : codes.length = 907 := by decide +kernel

/-- Forgetting code and locals in the constructor recovers exactly the decoded
function-section indices. This uses the existing assembly proof, not another
reduction of all function bodies. -/
theorem function_type_list : funcs.toList.map (·.type) = funcTypesList := by
  rw [← zip_codes]
  exact entry_types funcTypesList codes (type_count.trans code_count.symm)

/-- Actual function metadata, without inspecting any body. -/
theorem function_type_array : funcs.map (·.type) = funcTypesList.toArray := by
  apply Array.toList_inj.mp
  rw [Array.toList_map, function_type_list, List.toList_toArray]

private theorem forIn_function_types (initial : Array FuncType)
    (step : Nat → Array FuncType → Except ValidationError (ForInStep (Array FuncType))) :
    forIn funcs initial (fun f acc => step f.type acc) = forIn funcTypesList.toArray initial step := by
  rw [← Array.forIn_map, function_type_array]

/-- A metadata-only module used for static checking. Defined-function bodies
are absent, while the real data payload stays opaque. -/
noncomputable def typeOnlyModule : Module :=
  {wNearModule with funcs := funcTypesList.toArray.map (fun t => {type := t, locals := [], body := []})}

private theorem bind_cont {α β : Type} (x : Except ValidationError α)
    (f g : α → Except ValidationError β) (h : ∀ a, f a = g a) :
    (x >>= f) = (x >>= g) := congrArg (fun k => x >>= k) (funext h)

/-- The actual prelude reads precisely the same metadata in this smaller
module. The equality is structural, not a reduction of all deployed bodies. -/
theorem prelude_typeOnly (features : Features) :
    Validate.Certificate.prelude features wNearModule =
      Validate.Certificate.prelude features typeOnlyModule := by
  unfold Validate.Certificate.prelude
  dsimp only [typeOnlyModule, wNearModule]
  apply bind_cont
  intro unused
  apply bind_cont
  intro imported
  conv =>
    lhs
    arg 1
    erw [forIn_function_types imported.fst (fun i acc =>
      match types[i]? with
      | some ft => pure (.yield (acc.push ft))
      | none => do
        throw (ValidationError.invalid "unknown type")
        pure (.yield acc))]
  simp only [Array.forIn_map]
  rfl

/-- The imported signature vector is pure decoded metadata. -/
noncomputable def importedTypes : Array FuncType := imports.map fun imp =>
  match imp.desc with
  | .func i => types[i]!
  | _ => default

/-- The context used by all local body certificates; it is defined from the
section metadata, never by executing the static validator. -/
noncomputable def context : Validate.Context :=
  {features := Features.nearcore true, types,
   funcs := importedTypes ++ funcTypesList.toArray.map (fun i => types[i]!),
   tables := tables.map (·.type), mems := mems.map (·.type),
   globals := globals.map (·.type), elems := elems.map (·.type), datas := 1,
   refs := Validate.declaredRefs wNearModule 955, locals := #[], «return» := none}

/-- The actual type-section feature checks. -/
theorem type_checks :
    (forIn types PUnit.unit (fun ft _ => do
      if !(Features.nearcore true).multiValue && ft.results.length > 1 then
        throw (ValidationError.unsupported "multi-value")
      for t in ft.params ++ ft.results do
        if let .ref _ := t then
          if !(Features.nearcore true).referenceTypes then
            throw (ValidationError.unsupported "reference-types")
      pure (.yield PUnit.unit))) =
      (Except.ok PUnit.unit : Except ValidationError PUnit) := by rfl

/-- The actual import loop contributes only its forty-eight function types. -/
theorem import_checks :
    (forIn imports (#[], #[], #[], #[]) (fun imp acc => do
      match imp.desc with
      | .func ty =>
        match types[ty]? with
        | some ft => pure (.yield (acc.1.push ft, acc.2.1, acc.2.2.1, acc.2.2.2))
        | none => throw (ValidationError.invalid "unknown type")
      | .table tt =>
        Validate.tableTypeOk (Features.nearcore true) tt
        pure (.yield (acc.1, acc.2.1.push tt, acc.2.2.1, acc.2.2.2))
      | .mem mt =>
        Validate.memTypeOk mt
        pure (.yield (acc.1, acc.2.1, acc.2.2.1.push mt, acc.2.2.2))
      | .global gt =>
        Validate.globalTypeOk (Features.nearcore true) gt
        if gt.mutable && !(Features.nearcore true).mutableGlobals then
          throw (ValidationError.unsupported "mutable-globals")
        pure (.yield (acc.1, acc.2.1, acc.2.2.1, acc.2.2.2.push gt)))) =
      (Except.ok (importedTypes, #[], #[], #[]) : Except ValidationError
        (Array FuncType × Array TableType × Array MemType × Array GlobalType)) := by kernel_rfl

private theorem collect_types (ts : Array FuncType) (xs : List Nat)
    (initial : Array FuncType) (hvalid : ∀ i ∈ xs, i < ts.size) :
    (forIn xs initial (fun i acc =>
      match ts[i]? with
      | some ft => (Except.ok (ForInStep.yield (acc.push ft)) : Except ValidationError _)
      | none => .error (.invalid "unknown type"))) =
        .ok (initial ++ (xs.map (fun i => ts[i]!)).toArray) := by
  induction xs generalizing initial with
  | nil => simp; rfl
  | cons i xs ih =>
    have hi := hvalid i (by simp)
    rw [List.forIn_cons]
    simp only [Array.getElem?_eq_getElem hi, Bind.bind, Except.bind]
    rw [ih (initial.push ts[i]) (fun j hj => hvalid j (by simp [hj]))]
    have hp : initial.push ts[i] = initial ++ #[ts[i]] := Array.push_eq_append
    have hc : (ts[i]! :: xs.map (fun j => ts[j]!)).toArray =
        #[ts[i]!] ++ (xs.map (fun j => ts[j]!)).toArray := List.toArray_cons _ _
    simp only [getElem!_pos ts i hi] at hc
    simp only [List.map_cons, getElem!_pos ts i hi, hc, hp, Array.append_assoc]

private theorem all_function_types_valid :
    (funcTypesList.all (fun i => decide (i < types.size))) = true := by decide +kernel

/-- Assemble the defined-function signature vector from indices. Its proof is
list induction plus a small index-bound certificate, without checking bodies. -/
theorem defined_checks (initial : Array FuncType) :
    (forIn funcTypesList.toArray initial (fun i acc =>
      match types[i]? with
      | some ft => (Except.ok (ForInStep.yield (acc.push ft)) : Except ValidationError _)
      | none => .error (.invalid "unknown type"))) =
        .ok (initial ++ funcTypesList.toArray.map (fun i => types[i]!)) := by
  rw [← Array.forIn_toList, List.toList_toArray]
  have hv : ∀ i ∈ funcTypesList, i < types.size := by
    simpa only [List.all_eq_true, decide_eq_true_eq] using all_function_types_valid
  simpa only [List.map_toArray] using collect_types types funcTypesList initial hv

theorem table_checks :
    (forIn tables #[] (fun t acc => do
      Validate.tableTypeOk (Features.nearcore true) t.type
      pure (.yield (acc.push t.type)))) =
      (Except.ok (tables.map (·.type)) : Except ValidationError (Array TableType)) := by kernel_rfl

theorem memory_checks :
    (forIn mems #[] (fun t acc => do
      Validate.memTypeOk t.type
      pure (.yield (acc.push t.type)))) =
      (Except.ok (mems.map (·.type)) : Except ValidationError (Array MemType)) := by kernel_rfl

theorem global_checks :
    (forIn globals #[] (fun t acc => do
      Validate.globalTypeOk (Features.nearcore true) t.type
      pure (.yield (acc.push t.type)))) =
      (Except.ok (globals.map (·.type)) : Except ValidationError (Array GlobalType)) := by kernel_rfl

private theorem const_ref (ctx : Validate.Context) (i imported visible : Nat)
    (hf : ctx.features.referenceTypes = true) (hb : i < ctx.funcs.size)
    (hr : ctx.refs[i]?.getD false = true) :
    Validate.constExpr imported visible ctx .funcref [.ref_func i] = .ok () := by
  have hg := Array.getElem?_eq_getElem hb
  simp only [Validate.constExpr, Validate.seq, Validate.instr,
    Validate.checkRefFeature, Validate.funcType, Validate.requireFeature,
    hf, hg, Validate.require, hr]
  rfl

private noncomputable def validInit (code : Expr) : Bool :=
  match code with
  | [.ref_func i] => decide (i < 955) &&
      ((Validate.declaredRefs wNearModule 955)[i]?.getD false)
  | _ => false

private theorem element_initializers_valid :
    elems.all (fun e => e.init.all validInit) = true := by decide +kernel

/-- The explicit validation context has exactly the deployed function space. -/
theorem context_funcs_size : context.funcs.size = 955 := by
  have hi : imports.size = 48 := by kernel_rfl
  simp only [context, importedTypes, Array.size_append, Array.size_map,
    List.size_toArray, type_count, hi]

private theorem elem_type (e : Elem) (he : e ∈ elems) : e.type = .funcref := by
  simp only [elems, Array.mem_singleton] at he
  subst e
  rfl

theorem initializer_ok (e : Elem) (he : e ∈ elems)
    (code : Expr) (hc : code ∈ e.init) (imported visible : Nat) :
    Validate.constExpr imported visible context (.ref e.type) code = .ok () := by
  rw [elem_type e he]
  have hv := List.all_eq_true.mp (Array.all_eq_true_iff_forall_mem.mp element_initializers_valid e he) code hc
  unfold validInit at hv
  split at hv
  next _ i =>
    have hh : i < 955 ∧ (Validate.declaredRefs wNearModule 955)[i]?.getD false = true := by
      simpa only [Bool.and_eq_true, decide_eq_true_eq] using hv
    apply const_ref context i imported visible rfl
    · simpa only [context_funcs_size] using hh.1
    · exact hh.2
  next => contradiction

private theorem list_checks {α : Type} (xs : List α)
    (check : α → Except ValidationError Unit)
    (hv : ∀ x ∈ xs, check x = .ok ()) :
    (forIn xs PUnit.unit (fun x _ => do check x; pure (.yield PUnit.unit))) =
      .ok PUnit.unit := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.forIn_cons]
    simp only [hv x (by simp), Bind.bind, Except.bind, Pure.pure, Except.pure]
    exact ih (fun y hy => hv y (by simp [hy]))

theorem initializer_checks (e : Elem) (he : e ∈ elems) (imported visible : Nat) :
    (forIn e.init PUnit.unit (fun code _ => do
      Validate.constExpr imported visible context (.ref e.type) code
      pure (.yield PUnit.unit))) = .ok PUnit.unit :=
  list_checks _ _ (fun code hc => initializer_ok e he code hc imported visible)

private theorem elem_mode (e : Elem) (he : e ∈ elems) :
    e.mode = .active 0 [.i32_const 1] := by
  simp only [elems, Array.mem_singleton] at he
  subst e
  rfl

noncomputable def checkElement (e : Elem) : Except ValidationError Unit := do
  if e.type != .funcref && !context.features.referenceTypes then
    throw (.unsupported "reference-types")
  for init in e.init do Validate.constExpr 0 context.globals.size context (.ref e.type) init
  match e.mode with
  | .active table offset =>
    match context.tables[table]? with
    | some tt =>
      if tt.elem != e.type then throw (.invalid "type mismatch: element segment type")
    | none => throw (.invalid "unknown table")
    Validate.constExpr 0 context.globals.size context .i32 offset
  | .passive | .declarative =>
    if !context.features.bulkMemory then throw (.unsupported "bulk-memory")

theorem checkElement_ok (e : Elem) (he : e ∈ elems) :
    checkElement e = .ok () := by
  unfold checkElement
  rw [elem_type e he]
  have hi := initializer_checks e he 0 context.globals.size
  rw [elem_type e he] at hi
  simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, ite_false]
  erw [hi]
  rw [elem_mode e he]
  have ht : context.tables[0]? = some
      {elem := .funcref, limits := {min := 215, max := some 215}} := by kernel_rfl
  dsimp only [Bind.bind, Except.bind]
  rw [ht]
  have hc : Validate.constExpr 0 context.globals.size context .i32 [.i32_const 1] = .ok () := by
    rfl
  simpa only [bne_self_eq_false, Bool.false_eq_true, ite_false] using hc

theorem element_checks :
    (forIn elems PUnit.unit (fun e _ => do
      checkElement e
      pure (.yield PUnit.unit))) = .ok PUnit.unit := by
  rw [← Array.forIn_toList]
  apply list_checks
  intro e he
  exact checkElement_ok e (by simpa using he)

theorem global_initializers :
    (forIn' [:globals.size] PUnit.unit (fun i h _ => do
      Validate.constExpr 0 i context globals[i].type.type globals[i].init
      pure (.yield PUnit.unit))) =
      (Except.ok PUnit.unit : Except ValidationError PUnit) := by kernel_rfl

noncomputable def checkData (d : Data) : Except ValidationError Unit := do
  match d.mode with
  | .active mem offset =>
    if mem ≥ context.mems.size then throw (.invalid "unknown memory")
    Validate.constExpr 0 context.globals.size context .i32 offset
  | .passive => if !context.features.bulkMemory then throw (.unsupported "bulk-memory")
  | .declarative => throw (.invalid "declarative data segment")

theorem data_checks :
    (forIn datas PUnit.unit (fun d _ => do
      checkData d
      pure (.yield PUnit.unit))) = .ok PUnit.unit := by
  kernel_rfl

theorem export_checks :
    (forIn exports #[] (fun e names => do
      if names.contains e.name then throw (ValidationError.invalid "duplicate export name")
      let ok := match e.desc with
        | .func i => i < context.funcs.size
        | .table i => i < context.tables.size
        | .mem i => i < context.mems.size
        | .global i => i < context.globals.size
      if !ok then throw (ValidationError.invalid s!"unknown export index: {e.name}")
      pure (.yield (names.push e.name)))) =
        (Except.ok (exports.map (·.name)) : Except ValidationError (Array String)) := by
  rw [context_funcs_size]
  kernel_rfl

end WNear.Binary.ValidationPrelude
