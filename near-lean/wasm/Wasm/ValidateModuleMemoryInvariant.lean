import Wasm.ValidateMemoryInvariant

/-! Transport of actual module validation across memory-limit replacement. -/
namespace Wasm.Validate

theorem memoryDecls_ok (mems : Array Mem) (initial : Array MemType)
    (hvalid : ∀ mem ∈ mems, memTypeOk mem.type = .ok ()) :
    (forIn mems initial fun mem acc => do
      memTypeOk mem.type
      pure (.yield (acc.push mem.type))) =
        (Except.ok (initial ++ mems.map (·.type)) : Except ValidationError (Array MemType)) := by
  rw [← Array.forIn_toList]
  have hmap : (mems.toList.map (·.type)).toArray = mems.map (·.type) := by
    apply Array.toList_inj.mp
    simp
  rw [← hmap]
  have hv : ∀ mem ∈ mems.toList, memTypeOk mem.type = .ok () := by simpa using hvalid
  generalize mems.toList = xs at hv ⊢
  induction xs generalizing initial with
  | nil => simp; rfl
  | cons mem xs ih =>
    rw [List.forIn_cons]
    simp only [hv mem (by simp), Bind.bind, Except.bind, Pure.pure, Except.pure]
    have hr := ih (initial.push mem.type) (fun m hm => hv m (by simp [hm]))
    have hp : initial.push mem.type = initial ++ #[mem.type] := Array.push_eq_append
    have hc : (mem.type :: xs.map (·.type)).toArray =
        #[mem.type] ++ (xs.map (·.type)).toArray := List.toArray_cons _ _
    simpa only [List.map_cons, hp, hc, Array.append_assoc, Bind.bind, Except.bind, Pure.pure, Except.pure] using hr

theorem declaredRefs_mems (m : Module) (mems : Array Mem) (count : Nat) :
    declaredRefs {m with mems} count = declaredRefs m count := rfl

theorem module_mems_of_checks (features : Features) (m : Module) (mems : Array Mem)
    (hsize : mems.size = m.mems.size)
    (hold : ∀ mem ∈ m.mems, memTypeOk mem.type = .ok ())
    (hnew : ∀ mem ∈ mems, memTypeOk mem.type = .ok ()) :
    module features {m with mems} = module features m := by
  unfold module
  dsimp only
  simp only [memoryDecls_ok m.mems _ hold, memoryDecls_ok mems _ hnew]
  congr 1
  funext unused
  congr 1
  funext imported
  congr 1
  funext funcs
  congr 1
  funext tables
  dsimp only [Bind.bind, Except.bind]
  congr 1
  funext globals
  let old := imported.snd.snd.fst ++ m.mems.map (·.type)
  let new := imported.snd.snd.fst ++ mems.map (·.type)
  let ctx : Context :=
    { features, types := m.types, funcs, tables, mems := old, globals,
      elems := m.elems.map (·.type), datas := m.datas.size, locals := #[],
      refs := declaredRefs m funcs.size, «return» := none }
  have hs : new.size = old.size := by simp [new, old, hsize]
  have hc : ∀ imported visible type code,
      constExpr imported visible {ctx with mems := new} type code =
        constExpr imported visible ctx type code := by
    intro imported visible type code
    exact constExpr_mems imported visible ctx new hs type code
  have hb : ∀ locals results code,
      body {ctx with mems := new, locals, «return» := some results} results code =
        body {ctx with locals, «return» := some results} results code := by
    intro locals results code
    exact body_mems {ctx with locals, «return» := some results} new hs results code
  dsimp only [ctx] at hc hb
  simp only [declaredRefs_mems m mems, hs,
    show imported.snd.snd.fst ++ Array.map (fun x => x.type) mems = new from rfl,
    show imported.snd.snd.fst ++ Array.map (fun x => x.type) m.mems = old from rfl,
    hc, hb]

/-- Transport a successful original check without revalidating any body. The
small original memory-type checks are explicit, as are replacement checks. -/
theorem module_mems_success (features : Features) (m : Module) (mems : Array Mem)
    (hsize : mems.size = m.mems.size)
    (hold : ∀ mem ∈ m.mems, memTypeOk mem.type = .ok ())
    (hnew : ∀ mem ∈ mems, memTypeOk mem.type = .ok ())
    (hvalid : module features m = .ok ()) :
    module features {m with mems} = .ok () := by
  rw [module_mems_of_checks features m mems hsize hold hnew, hvalid]

/-- The memory replacement used in runtime preparation leaves the validator
result unchanged when both the original and configured page bounds are valid.
This does not assert that the original module itself passes validation. -/
theorem module_replace_limits (features : Features) (m : Module) (min max : Nat)
    (hold : ∀ mem ∈ m.mems, memTypeOk mem.type = .ok ())
    (horder : min ≤ max) (hmax : max ≤ 65536) :
    module features {m with mems := m.mems.map (fun _ =>
      {type := {limits := {min, max := some max}}})} = module features m := by
  apply module_mems_of_checks
  · simp
  · exact hold
  · intro mem hmem
    obtain ⟨original, _, rfl⟩ := Array.mem_map.mp hmem
    exact memTypeOk_of_bounds min max horder hmax

end Wasm.Validate
