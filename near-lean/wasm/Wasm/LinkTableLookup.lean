import Wasm.LinkFunctionLookup

/-! Table allocation and active-segment lookup facts for the actual linker. -/
namespace Wasm.Link
set_option maxRecDepth 4096

/-- The table allocated from one declared table type. -/
def freshTable (t : Table) : TableInst :=
  {elemType := t.type.elem, elems := Array.replicate t.type.limits.min (.null t.type.elem),
   max := t.type.limits.max}

/-- The allocation fold appends precisely the declared tables and returns their
contiguous store addresses. All other store fields are framed. -/
theorem allocTables_layout (s : Store H) (ts : List Table) :
    allocTables s ts =
      ({s with tables := s.tables ++ (ts.map freshTable).toArray},
        (List.range' s.tables.size ts.length).toArray) := by
  suffices aux : ∀ (s : Store H) (a : Array Nat),
      ts.foldl (fun (s, a) t =>
        let (s, addr) := s.allocTable (freshTable t)
        (s, a.push addr)) (s, a) =
        ({s with tables := s.tables ++ (ts.map freshTable).toArray},
          a ++ (List.range' s.tables.size ts.length).toArray) by
    simpa only [allocTables, freshTable, Array.empty_append] using aux s #[]
  intro s a
  induction ts generalizing s a with
  | nil => simp
  | cons t ts ih =>
    have hp : s.tables.push (freshTable t) = s.tables ++ #[freshTable t] := Array.push_eq_append
    have ha : a.push s.tables.size = a ++ #[s.tables.size] := Array.push_eq_append
    have hc : (freshTable t :: ts.map freshTable).toArray =
        #[freshTable t] ++ (ts.map freshTable).toArray := List.toArray_cons _ _
    have hr : (List.range' s.tables.size (ts.length + 1)).toArray =
        #[s.tables.size] ++ (List.range' (s.tables.size + 1) ts.length).toArray := by
      rw [List.range'_succ, List.toArray_cons]
    simpa only [List.foldl_cons, Store.allocTable, List.map_cons, List.length_cons,
      Array.size_push, hp, ha, hc, hr, Array.append_assoc, Array.size_append, Array.size_singleton] using
      ih {s with tables := s.tables.push (freshTable t)} (a.push s.tables.size)

private theorem copied_size (indices : List Nat) (offset : Nat) (values : Array Ref)
    (target : Array Ref) :
    (indices.foldl (fun es k => es.set! (offset + k) values[k]!) target).size = target.size := by
  induction indices generalizing target with
  | nil => rfl
  | cons i indices ih =>
    simpa only [List.foldl_cons, Array.size_set!] using
      ih (target.set! (offset + i) values[i]!)

private theorem copied_untouched (indices : List Nat) (offset query : Nat) (values : Array Ref)
    (target : Array Ref) (hne : ∀ i ∈ indices, offset + i ≠ query) :
    (indices.foldl (fun es k => es.set! (offset + k) values[k]!) target)[query]? = target[query]? := by
  induction indices generalizing target with
  | nil => rfl
  | cons i indices ih =>
    rw [List.foldl_cons, ih _ (fun j hj => hne j (by simp [hj]))]
    simp only [Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (hne i (by simp))]

private theorem copied_get (indices : List Nat) (offset index : Nat) (values : Array Ref)
    (target : Array Ref) (huniq : indices.Nodup) (hmem : index ∈ indices)
    (hbound : offset + index < target.size) :
    (indices.foldl (fun es k => es.set! (offset + k) values[k]!) target)[offset + index]? =
      some values[index]! := by
  induction indices generalizing target with
  | nil => simp at hmem
  | cons i indices ih =>
    have hu := List.nodup_cons.mp huniq
    rcases List.mem_cons.mp hmem with rfl | hm
    · rw [List.foldl_cons, copied_untouched]
      · simp only [Array.set!_eq_setIfInBounds,
          Array.getElem?_setIfInBounds_self_of_lt hbound]
      · intro j hj heq
        exact hu.1 ((Nat.add_left_cancel heq) ▸ hj)
    · rw [List.foldl_cons]
      apply ih _ hu.2 hm
      simpa only [Array.size_set!] using hbound

/-- The actual active-segment write fold places every source reference at its
offset, without any assumption about the target's previous contents. -/
theorem active_copy_get (target values : Array Ref) (offset index : Nat)
    (hindex : index < values.size) (hbound : offset + values.size ≤ target.size) :
    ((List.range values.size).foldl
      (fun es k => es.set! (offset + k) values[k]!) target)[offset + index]? =
        values[index]? := by
  rw [copied_get _ _ _ _ _ List.nodup_range (List.mem_range.mpr hindex)]
  · simp only [Array.getElem?_eq_getElem hindex, getElem!_pos values index hindex]
  · omega

/-- Successful element-expression evaluation retains the exact length. -/
theorem evalRefs_length (s : Store H) (inst : ModuleInst) (code : List Expr)
    (refs : List Ref) (h : evalRefs s inst code = .ok refs) : refs.length = code.length := by
  induction code generalizing refs with
  | nil => cases h; rfl
  | cons c cs ih =>
    cases hv : evalConst s inst c with
    | error err => simp only [evalRefs, hv] at h; cases h
    | ok v =>
      cases v with
      | i32 n => simp only [evalRefs, hv] at h; cases h
      | i64 n => simp only [evalRefs, hv] at h; cases h
      | f32 n => simp only [evalRefs, hv] at h; cases h
      | f64 n => simp only [evalRefs, hv] at h; cases h
      | ref r =>
        simp only [evalRefs, hv] at h
        cases he : evalRefs s inst cs with
        | error err => simp only [he, Except.map] at h; cases h
        | ok rs =>
          simp only [he, Except.map, Except.ok.injEq] at h
          subst refs
          simp only [List.length_cons, ih rs he]

/-- A local initializer index determines the corresponding evaluated reference;
all earlier and later initializer expressions remain symbolic. -/
theorem evalRefs_ref_func (s : Store H) (inst : ModuleInst) (code : List Expr)
    (refs : List Ref) (h : evalRefs s inst code = .ok refs) (index function address : Nat)
    (hc : code[index]? = some [.ref_func function])
    (hf : inst.funcAddrs[function]? = some address) : refs[index]? = some (.func address) := by
  induction code generalizing refs index with
  | nil => simp at hc
  | cons c cs ih =>
    cases index with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hc
      subst c
      simp only [evalRefs, evalConst, hf] at h
      cases he : evalRefs s inst cs with
      | error err => simp only [he, Except.map] at h; cases h
      | ok rs =>
        simp only [he, Except.map, Except.ok.injEq] at h
        subst refs
        rfl
    | succ n =>
      simp only [List.getElem?_cons_succ] at hc
      cases hv : evalConst s inst c with
      | error err => simp only [evalRefs, hv] at h; cases h
      | ok v =>
        cases v with
        | i32 n => simp only [evalRefs, hv] at h; cases h
        | i64 n => simp only [evalRefs, hv] at h; cases h
        | f32 n => simp only [evalRefs, hv] at h; cases h
        | f64 n => simp only [evalRefs, hv] at h; cases h
        | ref r =>
          simp only [evalRefs, hv] at h
          cases he : evalRefs s inst cs with
          | error err => simp only [he, Except.map] at h; cases h
          | ok rs =>
            simp only [he, Except.map, Except.ok.injEq] at h
            subst refs
            exact ih rs he n hc

/-- Successful active initialization derives the actual table/address and
places a selected allocated segment reference in that table. -/
theorem initElem_reference (s : Store H) (inst : ModuleInst) (n : Nat) (e : Elem)
    (after : Store H) (tableIndex index : Nat) (offset : UInt32) (value : Ref)
    (hmode : e.mode = .active tableIndex [.i32_const offset])
    (hslot : (s.elems[inst.elemAddrs[n]!]!).elems[index]? = some value)
    (h : initElem s inst n e = .ok after) :
    ∃ address table, inst.tableAddrs[tableIndex]? = some address ∧
      after.tables[address]? = some table ∧
      table.elems[offset.toNat + index]? = some value := by
  have hk := (Array.getElem?_eq_some_iff.mp hslot).1
  unfold initElem at h
  rw [hmode] at h
  simp only [evalConst] at h
  cases ha : inst.tableAddrs[tableIndex]? with
  | none => simp [Exec.tableOf, ha] at h
  | some address =>
    cases ht : s.tables[address]? with
    | none => simp [Exec.tableOf, ha, ht] at h
    | some table =>
      simp [Exec.tableOf, ha, ht] at h
      dsimp only [Exec.i32] at h
      by_cases hb : table.elems.size < offset.toNat + s.elems[inst.elemAddrs[n]!]!.elems.size
      · erw [ite_eq_left hb] at h
        cases h
      · erw [ite_eq_right hb] at h
        cases h
        let copied := (List.range s.elems[inst.elemAddrs[n]!]!.elems.size).foldl
            (fun es k => es.set! (offset.toNat + k) s.elems[inst.elemAddrs[n]!]!.elems[k]!) table.elems
        let result : TableInst := {table with elems := copied}
        refine ⟨address, result, rfl, ?_, ?_⟩
        · change (s.tables.set! address _)[address]? = _
          simp only [Array.set!_eq_setIfInBounds,
            Array.getElem?_setIfInBounds_self_of_lt (Array.getElem?_eq_some_iff.mp ht).1]
          rfl
        · change ((List.range _).foldl _ _)[offset.toNat + index]? = some value
          rw [active_copy_get _ _ _ _ hk (by omega)]
          exact hslot

private theorem fold_tables (xs : List α)
    (step : Store H × Array Nat → α → Store H × Array Nat)
    (hf : ∀ s a x, (step (s, a) x).1.tables = s.tables) (s : Store H) (a : Array Nat) :
    (xs.foldl step (s, a)).1.tables = s.tables := by
  induction xs generalizing s a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.foldl_cons, ih, hf]

/-- Function allocation does not touch tables. -/
theorem allocFuncs_tables (s : Store H) (types : Array FuncType) (inst : Nat) (fs : List Func) :
    (allocFuncs s types inst fs).1.tables = s.tables := by
  apply fold_tables
  intros
  rfl

/-- Memory allocation does not touch tables. -/
theorem allocMems_tables (s : Store H) (xs : List Mem) :
    (allocMems s xs).1.tables = s.tables := by
  apply fold_tables
  intros
  rfl

/-- Global allocation retains table contents and the two relevant address spaces. -/
theorem allocGlobals_tables (s : Store H) (inst : ModuleInst) (xs : List Global)
    {after : Store H} {result : ModuleInst} (h : allocGlobals s inst xs = .ok (after, result)) :
    after.tables = s.tables ∧ result.tableAddrs = inst.tableAddrs ∧ result.funcAddrs = inst.funcAddrs := by
  induction xs generalizing s inst with
  | nil =>
    simp only [allocGlobals, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl⟩
  | cons g xs ih =>
    simp only [allocGlobals] at h
    split at h
    · cases h
    · have hr := ih _ _ h
      exact hr

private theorem allocDatas_frames (s : Store H) (xs : List Data) :
    (allocDatas s xs).1.tables = s.tables ∧ (allocDatas s xs).1.elems = s.elems := by
  have aux : ∀ (s : Store H) (a : Array Nat),
      (xs.foldl (fun (s, a) d =>
        let (s, addr) := s.allocData {bytes := d.init}
        (s, a.push addr)) (s, a)).1.tables = s.tables ∧
      (xs.foldl (fun (s, a) d =>
        let (s, addr) := s.allocData {bytes := d.init}
        (s, a.push addr)) (s, a)).1.elems = s.elems := by
    intro s a
    induction xs generalizing s a with
    | nil => exact ⟨rfl, rfl⟩
    | cons d ds ih => exact ih _ _
  exact aux s #[]

/-- Data initialization, including payload writes, leaves the tables unchanged. -/
theorem initData_tables (s : Store H) (inst : ModuleInst) (n : Nat) (d : Data)
    {after : Store H} (h : initData s inst n d = .ok after) : after.tables = s.tables := by
  unfold initData at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst after
          unfold Store.setMemOf
          split <;> rfl
  · cases h; rfl

theorem initDatas_tables (s : Store H) (inst : ModuleInst) (xs : List (Nat × Data))
    {after : Store H} (h : initDatas s inst xs = .ok after) : after.tables = s.tables := by
  induction xs generalizing s with
  | nil => cases h; rfl
  | cons x xs ih =>
    rcases x with ⟨n, d⟩
    simp only [initDatas] at h
    split at h
    · cases h
    · rename_i s' hi
      exact (ih _ h).trans (initData_tables s inst n d hi)

theorem initElems_single (s : Store H) (inst : ModuleInst) (n : Nat) (e : Elem) :
    initElems s inst [(n, e)] = initElem s inst n e := by
  unfold initElems
  cases hi : initElem s inst n e <;> rfl

/-- A single active element segment in a successfully instantiated module
provides an actual table entry. No table descriptor or guest execution premise
is supplied: the selected reference follows from its local initializer. -/
theorem instantiateModule_single_active_ref (s : Store H) (vm : ValidModule)
    (imports : List ExternVal) (after : Store H) (inst : ModuleInst)
    (h : instantiateModule s vm imports = .ok (after, inst))
    (e : Elem) (hsingle : vm.module.elems = #[e])
    (tableIndex index function address : Nat) (offset : UInt32)
    (hmode : e.mode = .active tableIndex [.i32_const offset])
    (hc : e.init[index]? = some [.ref_func function])
    (hf : inst.funcAddrs[function]? = some address) :
    ∃ tableAddress table, inst.tableAddrs[tableIndex]? = some tableAddress ∧
      after.tables[tableAddress]? = some table ∧
      table.elems[offset.toNat + index]? = some (.func address) := by
  unfold instantiateModule at h
  dsimp only at h
  have hindexed : indexed #[e] = [(0, e)] := rfl
  have hlist : vm.module.elems.toList = [e] := by rw [hsingle]
  rw [hlist] at h
  simp only [hsingle, allocElems, hindexed, initElems_single] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i globalsResult globalsStore globalsInst hg
        split at h
        · cases h
        · rename_i refsResult refs hr
          cases hvalues : evalRefs globalsStore globalsInst e.init with
          | error err => simp only [hvalues] at hr; cases hr
          | ok values =>
            simp only [hvalues, Except.ok.injEq, Prod.mk.injEq, Array.append_empty] at hr
            obtain ⟨rfl, rfl⟩ := hr
            split at h
            · cases h
            · rename_i initializedResult initialized hi
              split at h
              · cases h
              · rename_i dataResult final hd
                simp only [Except.ok.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                change globalsInst.funcAddrs[function]? = some address at hf
                have href := evalRefs_ref_func globalsStore globalsInst e.init values hvalues
                  index function address hc hf
                have hframes := allocDatas_frames
                  (globalsStore.allocElem {elems := values.toArray}).1 vm.module.datas.toList
                have result := initElem_reference _ _ 0 e _ tableIndex index offset (.func address) hmode
                  (by
                    change ((allocDatas (globalsStore.allocElem {elems := values.toArray}).1
                      vm.module.datas.toList).1.elems[globalsStore.elems.size]!).elems[index]? = _
                    rw [hframes.2]
                    simp only [Store.allocElem, getElem!_def, Array.getElem?_push_size]
                    simpa only [List.getElem?_toArray] using href) hi
                rcases result with ⟨tableAddress, table, ha, ht, hentry⟩
                refine ⟨tableAddress, table, ha, ?_, hentry⟩
                rw [initDatas_tables _ _ _ hd]
                exact ht

end Wasm.Link
