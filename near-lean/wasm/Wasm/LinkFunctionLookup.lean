import Wasm.LinkFuncs

/-! Exact defined-function addresses after successful instantiation. Proofs
follow allocation and frame segment initialization, without evaluating payloads. -/
namespace Wasm.Link
set_option maxRecDepth 4096

private def CodeEq (before after : Store H) : Prop :=
  after.funcs = before.funcs ∧ after.modules = before.modules

private theorem CodeEq.trans {a b c : Store H} (h₁ : CodeEq a b) (h₂ : CodeEq b c) :
    CodeEq a c := ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2⟩

private theorem fold_code (xs : List α) (step : Store H × Array Nat → α → Store H × Array Nat)
    (hstep : ∀ s a x, CodeEq s (step (s, a) x).1) (s : Store H) (a : Array Nat) :
    CodeEq s (xs.foldl step (s, a)).1 := by
  induction xs generalizing s a with
  | nil => exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact (hstep s a x).trans (ih (step (s, a) x).1 (step (s, a) x).2)

/-- Exact arrays produced by the actual function-allocation fold. -/
theorem allocFuncs_arrays (s : Store H) (types : Array FuncType) (inst : Nat) (fs : List Func) :
    (allocFuncs s types inst fs).1.funcs =
      s.funcs ++ (fs.map (fun f => FuncInst.wasm (H := H) types[f.type]! inst f)).toArray ∧
    (allocFuncs s types inst fs).2 = (List.range' s.funcs.size fs.length).toArray ∧
    (allocFuncs s types inst fs).1.modules = s.modules := by
  suffices aux : ∀ (s : Store H) (a : Array Nat),
      let r := fs.foldl (fun (s, a) f =>
        let (s, addr) := s.allocFunc (.wasm types[f.type]! inst f)
        (s, a.push addr)) (s, a)
      r.1.funcs = s.funcs ++ (fs.map (fun f => FuncInst.wasm (H := H) types[f.type]! inst f)).toArray ∧
      r.2 = a ++ (List.range' s.funcs.size fs.length).toArray ∧ r.1.modules = s.modules by
    simpa only [allocFuncs, Array.empty_append] using aux s #[]
  intro s a
  induction fs generalizing s a with
  | nil => simp
  | cons f fs ih =>
    have hf : s.funcs.push (.wasm types[f.type]! inst f) = s.funcs ++ #[.wasm types[f.type]! inst f] := Array.push_eq_append
    have ha : a.push s.funcs.size = a ++ #[s.funcs.size] := Array.push_eq_append
    have hc : (FuncInst.wasm (H := H) types[f.type]! inst f :: fs.map (fun f => FuncInst.wasm (H := H) types[f.type]! inst f)).toArray =
        #[FuncInst.wasm (H := H) types[f.type]! inst f] ++ (fs.map (fun f => FuncInst.wasm (H := H) types[f.type]! inst f)).toArray := List.toArray_cons _ _
    have hr : (List.range' s.funcs.size (fs.length + 1)).toArray =
        #[s.funcs.size] ++ (List.range' (s.funcs.size + 1) fs.length).toArray := by
      rw [List.range'_succ, List.toArray_cons]
    simpa only [List.foldl_cons, Store.allocFunc, List.map_cons, List.length_cons,
      Array.size_push, Array.size_append, Array.size_singleton, hf, ha, hc, hr,
      Array.append_assoc] using ih {s with funcs := s.funcs.push (.wasm types[f.type]! inst f)}
        (a.push s.funcs.size)

private theorem allocTables_code (s : Store H) (xs : List Table) :
    CodeEq s (allocTables s xs).1 := by
  apply fold_code
  intro s a x
  exact ⟨rfl, rfl⟩

private theorem allocMems_code (s : Store H) (xs : List Mem) :
    CodeEq s (allocMems s xs).1 := by
  apply fold_code
  intro s a x
  exact ⟨rfl, rfl⟩

private theorem allocDatas_code (s : Store H) (xs : List Data) :
    CodeEq s (allocDatas s xs).1 := by
  apply fold_code
  intro s a x
  exact ⟨rfl, rfl⟩

private theorem allocGlobals_code (s : Store H) (i : ModuleInst) (xs : List Global)
    {s' : Store H} {i' : ModuleInst} (h : allocGlobals s i xs = .ok (s', i')) :
    CodeEq s s' ∧ i'.funcAddrs = i.funcAddrs := by
  induction xs generalizing s i with
  | nil => simp only [allocGlobals, Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, rfl⟩ := h; exact ⟨⟨rfl, rfl⟩, rfl⟩
  | cons g xs ih =>
    simp only [allocGlobals] at h
    split at h
    · cases h
    · have hr := ih _ _ h
      exact ⟨⟨hr.1.1, hr.1.2⟩, hr.2⟩

private theorem allocElems_code (s : Store H) (i : ModuleInst) (xs : List Elem)
    {s' : Store H} {a : Array Nat} (h : allocElems s i xs = .ok (s', a)) : CodeEq s s' := by
  induction xs generalizing s a with
  | nil => simp only [allocElems, Except.ok.injEq, Prod.mk.injEq] at h
           exact h.1 ▸ ⟨rfl, rfl⟩
  | cons e xs ih =>
    simp only [allocElems] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i x₁ refs he x₂ s₂ a₂ hr
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have hc : CodeEq s (s.allocElem {elems := refs.toArray}).1 := ⟨rfl, rfl⟩
        exact hc.trans (ih _ hr)

private theorem initElem_code (s : Store H) (i : ModuleInst) (n : Nat) (e : Elem)
    {s' : Store H} (h : initElem s i n e = .ok s') : CodeEq s s' := by
  unfold initElem at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · dsimp only at h
        split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s'
          exact ⟨rfl, rfl⟩
  · simp only [Except.ok.injEq] at h; subst s'; exact ⟨rfl, rfl⟩
  · simp only [Except.ok.injEq] at h; subst s'; exact ⟨rfl, rfl⟩

private theorem initElems_code (s : Store H) (i : ModuleInst) (xs : List (Nat × Elem))
    {s' : Store H} (h : initElems s i xs = .ok s') : CodeEq s s' := by
  induction xs generalizing s with
  | nil => simp only [initElems, Except.ok.injEq] at h; subst s'; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    rcases x with ⟨n, e⟩
    simp only [initElems] at h
    split at h
    · cases h
    · rename_i he
      exact (initElem_code _ _ _ _ he).trans (ih _ h)

private theorem initData_code (s : Store H) (i : ModuleInst) (n : Nat) (d : Data)
    {s' : Store H} (h : initData s i n d = .ok s') : CodeEq s s' := by
  unfold initData at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst s'
          unfold CodeEq Store.setMemOf
          split <;> exact ⟨rfl, rfl⟩
  · simp only [Except.ok.injEq] at h; subst s'; exact ⟨rfl, rfl⟩

private theorem initDatas_code (s : Store H) (i : ModuleInst) (xs : List (Nat × Data))
    {s' : Store H} (h : initDatas s i xs = .ok s') : CodeEq s s' := by
  induction xs generalizing s with
  | nil => simp only [initDatas, Except.ok.injEq] at h; subst s'; exact ⟨rfl, rfl⟩
  | cons x xs ih =>
    rcases x with ⟨n, d⟩
    simp only [initDatas] at h
    split at h
    · cases h
    · rename_i he
      exact (initData_code _ _ _ _ he).trans (ih _ h)

/-- Successful instantiation installs the exact defined function array and
address vector, and returns the module instance stored at its allocated slot.
The segment initialization routines are only framed, never evaluated. -/
theorem instantiateModule_arrays (store : Store H) (vm : ValidModule) (imports : List ExternVal)
    {store' : Store H} {inst : ModuleInst}
    (h : instantiateModule store vm imports = .ok (store', inst)) :
    store'.funcs = store.funcs ++ (vm.module.funcs.toList.map
      (fun f => FuncInst.wasm vm.module.types[f.type]! store.modules.size f)).toArray ∧
    inst.funcAddrs = (importAddrs imports).funcAddrs ++
      (List.range' store.funcs.size vm.module.funcs.size).toArray ∧
    store'.modules[store.modules.size]? = some inst := by
  unfold instantiateModule at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i x₁ s₁ i₁ hg
        split at h
        · cases h
        · rename_i x₂ s₂ a₂ he
          split at h
          · cases h
          · rename_i x₃ s₃ hie
            split at h
            · cases h
            · rename_i x₄ s₄ hid
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hg' := allocGlobals_code _ _ _ hg
              have he' := allocElems_code _ _ _ he
              have hie' := initElems_code _ _ _ hie
              have hid' := initDatas_code _ _ _ hid
              have ht := allocTables_code
                (allocFuncs (store.allocModule {importAddrs imports with types := vm.module.types}).1
                  vm.module.types store.modules.size vm.module.funcs.toList).1 vm.module.tables.toList
              have hm := allocMems_code
                (allocTables
                  (allocFuncs (store.allocModule {importAddrs imports with types := vm.module.types}).1
                    vm.module.types store.modules.size vm.module.funcs.toList).1 vm.module.tables.toList).1
                vm.module.mems.toList
              have hf := allocFuncs_arrays
                (store.allocModule {importAddrs imports with types := vm.module.types}).1
                vm.module.types store.modules.size vm.module.funcs.toList
              have hd := allocDatas_code s₂ vm.module.datas.toList
              simp only [Store.allocModule] at hg' ht hm hf ⊢
              have hfuncs : s₄.funcs = store.funcs ++ (vm.module.funcs.toList.map
                  (fun f => FuncInst.wasm vm.module.types[f.type]! store.modules.size f)).toArray := by
                rw [hid'.1, hie'.1]
                change (allocDatas s₂ vm.module.datas.toList).1.funcs = _
                rw [hd.1, he'.1, hg'.1.1, hm.1, ht.1, hf.1]
              have hmodules : s₂.modules = store.modules.push
                  {importAddrs imports with types := vm.module.types} := by
                rw [he'.2, hg'.1.2, hm.2, ht.2, hf.2.2]
              refine ⟨hfuncs, ?_, ?_⟩
              · change i₁.funcAddrs = _
                rw [hg'.2, hf.2.1]
                rfl
              · rw [hid'.2, hie'.2]
                change ((allocDatas s₂ vm.module.datas.toList).1.modules.set! store.modules.size _)[store.modules.size]? = _
                rw [hd.2, hmodules]
                simp

/-- A code-table lookup becomes actual installed-function and module lookups.
Only successful loading and the two small source-table facts are premises. -/
theorem instantiateModule_defined (store : Store H) (vm : ValidModule) (imports : List ExternVal)
    {store' : Store H} {inst : ModuleInst}
    (h : instantiateModule store vm imports = .ok (store', inst))
    (n : Nat) (f : Func) (type : FuncType)
    (hfunc : vm.module.funcs[n]? = some f)
    (htype : vm.module.types[f.type]? = some type) :
    inst.funcAddrs[(importAddrs imports).funcAddrs.size + n]? = some (store.funcs.size + n) ∧
    store'.funcs[store.funcs.size + n]? = some (.wasm type store.modules.size f) ∧
    store'.modules[store.modules.size]? = some inst := by
  obtain ⟨hf, ha, hm⟩ := instantiateModule_arrays store vm imports h
  have hn : n < vm.module.funcs.size := (Array.getElem?_eq_some_iff.mp hfunc).1
  refine ⟨?_, ?_, hm⟩
  · rw [ha, Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_toArray, List.getElem?_range' hn]
    simp
  · rw [hf, Array.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_toArray, List.getElem?_map]
    simp only [Array.getElem?_toList, hfunc, Option.map_some, getElem!_def, htype]

end Wasm.Link
