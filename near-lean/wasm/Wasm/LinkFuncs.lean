import Wasm.LinkInvariant

/-!
# Instantiation adds only the module's functions

Every function instance in an instantiated store was already in the store or
is one of the module's own functions. Together with `HostEnv.allocate`, which
adds only host functions, this bounds the code a call can ever execute by the
module's function bodies (`Wasm.Fuel`).
-/

namespace Wasm.Link

/-- Every function of `after` is one of `before`'s or a Wasm function with code from `fs`. -/
def FuncsFrom (fs : List Func) (before after : Store H) : Prop :=
  ∀ fn ∈ after.funcs, fn ∈ before.funcs ∨ ∃ t i f, fn = FuncInst.wasm t i f ∧ f ∈ fs

variable {fs : List Func}

theorem FuncsFrom.refl (s : Store H) : FuncsFrom fs s s := fun _ h => Or.inl h

theorem FuncsFrom.trans {a b c : Store H} (h₁ : FuncsFrom fs a b) (h₂ : FuncsFrom fs b c) :
    FuncsFrom fs a c := by
  intro fn h
  rcases h₂ fn h with h | h
  · exact h₁ fn h
  · exact Or.inr h

theorem FuncsFrom.of_eq {a b : Store H} (hf : b.funcs = a.funcs) : FuncsFrom fs a b :=
  fun _ h => Or.inl (hf ▸ h)

theorem allocModule_from (s : Store H) (m : ModuleInst) : FuncsFrom fs s (s.allocModule m).1 :=
  .of_eq rfl

theorem setModule_from (s : Store H) (i : Nat) (m : ModuleInst) : FuncsFrom fs s (s.setModule i m) :=
  .of_eq rfl

theorem allocFunc_wasm_from (s : Store H) (t : FuncType) (i : Nat) {f : Func} (hf : f ∈ fs) :
    FuncsFrom fs s (s.allocFunc (.wasm t i f)).1 := by
  intro fn h
  simp only [Store.allocFunc, Array.mem_push] at h
  rcases h with h | rfl
  · exact Or.inl h
  · exact Or.inr ⟨t, i, f, rfl, hf⟩

theorem allocFuncs_from (store : Store H) (types : Array FuncType) (instAddr : Nat)
    (funcs : List Func) (hfuncs : ∀ f ∈ funcs, f ∈ fs) :
    FuncsFrom fs store (allocFuncs store types instAddr funcs).1 := by
  unfold allocFuncs
  suffices key : ∀ (init : Store H × Array Nat),
      FuncsFrom fs init.1 (funcs.foldl (fun (store, addrs) f =>
        let (store, addr) := store.allocFunc (.wasm types[f.type]! instAddr f)
        (store, addrs.push addr)) init).1 by
    exact key (store, #[])
  intro init
  induction funcs generalizing init with
  | nil => exact .refl _
  | cons f rest ih =>
    obtain ⟨st, addrs⟩ := init
    simp only [List.foldl_cons]
    exact (allocFunc_wasm_from st _ _ (hfuncs f (by simp))).trans
      (ih (fun g hg => hfuncs g (by simp [hg])) _)

theorem allocTables_from (store : Store H) (tables : List Table) :
    FuncsFrom fs store (allocTables store tables).1 := by
  unfold allocTables
  suffices key : ∀ (init : Store H × Array Nat),
      FuncsFrom fs init.1 (tables.foldl (fun (store, addrs) t =>
        let tt := t.type
        let table : TableInst :=
          { elemType := tt.elem, elems := Array.replicate tt.limits.min (.null tt.elem),
            max := tt.limits.max }
        let (store, addr) := store.allocTable table
        (store, addrs.push addr)) init).1 by
    exact key (store, #[])
  intro init
  induction tables generalizing init with
  | nil => exact .refl _
  | cons t rest ih =>
    obtain ⟨st, addrs⟩ := init
    simp only [List.foldl_cons]
    exact (FuncsFrom.of_eq rfl).trans (ih _)

theorem allocMems_from (store : Store H) (mems : List Mem) :
    FuncsFrom fs store (allocMems store mems).1 := by
  unfold allocMems
  suffices key : ∀ (init : Store H × Array Nat),
      FuncsFrom fs init.1 (mems.foldl (fun (store, addrs) mem =>
        let (store, addr) := store.allocMem (Memory.new mem.type.limits.min mem.type.limits.max)
        (store, addrs.push addr)) init).1 by
    exact key (store, #[])
  intro init
  induction mems generalizing init with
  | nil => exact .refl _
  | cons m rest ih =>
    obtain ⟨st, addrs⟩ := init
    simp only [List.foldl_cons]
    exact (FuncsFrom.of_eq rfl).trans (ih _)

theorem allocDatas_from (store : Store H) (datas : List Data) :
    FuncsFrom fs store (allocDatas store datas).1 := by
  unfold allocDatas
  suffices key : ∀ (init : Store H × Array Nat),
      FuncsFrom fs init.1 (datas.foldl (fun (store, addrs) d =>
        let (store, addr) := store.allocData { bytes := d.init }
        (store, addrs.push addr)) init).1 by
    exact key (store, #[])
  intro init
  induction datas generalizing init with
  | nil => exact .refl _
  | cons d rest ih =>
    obtain ⟨st, addrs⟩ := init
    simp only [List.foldl_cons]
    exact (FuncsFrom.of_eq rfl).trans (ih _)

theorem allocGlobals_from (store : Store H) (inst : ModuleInst) (globals : List Global)
    {store' : Store H} {inst' : ModuleInst}
    (h : allocGlobals store inst globals = .ok (store', inst')) : FuncsFrom fs store store' := by
  induction globals generalizing store inst with
  | nil => simp only [allocGlobals, Except.ok.injEq, Prod.mk.injEq] at h; exact h.1 ▸ .refl _
  | cons g rest ih =>
    simp only [allocGlobals] at h
    split at h
    · cases h
    · rename_i value heq
      exact FuncsFrom.trans (b := (store.allocGlobal { type := g.type, value }).1)
        (.of_eq rfl) (ih _ _ h)

theorem allocElems_from (store : Store H) (inst : ModuleInst) (elems : List Elem)
    {store' : Store H} {addrs : Array Nat}
    (h : allocElems store inst elems = .ok (store', addrs)) : FuncsFrom fs store store' := by
  induction elems generalizing store addrs with
  | nil => simp only [allocElems, Except.ok.injEq, Prod.mk.injEq] at h; exact h.1 ▸ .refl _
  | cons e rest ih =>
    simp only [allocElems] at h
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i x1 refs hrefs x2 store2 addrs2 heq
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact FuncsFrom.trans (b := (store.allocElem { elems := refs.toArray }).1)
          (.of_eq rfl) (ih _ heq)

theorem initElem_from (store : Store H) (inst : ModuleInst) (i : Nat) (e : Elem) {store' : Store H}
    (h : initElem store inst i e = .ok store') : FuncsFrom fs store store' := by
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
          subst h
          exact .of_eq rfl
  · simp only [Except.ok.injEq] at h; subst h; exact .of_eq rfl
  · simp only [Except.ok.injEq] at h; subst h; exact .refl _

theorem initElems_from (store : Store H) (inst : ModuleInst) (segs : List (Nat × Elem))
    {store' : Store H} (h : initElems store inst segs = .ok store') : FuncsFrom fs store store' := by
  induction segs generalizing store with
  | nil => simp only [initElems, Except.ok.injEq] at h; exact h ▸ .refl _
  | cons seg rest ih =>
    obtain ⟨i, e⟩ := seg
    simp only [initElems] at h
    split at h
    · cases h
    · rename_i heq
      exact (initElem_from _ _ _ _ heq).trans (ih _ h)

theorem initData_from (store : Store H) (inst : ModuleInst) (i : Nat) (d : Data) {store' : Store H}
    (h : initData store inst i d = .ok store') : FuncsFrom fs store store' := by
  unfold initData at h
  split at h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h
          subst h
          exact .of_eq (by simp [Exec.setMemOf_funcs])
  · simp only [Except.ok.injEq] at h; subst h; exact .refl _

theorem initDatas_from (store : Store H) (inst : ModuleInst) (segs : List (Nat × Data))
    {store' : Store H} (h : initDatas store inst segs = .ok store') : FuncsFrom fs store store' := by
  induction segs generalizing store with
  | nil => simp only [initDatas, Except.ok.injEq] at h; exact h ▸ .refl _
  | cons seg rest ih =>
    obtain ⟨i, d⟩ := seg
    simp only [initDatas] at h
    split at h
    · cases h
    · rename_i heq
      exact (initData_from _ _ _ _ heq).trans (ih _ h)

/-- Every function in an instantiated store was there before or is one of the module's. -/
theorem instantiateModule_from (store : Store H) (vm : ValidModule) (imports : List ExternVal)
    {store' : Store H} {inst : ModuleInst}
    (h : instantiateModule store vm imports = .ok (store', inst)) : FuncsFrom vm.module.funcs.toList store store' := by
  unfold instantiateModule at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i x1 s1 i1 hg
        split at h
        · cases h
        · rename_i x2 s2 a2 he
          split at h
          · cases h
          · rename_i x3 s3 hie
            split at h
            · cases h
            · rename_i x4 s4 hid
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact (allocModule_from _ _).trans ((allocFuncs_from _ _ _ _ (fun _ h => h)).trans
                ((allocTables_from _ _).trans ((allocMems_from _ _).trans
                ((allocGlobals_from _ _ _ hg).trans ((allocElems_from _ _ _ he).trans
                ((allocDatas_from _ _).trans ((setModule_from _ _ _).trans
                ((initElems_from _ _ _ hie).trans (initDatas_from _ _ _ hid)))))))))

end Wasm.Link
