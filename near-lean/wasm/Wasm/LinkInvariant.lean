import Wasm.Link
import Wasm.HostInvariant

/-!
# Instantiation and host-state invariants

Instantiating a module allocates Wasm functions, tables, memories, globals
and segments, and writes active segments; it never touches the host state
and never adds a host function. So a predicate on the host state that holds
before instantiation holds after it, and the host functions that could
preserve it are the same ones.
-/

namespace Wasm.Link

/-- The store's host state and host functions are unchanged. -/
def SameHosts (before after : Store H) : Prop :=
  after.host = before.host ∧
    ∀ fn, FuncInst.host fn ∈ after.funcs → FuncInst.host fn ∈ before.funcs

theorem SameHosts.refl (s : Store H) : SameHosts s s := ⟨rfl, fun _ h => h⟩

theorem SameHosts.trans {a b c : Store H} (h₁ : SameHosts a b) (h₂ : SameHosts b c) :
    SameHosts a c :=
  ⟨h₂.1.trans h₁.1, fun fn h => h₁.2 fn (h₂.2 fn h)⟩

/-- Changing anything but `funcs` and `host` keeps the hosts. -/
theorem SameHosts.of_eq {a b : Store H} (hh : b.host = a.host) (hf : b.funcs = a.funcs) :
    SameHosts a b :=
  ⟨hh, fun _ h => hf ▸ h⟩

theorem allocModule_same (s : Store H) (m : ModuleInst) : SameHosts s (s.allocModule m).1 :=
  .of_eq rfl rfl

theorem setModule_same (s : Store H) (i : Nat) (m : ModuleInst) : SameHosts s (s.setModule i m) :=
  .of_eq rfl rfl

theorem allocFunc_wasm_same (s : Store H) (t : FuncType) (i : Nat) (f : Func) :
    SameHosts s (s.allocFunc (.wasm t i f)).1 := by
  refine ⟨rfl, fun fn h => ?_⟩
  simp only [Store.allocFunc, Array.mem_push] at h
  rcases h with h | h
  · exact h
  · cases h

theorem allocFuncs_same (store : Store H) (types : Array FuncType) (instAddr : Nat)
    (funcs : List Func) : SameHosts store (allocFuncs store types instAddr funcs).1 := by
  unfold allocFuncs
  suffices key : ∀ (init : Store H × Array Nat),
      SameHosts init.1 (funcs.foldl (fun (store, addrs) f =>
        let (store, addr) := store.allocFunc (.wasm types[f.type]! instAddr f)
        (store, addrs.push addr)) init).1 by
    exact key (store, #[])
  intro init
  induction funcs generalizing init with
  | nil => exact .refl _
  | cons f rest ih =>
    obtain ⟨st, addrs⟩ := init
    simp only [List.foldl_cons]
    exact (allocFunc_wasm_same st _ _ _).trans (ih _)

theorem allocTables_same (store : Store H) (tables : List Table) :
    SameHosts store (allocTables store tables).1 := by
  unfold allocTables
  suffices key : ∀ (init : Store H × Array Nat),
      SameHosts init.1 (tables.foldl (fun (store, addrs) t =>
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
    exact (SameHosts.of_eq rfl rfl).trans (ih _)

theorem allocMems_same (store : Store H) (mems : List Mem) :
    SameHosts store (allocMems store mems).1 := by
  unfold allocMems
  suffices key : ∀ (init : Store H × Array Nat),
      SameHosts init.1 (mems.foldl (fun (store, addrs) mem =>
        let (store, addr) := store.allocMem (Memory.new mem.type.limits.min mem.type.limits.max)
        (store, addrs.push addr)) init).1 by
    exact key (store, #[])
  intro init
  induction mems generalizing init with
  | nil => exact .refl _
  | cons m rest ih =>
    obtain ⟨st, addrs⟩ := init
    simp only [List.foldl_cons]
    exact (SameHosts.of_eq rfl rfl).trans (ih _)

theorem allocDatas_same (store : Store H) (datas : List Data) :
    SameHosts store (allocDatas store datas).1 := by
  unfold allocDatas
  suffices key : ∀ (init : Store H × Array Nat),
      SameHosts init.1 (datas.foldl (fun (store, addrs) d =>
        let (store, addr) := store.allocData { bytes := d.init }
        (store, addrs.push addr)) init).1 by
    exact key (store, #[])
  intro init
  induction datas generalizing init with
  | nil => exact .refl _
  | cons d rest ih =>
    obtain ⟨st, addrs⟩ := init
    simp only [List.foldl_cons]
    exact (SameHosts.of_eq rfl rfl).trans (ih _)

theorem allocGlobals_same (store : Store H) (inst : ModuleInst) (globals : List Global)
    {store' : Store H} {inst' : ModuleInst}
    (h : allocGlobals store inst globals = .ok (store', inst')) : SameHosts store store' := by
  induction globals generalizing store inst with
  | nil => simp only [allocGlobals, Except.ok.injEq, Prod.mk.injEq] at h; exact h.1 ▸ .refl _
  | cons g rest ih =>
    simp only [allocGlobals] at h
    split at h
    · cases h
    · rename_i value heq
      exact SameHosts.trans (b := (store.allocGlobal { type := g.type, value }).1)
        (.of_eq rfl rfl) (ih _ _ h)

theorem allocElems_same (store : Store H) (inst : ModuleInst) (elems : List Elem)
    {store' : Store H} {addrs : Array Nat}
    (h : allocElems store inst elems = .ok (store', addrs)) : SameHosts store store' := by
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
        exact SameHosts.trans (b := (store.allocElem { elems := refs.toArray }).1)
          (.of_eq rfl rfl) (ih _ heq)

theorem initElem_same (store : Store H) (inst : ModuleInst) (i : Nat) (e : Elem) {store' : Store H}
    (h : initElem store inst i e = .ok store') : SameHosts store store' := by
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
          exact .of_eq rfl rfl
  · simp only [Except.ok.injEq] at h; subst h; exact .of_eq rfl rfl
  · simp only [Except.ok.injEq] at h; subst h; exact .refl _

theorem initElems_same (store : Store H) (inst : ModuleInst) (segs : List (Nat × Elem))
    {store' : Store H} (h : initElems store inst segs = .ok store') : SameHosts store store' := by
  induction segs generalizing store with
  | nil => simp only [initElems, Except.ok.injEq] at h; exact h ▸ .refl _
  | cons seg rest ih =>
    obtain ⟨i, e⟩ := seg
    simp only [initElems] at h
    split at h
    · cases h
    · rename_i heq
      exact (initElem_same _ _ _ _ heq).trans (ih _ h)

theorem initData_same (store : Store H) (inst : ModuleInst) (i : Nat) (d : Data) {store' : Store H}
    (h : initData store inst i d = .ok store') : SameHosts store store' := by
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
          exact .of_eq (by simp [Exec.setMemOf_host]) (by simp [Exec.setMemOf_funcs])
  · simp only [Except.ok.injEq] at h; subst h; exact .refl _

theorem initDatas_same (store : Store H) (inst : ModuleInst) (segs : List (Nat × Data))
    {store' : Store H} (h : initDatas store inst segs = .ok store') : SameHosts store store' := by
  induction segs generalizing store with
  | nil => simp only [initDatas, Except.ok.injEq] at h; exact h ▸ .refl _
  | cons seg rest ih =>
    obtain ⟨i, d⟩ := seg
    simp only [initDatas] at h
    split at h
    · cases h
    · rename_i heq
      exact (initData_same _ _ _ _ heq).trans (ih _ h)

/-- Instantiation keeps the host state and adds no host function. -/
theorem instantiateModule_same (store : Store H) (vm : ValidModule) (imports : List ExternVal)
    {store' : Store H} {inst : ModuleInst}
    (h : instantiateModule store vm imports = .ok (store', inst)) : SameHosts store store' := by
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
              exact (allocModule_same _ _).trans ((allocFuncs_same _ _ _ _).trans
                ((allocTables_same _ _).trans ((allocMems_same _ _).trans
                ((allocGlobals_same _ _ _ hg).trans ((allocElems_same _ _ _ he).trans
                ((allocDatas_same _ _).trans ((setModule_same _ _ _).trans
                ((initElems_same _ _ _ hie).trans (initDatas_same _ _ _ hid)))))))))

end Wasm.Link
