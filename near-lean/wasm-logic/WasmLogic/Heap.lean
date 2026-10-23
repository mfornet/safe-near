import Wasm
import WasmLogic.MemoryLemmas
import Iris.Std.HeapInstances
import Iris.Std.PartialMap

/-!
# The store as a heap

Separation logic needs the store as a finite map from locations to cells, so
that ownership can be split cell by cell. A location names one byte of a
memory, the size of a memory, one global, one table entry, the size of a
table, one function, one module instance, one element or data segment, or
the host state.

Memory cells exist only while the memory is well formed (`Memory.wf`): its
pages are empty or full. Every runtime operation keeps memories well formed;
owning a byte therefore tells the logic the byte API behaves as an array.

`lookup σ` reads a location off a store. `heapOf σ` is the same function as a
finite map (`get?_heapOf`); it is what the state interpretation owns. Nothing
here changes how the runtime represents the store: the heap is a view of it.
-/

namespace WasmLogic

open Wasm Iris.Std

/-- A location: kind, address, offset. A product of naturals so that the
order the finite maps need comes from the library. -/
abbrev Loc := Nat × Nat × Nat

/-- Lexicographic, as the library's lawfulness instances for products expect. -/
instance instOrdNatNat : Ord (Nat × Nat) := lexOrd
instance instOrdLoc : Ord Loc := lexOrd

namespace Loc
/-- Byte `i` of the memory at store address `m`. -/
abbrev byte (m i : Nat) : Loc := (0, m, i)
/-- The length in bytes of the memory at `m`. -/
abbrev memLength (m : Nat) : Loc := (1, m, 0)
/-- The declared maximum, in pages, of the memory at `m`. -/
abbrev memLimit (m : Nat) : Loc := (1, m, 1)
abbrev global (g : Nat) : Loc := (2, g, 0)
/-- Entry `i` of the table at `t`. -/
abbrev tableElem (t i : Nat) : Loc := (3, t, i)
/-- The size, element type and maximum of the table at `t`. -/
abbrev tableInfo (t : Nat) : Loc := (4, t, 0)
abbrev func (a : Nat) : Loc := (5, a, 0)
abbrev inst (i : Nat) : Loc := (6, i, 0)
abbrev elem (a : Nat) : Loc := (7, a, 0)
abbrev data (a : Nat) : Loc := (8, a, 0)
abbrev host : Loc := (9, 0, 0)
end Loc

/-- What a location holds. -/
inductive Cell (H : Type) where
  | byte (b : UInt8)
  | memLength (bytes : Nat)
  | memLimit (max : Option Nat)
  | global (g : GlobalInst)
  | ref (r : Ref)
  | tableInfo (size : Nat) (elemType : RefType) (max : Option Nat)
  | func (f : FuncInst H)
  | inst (m : ModuleInst)
  | elem (e : ElemInst)
  | data (d : DataInst)
  | host (h : H)

/-- The cell at a location of a store. -/
def lookup (σ : Store H) : Loc → Option (Cell H)
  | (0, m, i) => σ.mems[m]?.bind fun mem =>
      if mem.wf ∧ i < mem.byteSize then some (.byte (mem.read8 i)) else none
  | (1, m, 0) => σ.mems[m]?.bind fun mem =>
      if mem.wf then some (.memLength mem.byteSize) else none
  | (1, m, 1) => σ.mems[m]?.bind fun mem => if mem.wf then some (.memLimit mem.max) else none
  | (2, g, 0) => σ.globals[g]?.map .global
  | (3, t, i) => σ.tables[t]?.bind fun tab => tab.elems[i]?.map .ref
  | (4, t, 0) => σ.tables[t]?.map fun tab => .tableInfo tab.elems.size tab.elemType tab.max
  | (5, a, 0) => σ.funcs[a]?.map .func
  | (6, i, 0) => σ.modules[i]?.map .inst
  | (7, a, 0) => σ.elems[a]?.map .elem
  | (8, a, 0) => σ.datas[a]?.map .data
  | (9, 0, 0) => some (.host σ.host)
  | _ => none

section lookup
variable (σ : Store H)
@[simp] theorem lookup_byte (m i : Nat) : lookup σ (Loc.byte m i) =
    σ.mems[m]?.bind fun mem =>
      if mem.wf ∧ i < mem.byteSize then some (.byte (mem.read8 i)) else none :=
  rfl
@[simp] theorem lookup_memLength (m : Nat) : lookup σ (Loc.memLength m) =
    σ.mems[m]?.bind fun mem => if mem.wf then some (.memLength mem.byteSize) else none := rfl
@[simp] theorem lookup_memLimit (m : Nat) : lookup σ (Loc.memLimit m) =
    σ.mems[m]?.bind fun mem => if mem.wf then some (.memLimit mem.max) else none := rfl
@[simp] theorem lookup_global (g : Nat) : lookup σ (Loc.global g) = σ.globals[g]?.map .global :=
  rfl
@[simp] theorem lookup_tableElem (t i : Nat) :
    lookup σ (Loc.tableElem t i) = σ.tables[t]?.bind fun tab => tab.elems[i]?.map .ref := rfl
@[simp] theorem lookup_tableInfo (t : Nat) : lookup σ (Loc.tableInfo t) =
    σ.tables[t]?.map fun tab => .tableInfo tab.elems.size tab.elemType tab.max := rfl
@[simp] theorem lookup_func (a : Nat) : lookup σ (Loc.func a) = σ.funcs[a]?.map .func := rfl
@[simp] theorem lookup_inst (i : Nat) : lookup σ (Loc.inst i) = σ.modules[i]?.map .inst := rfl
@[simp] theorem lookup_elem (a : Nat) : lookup σ (Loc.elem a) = σ.elems[a]?.map .elem := rfl
@[simp] theorem lookup_data (a : Nat) : lookup σ (Loc.data a) = σ.datas[a]?.map .data := rfl
@[simp] theorem lookup_host : lookup σ Loc.host = some (.host σ.host) := rfl
end lookup

/-! ## Finite maps over locations -/

/-- Finite maps keyed by locations. -/
abbrev HeapF := fun V => Std.ExtTreeMap Loc V compare

/-- The finite map that agrees with `f` on the keys `ks`. -/
def ofFun (ks : List Loc) (f : Loc → Option V) : HeapF V :=
  ks.foldl (fun acc k => match f k with
    | some v => PartialMap.insert acc k v
    | none => acc) ∅

theorem get?_ofFun_aux (ks : List Loc) (f : Loc → Option V) (acc : HeapF V) (k : Loc) :
    get? (ks.foldl (fun acc k => match f k with
      | some v => PartialMap.insert acc k v
      | none => acc) acc) k = if k ∈ ks then (f k).or (get? acc k) else get? acc k := by
  induction ks generalizing acc with
  | nil => simp
  | cons k' ks ih =>
    simp only [List.foldl_cons, List.mem_cons]
    rw [ih]
    by_cases hk : k = k'
    · subst hk
      cases hf : f k with
      | none => simp
      | some v => simp [LawfulPartialMap.get?_insert_eq rfl]
    · cases hf : f k' with
      | none => simp [hk]
      | some v =>
        simp only [hk, false_or]
        rw [LawfulPartialMap.get?_insert_ne (Ne.symm hk)]

theorem get?_ofFun (ks : List Loc) (f : Loc → Option V) (k : Loc) :
    get? (ofFun ks f) k = if k ∈ ks then f k else none := by
  unfold ofFun
  rw [get?_ofFun_aux]
  simp [LawfulPartialMap.get?_empty]

/-! ## The heap of a store -/

/-- A bound on every address and offset in a store. -/
def storeBound (σ : Store H) : Nat :=
  σ.funcs.size + σ.tables.size + σ.mems.size + σ.globals.size + σ.elems.size + σ.datas.size +
    σ.modules.size + (σ.mems.toList.map Memory.byteSize).sum +
    (σ.tables.toList.map (·.elems.size)).sum + 1

/-- Every location below the bound. -/
def storeKeys (σ : Store H) : List Loc :=
  (List.range 10).flatMap fun k => (List.range (storeBound σ)).flatMap fun a =>
    (List.range (storeBound σ)).map fun i => (k, a, i)

theorem lt_bound_of_get? {α} (xs : Array α) (n : Nat) {x : α} (h : xs[n]? = some x)
    (hle : xs.size ≤ m) : n < m := by
  have := (Array.getElem?_eq_some_iff.mp h).1
  omega

theorem le_sum_of_mem {xs : List Nat} {x : Nat} (h : x ∈ xs) : x ≤ xs.sum := by
  induction xs with
  | nil => cases h
  | cons y ys ih =>
    simp only [List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem le_sum_of_get? (xs : Array α) (f : α → Nat) {n : Nat} {x : α} (h : xs[n]? = some x) :
    f x ≤ (xs.toList.map f).sum :=
  le_sum_of_mem (List.mem_map.mpr ⟨x, Array.mem_toList_iff.mpr (Array.mem_of_getElem? h), rfl⟩)

/-- `lookup` is supported below the bound. -/
theorem mem_keys_of_lookup {σ : Store H} {l : Loc} {c : Cell H} (h : lookup σ l = some c) :
    l ∈ storeKeys σ := by
  obtain ⟨k, a, i⟩ := l
  simp only [storeKeys, List.mem_flatMap, List.mem_range, List.mem_map, Prod.mk.injEq]
  have hb : ∀ {α} (xs : Array α) {n x}, xs[n]? = some x → n < xs.size := fun xs _ _ h =>
    (Array.getElem?_eq_some_iff.mp h).1
  unfold storeBound
  match k, a, i, h with
  | 0, m, i, h =>
    simp only [lookup] at h
    obtain ⟨mem, hm, h⟩ := Option.bind_eq_some_iff.mp h
    split at h
    · rename_i hi
      have := hb _ hm
      have := le_sum_of_get? σ.mems Memory.byteSize hm
      exact ⟨0, by omega, m, by omega, i, by omega, rfl, rfl, rfl⟩
    · cases h
  | 1, m, 0, h =>
    obtain ⟨_, hm, _⟩ := Option.bind_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨1, by omega, m, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 1, m, 1, h =>
    obtain ⟨_, hm, _⟩ := Option.bind_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨1, by omega, m, by omega, 1, by omega, rfl, rfl, rfl⟩
  | 2, g, 0, h =>
    obtain ⟨_, hm, _⟩ := Option.map_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨2, by omega, g, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 3, t, i, h =>
    simp only [lookup] at h
    obtain ⟨tab, ht, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, he, _⟩ := Option.map_eq_some_iff.mp h
    have := hb _ ht
    have := hb _ he
    have := le_sum_of_get? σ.tables (·.elems.size) ht
    exact ⟨3, by omega, t, by omega, i, by omega, rfl, rfl, rfl⟩
  | 4, t, 0, h =>
    obtain ⟨_, hm, _⟩ := Option.map_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨4, by omega, t, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 5, a, 0, h =>
    obtain ⟨_, hm, _⟩ := Option.map_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨5, by omega, a, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 6, a, 0, h =>
    obtain ⟨_, hm, _⟩ := Option.map_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨6, by omega, a, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 7, a, 0, h =>
    obtain ⟨_, hm, _⟩ := Option.map_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨7, by omega, a, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 8, a, 0, h =>
    obtain ⟨_, hm, _⟩ := Option.map_eq_some_iff.mp h
    have := hb _ hm
    exact ⟨8, by omega, a, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 9, 0, 0, _ => exact ⟨9, by omega, 0, by omega, 0, by omega, rfl, rfl, rfl⟩
  | 1, _, _ + 2, h | 2, _, _ + 1, h | 4, _, _ + 1, h | 5, _, _ + 1, h | 6, _, _ + 1, h
  | 7, _, _ + 1, h | 8, _, _ + 1, h | 9, _ + 1, _, h | 9, 0, _ + 1, h
  | _ + 10, _, _, h => simp [lookup] at h

/-- The store as a finite map. -/
def heapOf (σ : Store H) : HeapF (Cell H) := ofFun (storeKeys σ) (lookup σ)

@[simp] theorem get?_heapOf (σ : Store H) (l : Loc) : get? (heapOf σ) l = lookup σ l := by
  unfold heapOf
  rw [get?_ofFun]
  split
  · rfl
  · rename_i hl
    cases h : lookup σ l with
    | none => rfl
    | some c => exact absurd (mem_keys_of_lookup h) hl

/-! ## Which locations a store update touches -/

section frame
variable (σ : Store H)

theorem lookup_with_mems (ms : Array Memory) (l : Loc) (hl : l.1 ≠ 0 ∧ l.1 ≠ 1) :
    lookup { σ with mems := ms } l = lookup σ l := by
  obtain ⟨k, a, i⟩ := l
  simp only at hl
  unfold lookup
  split <;> simp_all

theorem lookup_with_globals (gs : Array GlobalInst) (l : Loc) (hl : l.1 ≠ 2) :
    lookup { σ with globals := gs } l = lookup σ l := by
  obtain ⟨k, a, i⟩ := l
  simp only at hl
  unfold lookup
  split <;> simp_all

theorem lookup_with_tables (ts : Array TableInst) (l : Loc) (hl : l.1 ≠ 3 ∧ l.1 ≠ 4) :
    lookup { σ with tables := ts } l = lookup σ l := by
  obtain ⟨k, a, i⟩ := l
  simp only at hl
  unfold lookup
  split <;> simp_all

theorem lookup_with_host (h : H) (l : Loc) (hl : l.1 ≠ 9) :
    lookup { σ with host := h } l = lookup σ l := by
  obtain ⟨k, a, i⟩ := l
  simp only at hl
  unfold lookup
  split <;> simp_all

theorem lookup_with_elems (es : Array ElemInst) (l : Loc) (hl : l.1 ≠ 7) :
    lookup { σ with elems := es } l = lookup σ l := by
  obtain ⟨k, a, i⟩ := l
  simp only at hl
  unfold lookup
  split <;> simp_all

theorem lookup_with_datas (ds : Array DataInst) (l : Loc) (hl : l.1 ≠ 8) :
    lookup { σ with datas := ds } l = lookup σ l := by
  obtain ⟨k, a, i⟩ := l
  simp only at hl
  unfold lookup
  split <;> simp_all

end frame

/-- Two stores with the same lookup have the same heap. -/
theorem heapOf_eq_of_lookup {σ σ' : Store H} (h : ∀ l, lookup σ' l = lookup σ l) :
    heapOf σ' = heapOf σ :=
  LawfulPartialMap.equiv_iff_eq.mp fun l => by simp [h]

end WasmLogic
