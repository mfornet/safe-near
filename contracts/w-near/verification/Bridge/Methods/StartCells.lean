import Bridge.Methods.InitialState
import Binary.Run
import NearLogic.Adequacy

/-!
# The cells of the store a method starts from

`startList cfg h`: the cells of `wStore cfg h` a method of `contract.wasm` needs: the instance,
the memory's limit and length, the stack pointer global, the host (gas erased) and the gas
counter, the 215 table entries, the 955 functions and every byte of the memory. `startCells`
takes them out of the ownership adequacy gives (`ownCells (mheapOf ⟨wStore cfg h⟩)`), and
`startSplit` separates them, the memory as one `memR` (term mode: the proof mode is never run
on the memory's byte list). `tableOf`: the entries `ft_total_supply` uses (`tableRes`).
`persistList`: read-only cells (functions) made persistent.
-/

namespace WNear.Binary.InitialState

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic Iris.Std

/-- The stack pointer's global as instantiated. -/
def g0 : GlobalInst := { type := { type := .num .i32, mutable := true }, value := .i32 1048576 }

/-- The table's entries. -/
def tabCells : List (Loc × Cell NearState) := (List.range 215).map fun i => (Loc.tableElem 0 i, .ref wTable.elems[i]!)

/-- The functions. -/
noncomputable def funcCells (cfg : RuntimeConfig) (h : NearState) : List (Loc × Cell NearState) :=
  (List.range 955).map fun a => (Loc.func a, .func ((wStore cfg h).funcs.getD a (.wasm types[0]! 0 f68)))

/-- The cells a method starts with. -/
noncomputable def startList (cfg : RuntimeConfig) (h : NearState) : List (Loc × Cell NearState) :=
  [(Loc.inst 0, .inst wInst), (Loc.memLimit 0, .memLimit (some 2048)), (Loc.memLength 0, .memLength memLen),
    (Loc.global 0, .global g0), (Loc.host, .host (erase h)), (gasLoc, gasCellOf h.gas h.gasProfile h.actionProfile)] ++
    (tabCells ++ (funcCells cfg h ++ byteCells 0 0 (wDataMem.readList 0 memLen)))

theorem wTable_size : wTable.elems.size = 215 := by rfl

theorem wStore_funcs_size (cfg : RuntimeConfig) (h : NearState) : (wStore cfg h).funcs.size = 955 := by
  simp [wStore, wHosts_length, funcs_size]

theorem byteCells_fst (n i : Nat) (bs : List UInt8) :
    ∀ p ∈ byteCells (H := NearState) n i bs, p.1.1 = 0 ∧ p.1.2.1 = n ∧ i ≤ p.1.2.2 ∧ p.1.2.2 < i + bs.length ∧
      p.2 = .byte bs[p.1.2.2 - i]! := by
  intro p hp
  have := lookup_byteCells (H := NearState) n i bs p.1
  rw [lookup_of_mem (byteCells_nodup _ _ _) hp] at this
  split at this
  · rename_i h
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only [Option.some.injEq] at this
    exact ⟨h1, h2, h3, h4, this⟩
  · cases this

theorem startList_nodup (cfg : RuntimeConfig) (h : NearState) : ((startList cfg h).map (·.1)).Nodup := by
  have hb := byteCells_fst (n := 0) (i := 0) (bs := wDataMem.readList 0 memLen)
  simp only [startList, List.map_append, List.map_cons, List.map_nil, tabCells, funcCells, List.map_map]
  rw [List.nodup_append, List.nodup_append, List.nodup_append]
  refine ⟨by decide, ⟨?_, ⟨?_, byteCells_nodup _ _ _, ?_⟩, ?_⟩, ?_⟩
  · apply List.Nodup.map _ List.nodup_range
    intro a b e; simp only [Function.comp, Prod.mk.injEq] at e; exact e.2.2
  · apply List.Nodup.map _ List.nodup_range
    intro a b e; simp only [Function.comp, Prod.mk.injEq] at e; exact e.2.1
  · intro x hx y hy e
    subst e
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    obtain ⟨q, hq, e⟩ := List.mem_map.1 hy
    have := (hb q hq).1
    rw [e] at this; simp at this
  · intro x hx y hy e
    subst e
    obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
    rw [List.mem_append] at hy
    rcases hy with hy | hy
    · obtain ⟨b, -, e⟩ := List.mem_map.1 hy; simp at e
    · obtain ⟨q, hq, e⟩ := List.mem_map.1 hy
      have := (hb q hq).1
      rw [e] at this; simp at this
  · intro x hx y hy e
    subst e
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rw [List.mem_append, List.mem_append] at hy
    rcases hy with hy | hy | hy
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
      rcases hx with e | e | e | e | e | e <;> simp at e
    · obtain ⟨b, -, rfl⟩ := List.mem_map.1 hy
      rcases hx with e | e | e | e | e | e <;> simp at e
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hy
      have := (hb q hq).1
      rcases hx with e | e | e | e | e | e <;> (rw [e] at this; simp at this)

theorem readList_get (m : Memory) (len j : Nat) (hj : j < len) : (m.readList 0 len)[j]! = m.read8 j := by
  rw [readList_eq, getElem!_pos _ _ (by simpa using hj)]
  simp

theorem startList_get (cfg : RuntimeConfig) (h : NearState) :
    ∀ p ∈ startList cfg h, PartialMap.get? (mheapOf ⟨wStore cfg h⟩) p.1 = some p.2 := by
  intro p hp
  have hm : (wStore cfg h).mems[0]? = some wDataMem := by
    simp only [wStore, List.getElem?_toArray, List.getElem?_cons_zero]
  rw [get?_mheapOf]
  simp only [startList, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with (rfl | rfl | rfl | rfl | rfl | rfl) | hp | hp | hp
  · rw [mlookup_plain _ (by unfold isPlain; simp)]; rfl
  · rw [mlookup_plain _ (by unfold isPlain; simp), lookup_memLimit, hm, Option.bind_some,
      if_pos wDataMem_facts.1, wDataMem_facts.2.2.1]
  · rw [mlookup_plain _ (by unfold isPlain; simp), lookup_memLength, hm, Option.bind_some,
      if_pos wDataMem_facts.1, wDataMem_facts.2.1]
  · rw [mlookup_plain _ (by unfold isPlain; simp)]; rfl
  · simp only [mlookup]; rfl
  · simp only [mlookup]; rfl
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
    simp only [List.mem_range] at hi
    have ht : (wStore cfg h).tables[0]? = some wTable := by
      simp only [wStore, List.getElem?_toArray, List.getElem?_cons_zero]
    rw [mlookup_plain _ (by unfold isPlain; simp), lookup_tableElem, ht, Option.bind_some,
      Array.getElem?_eq_getElem (by rw [wTable_size]; exact hi), getElem!_pos _ _ (by rw [wTable_size]; exact hi)]
    rfl
  · obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
    simp only [List.mem_range] at ha
    rw [mlookup_plain _ (by unfold isPlain; simp), lookup_func,
      Array.getElem?_eq_getElem (by rw [wStore_funcs_size]; exact ha), Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem (by rw [wStore_funcs_size]; exact ha)]
    rfl
  · obtain ⟨h1, h2, -, h4, h5⟩ := byteCells_fst 0 0 _ p hp
    obtain ⟨⟨k, a, j⟩, c⟩ := p
    simp only at h1 h2 h4 h5 ⊢
    subst h1 h2 h5
    rw [Memory.readList_length, Nat.zero_add] at h4
    rw [mlookup_plain _ (by unfold isPlain; simp), lookup_byte, hm, Option.bind_some,
      if_pos ⟨wDataMem_facts.1, by rw [wDataMem_facts.2.1]; exact h4⟩, Nat.sub_zero, readList_get _ _ _ h4]

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- **The cells of the start**, out of the ownership adequacy gives. -/
theorem startCells (cfg : RuntimeConfig) (h : NearState) :
    ownCells (GF := GF) (mheapOf ⟨wStore cfg h⟩) ⊢ [∗list] p ∈ startList cfg h, p.1 ↦ₛ p.2 :=
  ownCells_take _ _ (startList_nodup cfg h) (startList_get cfg h)

/-- The memory's bytes, as one `memR`. -/
theorem byteCells_memR (m : Memory) (n len : Nat) :
    ([∗list] p ∈ byteCells (H := NearState) n 0 (m.readList 0 len), p.1 ↦ₛ p.2) ⊢ memR (GF := GF) m n 0 len :=
  .rfl

/-- The start's cells, separated: instance, limit, length, global, host, gas, table, functions,
memory. -/
theorem startSplit (cfg : RuntimeConfig) (h : NearState) :
    ([∗list] p ∈ startList cfg h, p.1 ↦ₛ p.2) ⊢
      (Loc.inst 0 ↦ₛ (.inst wInst : Cell NearState) ∗ Loc.memLimit 0 ↦ₛ (.memLimit (some 2048) : Cell NearState) ∗
        0 ↦[wmlength] memLen ∗ 0 ↦[wg] g0 ∗ mhostPt h ∗ gasPt h.gas h.gasProfile h.actionProfile) ∗
      ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ∗ ([∗list] p ∈ funcCells cfg h, p.1 ↦ₛ p.2) ∗
      memR (GF := GF) wDataMem 0 0 memLen := by
  unfold startList
  refine BigSepL.bigSepL_append.1.trans (sep_mono ?_ (BigSepL.bigSepL_append.1.trans
    (sep_mono_right (BigSepL.bigSepL_append.1.trans (sep_mono_right (byteCells_memR _ _ _))))))
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H1, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H2, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H3, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H4, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H5, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H6, -⟩
  iframe H1 H2
  iunfold memLength, globalPt, mhostPt, gasPt
  iframe H3 H4 H5 H6

/-- An affine big separating conjunction over a sublist. -/
theorem bigSepL_sublist {A : Type} {Φ : A → IProp GF} {l₁ l₂ : List A} (h : l₂.Sublist l₁) :
    ([∗list] x ∈ l₁, Φ x) ⊢ [∗list] x ∈ l₂, Φ x := by
  induction h with
  | slnil => exact .rfl
  | cons a _ ih =>
    exact (BigSepL.bigSepL_cons (Φ := fun _ x => Φ x)).1.trans (sep_elim_right.trans ih)
  | cons_cons a _ ih =>
    exact (BigSepL.bigSepL_cons (Φ := fun _ x => Φ x)).1.trans ((sep_mono_right ih).trans
      (BigSepL.bigSepL_cons (Φ := fun _ x => Φ x)).2)

set_option maxRecDepth 100000 in
/-- The table entries `ft_total_supply` uses. -/
theorem tableOf : ([∗list] p ∈ tabCells, p.1 ↦ₛ p.2) ⊢ tableRes (GF := GF) 0 := by
  have hs : (([38, 39, 58, 82, 92, 106, 116, 123, 157] : List Nat).map fun i =>
      ((Loc.tableElem 0 i, .ref wTable.elems[i]!) : Loc × Cell NearState)).Sublist tabCells :=
    List.Sublist.map _ (by decide)
  refine (bigSepL_sublist (Φ := fun p : Loc × Cell NearState => iprop(p.1 ↦ₛ p.2)) hs).trans ?_
  simp only [List.map_cons, List.map_nil]
  have e : ∀ i (r : Ref), wTable.elems[i]! = r →
      ((Loc.tableElem 0 i ↦ₛ (.ref wTable.elems[i]! : Cell NearState)) : IProp GF) ⊢ 0 ↦[wt][ i ] r := by
    intro i r hr; rw [hr]; exact .rfl
  iintro H
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H38, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H39, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H58, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H82, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H92, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H106, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H116, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H123, H⟩
  icases BigSepL.bigSepL_cons.1 $$ H with ⟨H157, -⟩
  ihave H38 := e 38 (Ref.func 240) rfl $$ H38
  ihave H39 := e 39 (Ref.func 241) rfl $$ H39
  ihave H58 := e 58 (Ref.func 260) rfl $$ H58
  ihave H82 := e 82 (Ref.func 284) rfl $$ H82
  ihave H92 := e 92 (Ref.func 353) rfl $$ H92
  ihave H106 := e 106 (Ref.func 564) rfl $$ H106
  ihave H116 := e 116 (Ref.func 565) rfl $$ H116
  ihave H123 := e 123 (Ref.func 578) rfl $$ H123
  ihave H157 := e 157 (Ref.func 759) rfl $$ H157
  iunfold tableRes
  iframe H38 H39 H58 H82 H92 H106 H116 H123 H157

/-- Read-only cells made persistent. -/
theorem persistList (l : List (Loc × Cell NearState)) :
    ([∗list] p ∈ l, p.1 ↦ₛ p.2) ⊢ |==> ([∗list] p ∈ l, p.1 ↦ₛ□ p.2 : IProp GF) := by
  induction l with
  | nil =>
    iintro _
    imodintro
    iapply BigSepL.bigSepL_nil.2
    iempintro
  | cons p l ih =>
    iintro H
    icases BigSepL.bigSepL_cons.1 $$ H with ⟨Hp, Hl⟩
    imod pointsTo_persist _ _ $$ Hp with #Hp
    imod ih $$ Hl with Hl
    imodintro
    iapply BigSepL.bigSepL_cons.2
    iframe Hp Hl

end Res

end WNear.Binary.InitialState
