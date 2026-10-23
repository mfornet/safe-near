import WasmLogic.Rules.Memory

/-!
# Rules for tables, segments and bulk memory

The instructions of the reference-types and bulk-memory proposals, which
nearcore enables (`NearVM` validates with `Features.nearcore true`): table
access, growth and bulk updates, element and data segment initialisation
and dropping, and `memory.fill` / `memory.copy` / `memory.init`. Iris-Wasm
(Wasm 1.0) has no counterpart; the rules have the shape of its memory rules:
each owns exactly the cells it touches. A bulk rule is for a non-empty range,
whose owned cells prove it in bounds; ranges that two operands share
(`table.copy`, `memory.copy`) must not overlap, since each is owned.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.ProgramLogic

section Assertions

variable {H : Type} {GF : BundledGFunctors} [ι : WasmGS H GF]

/-- The size, element type and maximum of the table at `t`. -/
def tableInfoPt (t size : Nat) (et : RefType) (mx : Option Nat) : IProp GF :=
  Loc.tableInfo t ↦ₛ (.tableInfo size et mx : Cell H)

/-- The element segment instance at `a`. -/
def elemPt (a : Nat) (e : ElemInst) : IProp GF := Loc.elem a ↦ₛ (.elem e : Cell H)

/-- The data segment instance at `a`. -/
def dataPt (a : Nat) (dt : DataInst) : IProp GF := Loc.data a ↦ₛ (.data dt : Cell H)

/-- Entries `i, i+1, …` of the table at `t`, as cells. -/
def entryCells (t i : Nat) : List Ref → List (Loc × Cell H)
  | [] => []
  | r :: rs => (Loc.tableElem t i, .ref r) :: entryCells t (i + 1) rs

/-- Entries `rs` from index `i` of the table at `t`. -/
def tableEntries (t i : Nat) (rs : List Ref) : IProp GF :=
  [∗list] p ∈ entryCells (H := H) t i rs, p.1 ↦ₛ p.2

end Assertions

notation:50 t:50 " ↦[wts][ " i " ] " rs:50 => tableEntries t i rs
notation:50 a:50 " ↦[welem] " e:50 => elemPt a e
notation:50 a:50 " ↦[wdata] " dt:50 => dataPt a dt

section Cells

variable {H : Type}

@[simp] theorem entryCells_length (t i : Nat) (rs : List Ref) :
    (entryCells (H := H) t i rs).length = rs.length := by
  induction rs generalizing i <;> simp_all [entryCells]

theorem lookup_entryCells (t i : Nat) (rs : List Ref) (l : Loc) :
    (entryCells (H := H) t i rs).lookup l =
      if l.1 = 3 ∧ l.2.1 = t ∧ i ≤ l.2.2 ∧ l.2.2 < i + rs.length then
        some (.ref rs[l.2.2 - i]!) else none := by
  induction rs generalizing i with
  | nil =>
    simp only [entryCells, List.length_nil, Nat.add_zero]
    split
    · omega
    · rfl
  | cons r rs ih =>
    obtain ⟨k, a, j⟩ := l
    rw [entryCells, lookup_cons_pair, ih]
    simp only [Loc.tableElem, Prod.mk.injEq, List.length_cons]
    by_cases hj : k = 3 ∧ a = t ∧ j = i
    · obtain ⟨rfl, rfl, rfl⟩ := hj
      simp
    · rw [ite_eq_right hj]
      by_cases hr : k = 3 ∧ a = t ∧ i + 1 ≤ j ∧ j < i + 1 + rs.length
      · have h1 : j - i = (j - (i + 1)) + 1 := by omega
        rw [ite_eq_left hr, ite_eq_left (by omega), h1]
        simp
      · rw [ite_eq_right hr, ite_eq_right (by omega)]

theorem entryCells_nodup (t i : Nat) (rs : List Ref) :
    ((entryCells (H := H) t i rs).map (·.1)).Nodup := by
  induction rs generalizing i with
  | nil => simp [entryCells]
  | cons r rs ih =>
    simp only [entryCells, List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih (i + 1)⟩
    obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hmem
    have := lookup_entryCells (H := H) t (i + 1) rs p.1
    rw [lookup_of_mem (ih (i + 1)) hp] at this
    split at this
    · rename_i h
      simp only [Loc.tableElem] at hp1
      rw [hp1] at h
      simp only at h
      omega
    · cases this

theorem mem_entryCells (t i : Nat) (rs : List Ref) {k : Nat} (hk : k < rs.length) :
    (Loc.tableElem t (i + k), (Cell.ref rs[k]! : Cell H)) ∈ entryCells (H := H) t i rs := by
  induction rs generalizing i k with
  | nil => cases hk
  | cons r rs ih =>
    cases k with
    | zero => simp [entryCells]
    | succ k =>
      simp only [entryCells, List.mem_cons]
      right
      have := ih (i + 1) (k := k) (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- What owning table entries says about the store. -/
theorem entries_facts {σ : Store H} {t i : Nat} {rs : List Ref} (hne : rs ≠ [])
    (h : ∀ p ∈ entryCells (H := H) t i rs, lookup σ p.1 = some p.2) :
    ∃ tab, σ.tables[t]? = some tab ∧ i + rs.length ≤ tab.elems.size ∧
      ∀ k, k < rs.length → tab.elems[i + k]? = some rs[k]! := by
  have hlen : 0 < rs.length := List.length_pos_iff.mpr hne
  have h0 := h _ (mem_entryCells t i rs hlen)
  simp only [lookup_tableElem, Option.bind_eq_some_iff] at h0
  obtain ⟨tab, htab, -⟩ := h0
  have hk : ∀ k, k < rs.length → tab.elems[i + k]? = some rs[k]! := by
    intro k hk
    have hl := h _ (mem_entryCells t i rs hk)
    simp only [lookup_tableElem, htab, Option.bind_some, Option.map_eq_some_iff] at hl
    obtain ⟨r, hr, he⟩ := hl
    cases he; exact hr
  refine ⟨tab, htab, ?_, hk⟩
  have := hk (rs.length - 1) (by omega)
  have := (Array.getElem?_eq_some_iff.mp this).1
  omega

/-- The cells of one table, by kind and index. -/
def tableCell (tab : TableInst) : Nat × Nat → Option (Cell H)
  | (3, i) => tab.elems[i]?.map .ref
  | (4, 0) => some (.tableInfo tab.elems.size tab.elemType tab.max)
  | _ => none

theorem lookup_table (σ : Store H) (k a i : Nat) (hk : k = 3 ∨ k = 4) :
    lookup σ (k, a, i) = σ.tables[a]?.bind fun tab => tableCell tab (k, i) := by
  rcases hk with rfl | rfl
  · simp [lookup, tableCell, Option.map_eq_bind]
  · rcases i with _ | i
    · simp [lookup, tableCell, Option.map_eq_bind]; rfl
    · simp [lookup, tableCell]

theorem lookup_setTable (σ : Store H) (a : Nat) (tab : TableInst) (ha : a < σ.tables.size)
    (k b i : Nat) : lookup (Exec.setTable σ a tab) (k, b, i) =
      if (k = 3 ∨ k = 4) ∧ b = a then tableCell tab (k, i) else lookup σ (k, b, i) := by
  unfold Exec.setTable
  by_cases hk : k = 3 ∨ k = 4
  · rw [lookup_table _ _ _ _ hk, lookup_table _ _ _ _ hk]
    by_cases hb : b = a
    · subst hb
      simp [hk, ha]
    · simp [hb, Ne.symm hb]
  · rw [lookup_with_tables _ _ _ (by simp only; omega)]
    simp [hk]

/-- Writing a run of entries, as `table.fill`, `table.copy` and `table.init`
do: `n` entries from `d`, the `k`-th being `g k`. -/
def writeEntries (elems : Array Ref) (d n : Nat) (g : Nat → Ref) : Array Ref :=
  (List.range n).foldl (fun es k => es.set! (d + k) (g k)) elems

theorem writeEntries_spec (elems : Array Ref) (d n : Nat) (g : Nat → Ref) (hb : d + n ≤ elems.size) :
    (writeEntries elems d n g).size = elems.size ∧
      ∀ j, (writeEntries elems d n g)[j]? = if d ≤ j ∧ j < d + n then some (g (j - d)) else elems[j]? := by
  induction n with
  | zero => simp [writeEntries]; intro j h1 h2; omega
  | succ n ih =>
    obtain ⟨hsz, hj⟩ := ih (by omega)
    have hstep : writeEntries elems d (n + 1) g = (writeEntries elems d n g).set! (d + n) (g n) := by
      simp [writeEntries, List.range_succ, List.foldl_append]
    rw [hstep]
    refine ⟨by simp [hsz], fun j => ?_⟩
    rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, hj]
    by_cases hjn : d + n = j
    · subst hjn
      simp [hsz]; omega
    · simp only [hjn, ite_false]
      by_cases h1 : d ≤ j ∧ j < d + n
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1]
        by_cases h2 : d ≤ j ∧ j < d + (n + 1)
        · omega
        · rw [ite_eq_right h2]

/-- Writing a run of entries replaces exactly their cells. -/
theorem replaces_writeEntries {σ : Store H} {a : Nat} {tab : TableInst}
    (htab : σ.tables[a]? = some tab) {d : Nat} {old : List Ref} (hb : d + old.length ≤ tab.elems.size)
    (g : Nat → Ref) :
    Replaces σ (Exec.setTable σ a { tab with elems := writeEntries tab.elems d old.length g })
      (entryCells a d old) (entryCells a d ((List.range old.length).map g)) := by
  obtain ⟨hsz, hj⟩ := writeEntries_spec tab.elems d old.length g hb
  have ha : a < σ.tables.size := (Array.getElem?_eq_some_iff.mp htab).1
  intro ⟨k, b, i⟩
  rw [lookup_setTable _ _ _ ha, lookup_entryCells, lookup_entryCells]
  simp only [List.length_map, List.length_range]
  by_cases hk : (k = 3 ∨ k = 4) ∧ b = a
  · rw [ite_eq_left hk]
    obtain ⟨hk, rfl⟩ := hk
    rw [lookup_table _ _ _ _ hk, htab, Option.bind_some]
    rcases hk with rfl | rfl
    · by_cases hi : d ≤ i ∧ i < d + old.length
      · have hidx : i - d < old.length := by omega
        simp only [hi, and_self, ite_true, tableCell, hj, Option.some_or]
        simp [List.getElem?_range hidx]
      · have hi' : ¬(d ≤ i ∧ i < d + old.length) := hi
        simp [tableCell, hj, hi']
    · rcases i with _ | i <;> simp [tableCell, hsz]
  · rw [ite_eq_right hk]
    have : ¬(k = 3 ∧ b = a ∧ d ≤ i ∧ i < d + old.length) := fun h => hk ⟨.inl h.1, h.2.1⟩
    simp [this]

theorem loc_of_mem_entryCells {t i : Nat} {rs : List Ref} {k b j : Nat} {c : Cell H}
    (hp : ((k, b, j), c) ∈ entryCells (H := H) t i rs) :
    k = 3 ∧ b = t ∧ i ≤ j ∧ j < i + rs.length := by
  have := lookup_entryCells (H := H) t i rs (k, b, j)
  rw [lookup_of_mem (entryCells_nodup _ _ _) hp] at this
  split at this
  · assumption
  · cases this

/-- Two runs of entries that do not overlap have distinct cells. -/
theorem entryCells_append_nodup {t t' i j : Nat} {rs rs' : List Ref}
    (h : t ≠ t' ∨ i + rs.length ≤ j ∨ j + rs'.length ≤ i) :
    ((entryCells (H := H) t i rs ++ entryCells (H := H) t' j rs').map (fun p : Loc × Cell H => p.1)).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨entryCells_nodup _ _ _, entryCells_nodup _ _ _, ?_⟩
  intro a ha b hb hab
  obtain ⟨⟨⟨k, c, x⟩, _⟩, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨⟨k', c', x'⟩, _⟩, hq, rfl⟩ := List.mem_map.mp hb
  have h1 := loc_of_mem_entryCells hp
  have h2 := loc_of_mem_entryCells hq
  simp only [Prod.mk.injEq] at hab
  omega

theorem lookup_setElem (σ : Store H) (a : Nat) (e : ElemInst) (ha : a < σ.elems.size) (k b i : Nat) :
    lookup { σ with elems := σ.elems.set! a e } (k, b, i) =
      if k = 7 ∧ b = a ∧ i = 0 then some (.elem e) else lookup σ (k, b, i) := by
  by_cases hk : k = 7
  · subst hk
    rcases i with _ | i
    · by_cases hb : b = a
      · subst hb; simp [lookup, Array.set!_eq_setIfInBounds, ha]
      · simp [lookup, Array.set!_eq_setIfInBounds, hb, Ne.symm hb]
    · simp [lookup]
  · rw [lookup_with_elems _ _ _ (by simpa using hk)]
    simp [hk]

theorem lookup_setData (σ : Store H) (a : Nat) (dt : DataInst) (ha : a < σ.datas.size) (k b i : Nat) :
    lookup { σ with datas := σ.datas.set! a dt } (k, b, i) =
      if k = 8 ∧ b = a ∧ i = 0 then some (.data dt) else lookup σ (k, b, i) := by
  by_cases hk : k = 8
  · subst hk
    rcases i with _ | i
    · by_cases hb : b = a
      · subst hb; simp [lookup, Array.set!_eq_setIfInBounds, ha]
      · simp [lookup, Array.set!_eq_setIfInBounds, hb, Ne.symm hb]
    · simp [lookup]
  · rw [lookup_with_datas _ _ _ (by simpa using hk)]
    simp [hk]

theorem loc_of_mem_byteCells {n i : Nat} {bs : List UInt8} {k b j : Nat} {c : Cell H}
    (hp : ((k, b, j), c) ∈ byteCells (H := H) n i bs) :
    k = 0 ∧ b = n ∧ i ≤ j ∧ j < i + bs.length := by
  have := lookup_byteCells (H := H) n i bs (k, b, j)
  rw [lookup_of_mem (byteCells_nodup _ _ _) hp] at this
  split at this
  · assumption
  · cases this

/-- Two runs of bytes that do not overlap have distinct cells. -/
theorem byteCells_append_nodup {n i j : Nat} {bs bs' : List UInt8}
    (h : i + bs.length ≤ j ∨ j + bs'.length ≤ i) :
    ((byteCells (H := H) n i bs ++ byteCells (H := H) n j bs').map (fun p : Loc × Cell H => p.1)).Nodup := by
  rw [List.map_append, List.nodup_append]
  refine ⟨byteCells_nodup _ _ _, byteCells_nodup _ _ _, ?_⟩
  intro a ha b hb hab
  obtain ⟨⟨⟨k, c, x⟩, _⟩, hp, rfl⟩ := List.mem_map.mp ha
  obtain ⟨⟨⟨k', c', x'⟩, _⟩, hq, rfl⟩ := List.mem_map.mp hb
  have h1 := loc_of_mem_byteCells hp
  have h2 := loc_of_mem_byteCells hq
  simp only [Prod.mk.injEq] at hab
  omega

/-- Cells that a step leaves alone can be added to both sides. -/
theorem replaces_append_same {σ σ' : Store H} {P Q R : List (Loc × Cell H)}
    (h : Replaces σ σ' P Q) (hR : ∀ p ∈ R, lookup σ' p.1 = some p.2) :
    Replaces σ σ' (P ++ R) (Q ++ R) := by
  intro l
  rw [List.lookup_append, List.lookup_append]
  cases hq : Q.lookup l with
  | some c =>
    have := h l
    rw [hq] at this
    simp only [Option.some_or] at this ⊢
    exact this
  | none =>
    cases hr : R.lookup l with
    | some c =>
      have hmem : (l, c) ∈ R := mem_of_lookup hr
      simp only [Option.none_or, Option.some_or]
      exact hR _ hmem
    | none =>
      have := h l
      rw [hq] at this
      simp only [Option.none_or] at this ⊢
      rw [this]
      cases P.lookup l <;> simp []

end Cells

section Rules

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]
variable {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value} {Φ : Post H GF}

theorem entry_fact {σ : Store H} {ta i : Nat} {r : Ref}
    (h : lookup σ (Loc.tableElem ta i) = some (.ref r)) :
    ∃ tab, σ.tables[ta]? = some tab ∧ tab.elems[i]? = some r := by
  simp only [lookup_tableElem, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
  obtain ⟨tab, htab, r', hr, he⟩ := h
  cases he
  exact ⟨tab, htab, hr⟩

theorem tableInfo_fact {σ : Store H} {ta size : Nat} {et : RefType} {mx : Option Nat}
    (h : lookup σ (Loc.tableInfo ta) = some (.tableInfo size et mx)) :
    ∃ tab, σ.tables[ta]? = some tab ∧ tab.elems.size = size ∧ tab.elemType = et ∧ tab.max = mx := by
  simp only [lookup_tableInfo, Option.map_eq_some_iff] at h
  obtain ⟨tab, htab, he⟩ := h
  cases he
  exact ⟨tab, htab, rfl, rfl, rfl⟩

/-- Owning one cell, as the generic rule wants it. -/
theorem single_cell (l : Loc) (c : Cell H) :
    ([∗list] p ∈ [(l, c)], p.1 ↦ₛ p.2) ⊣⊢ (l ↦ₛ c : IProp GF) :=
  BigSepL.bigSepL_singleton

/-- `table.get`: read an owned entry. -/
theorem wpi_table_get (t ta : Nat) (i : UInt32) (r : Ref) (hta : f.mi.tableAddrs[t]? = some ta) :
    ta ↦[wt][ i.toNat ] r ∗ ▷ (ta ↦[wt][ i.toNat ] r -∗ Φ.normal (vs ++ [.ref r]) f)
      ⊢ wpi lim d f (vs ++ [.i32 i]) [.table_get t] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 i])
    (.table_get t) (vs ++ [.ref r]) f.locals [] [(Loc.tableElem ta i.toNat, .ref r)]
    [(Loc.tableElem ta i.toNat, .ref r)] (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      obtain ⟨tab, htab, hr⟩ := entry_fact (hP _ List.mem_cons_self)
      refine ⟨σ, ?_, replaces_same hP⟩
      simp [Exec.instr, Exec.tableOf, Exec.i32, hta, htab, hr])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold tablePt
  iintro ⟨Hr, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hr]
  · iapply (single_cell _ _).2; iexact Hr
  · inext
    iintro HQ
    iapply HΦ
    iapply (single_cell _ _).1 $$ HQ

/-- `table.set`: overwrite an owned entry. -/
theorem wpi_table_set (t ta : Nat) (i : UInt32) (r r' : Ref) (hta : f.mi.tableAddrs[t]? = some ta) :
    ta ↦[wt][ i.toNat ] r ∗ ▷ (ta ↦[wt][ i.toNat ] r' -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 i, .ref r']) [.table_set t] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 i, .ref r'])
    (.table_set t) vs f.locals [] (entryCells ta i.toNat [r])
    (entryCells ta i.toNat ((List.range [r].length).map fun _ => r'))
    (entryCells_nodup _ _ _) (entryCells_nodup _ _ _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨tab, htab, hb, hk⟩ := entries_facts (List.cons_ne_nil r []) hP
      refine ⟨Exec.setTable σ ta { tab with elems := writeEntries tab.elems i.toNat [r].length fun _ => r' },
        ?_, replaces_writeEntries htab hb _⟩
      have hlt : i.toNat < tab.elems.size := by simp at hb; omega
      simp [Exec.instr, Exec.tableOf, Exec.i32, hta, htab, hlt, writeEntries])
    (by
      intro σ _ _ _ l hq hp
      rw [lookup_entryCells] at hq hp
      simp only [List.length_map, List.length_range] at hq
      split at hp
      · cases hp
      · rename_i hc; simp_all)
  simp only [Frame.withLocals_self, entryCells, List.length_singleton, List.range_one, List.map_cons,
    List.map_nil] at key
  unfold tablePt
  iintro ⟨Hr, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hr]
  · iapply (single_cell _ _).2; iexact Hr
  · inext
    iintro HQ
    iapply HΦ
    iapply (single_cell _ _).1 $$ HQ

/-- `table.size`: read the owned size. -/
theorem wpi_table_size (t ta size : Nat) (et : RefType) (mx : Option Nat)
    (hta : f.mi.tableAddrs[t]? = some ta) :
    tableInfoPt ta size et mx ∗ ▷ (tableInfoPt ta size et mx -∗ Φ.normal (vs ++ [.i32 (UInt32.ofNat size)]) f)
      ⊢ wpi lim d f vs [.table_size t] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs)
    (.table_size t) (vs ++ [.i32 (UInt32.ofNat size)]) f.locals [] [(Loc.tableInfo ta, .tableInfo size et mx)]
    [(Loc.tableInfo ta, .tableInfo size et mx)] (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      obtain ⟨tab, htab, hsz, -, -⟩ := tableInfo_fact (hP _ List.mem_cons_self)
      refine ⟨σ, ?_, replaces_same hP⟩
      simp [Exec.instr, Exec.tableOf, hta, htab, hsz])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold tableInfoPt
  iintro ⟨Hr, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hr]
  · iapply (single_cell _ _).2; iexact Hr
  · inext
    iintro HQ
    iapply HΦ
    iapply (single_cell _ _).1 $$ HQ

/-- When `table.grow` succeeds: the new size fits in an `i32` and in the
declared maximum. -/
def TableGrowOk (size : Nat) (mx : Option Nat) (n : Nat) : Prop :=
  size + n ≤ 2 ^ 32 - 1 ∧ ∀ m, mx = some m → size + n ≤ m

instance (size : Nat) (mx : Option Nat) (n : Nat) : Decidable (TableGrowOk size mx n) := by
  unfold TableGrowOk; cases mx <;> simp <;> infer_instance

theorem growCond_false {size n : Nat} {mx : Option Nat} (h : TableGrowOk size mx n) :
    (decide (size + n > 2 ^ 32 - 1) || mx.any (fun m => decide (size + n > m))) = false := by
  obtain ⟨h1, h2⟩ := h
  cases mx with
  | none => simp; omega
  | some m => have := h2 m rfl; simp; omega

theorem growCond_true {size n : Nat} {mx : Option Nat} (h : ¬TableGrowOk size mx n) :
    (decide (size + n > 2 ^ 32 - 1) || mx.any (fun m => decide (size + n > m))) = true := by
  unfold TableGrowOk at h
  cases mx with
  | none => simp at h ⊢; omega
  | some m => simp at h ⊢; omega

/-- `table.grow` when it succeeds: the size grows by `n` and the new entries
are owned, holding `r`. -/
theorem wpi_table_grow (t ta size : Nat) (et : RefType) (mx : Option Nat) (r : Ref) (n : UInt32)
    (hta : f.mi.tableAddrs[t]? = some ta) (hok : TableGrowOk size mx n.toNat) :
    tableInfoPt ta size et mx ∗
      ▷ (tableInfoPt ta (size + n.toNat) et mx ∗ ta ↦[wts][ size ] List.replicate n.toNat r -∗
        Φ.normal (vs ++ [.i32 (UInt32.ofNat size)]) f)
      ⊢ wpi lim d f (vs ++ [.ref r, .i32 n]) [.table_grow t] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.ref r, .i32 n])
    (.table_grow t) (vs ++ [.i32 (UInt32.ofNat size)]) f.locals []
    [(Loc.tableInfo ta, .tableInfo size et mx)]
    ((Loc.tableInfo ta, .tableInfo (size + n.toNat) et mx) :: entryCells ta size (List.replicate n.toNat r))
    (by simp) (by
      simp only [List.map_cons, List.nodup_cons]
      refine ⟨fun hmem => ?_, entryCells_nodup _ _ _⟩
      obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hmem
      have := lookup_entryCells (H := H) ta size (List.replicate n.toNat r) p.1
      rw [lookup_of_mem (entryCells_nodup _ _ _) hp] at this
      split at this
      · rename_i h; rw [hp1] at h; simp at h
      · cases this)
    (by
      intro σ _ _ hP base L R
      obtain ⟨tab, htab, hsz, het, hmx⟩ := tableInfo_fact (hP _ List.mem_cons_self)
      have ha : ta < σ.tables.size := (Array.getElem?_eq_some_iff.mp htab).1
      refine ⟨Exec.setTable σ ta { tab with elems := tab.elems ++ Array.replicate n.toNat r }, ?_, ?_⟩
      · have hc := growCond_false (hsz ▸ hmx ▸ hok)
        simp [Exec.instr, Exec.tableOf, Exec.i32, hta, htab, hsz] at hc ⊢
        simp [hc]
        intro h; omega
      · intro ⟨k, b, i⟩
        rw [lookup_setTable _ _ _ ha, lookup_cons_pair, lookup_entryCells, lookup_cons_pair]
        simp only [Loc.tableInfo, Prod.mk.injEq, List.lookup_nil, List.length_replicate]
        by_cases hk : (k = 3 ∨ k = 4) ∧ b = ta
        · rw [ite_eq_left hk]
          obtain ⟨hk, rfl⟩ := hk
          rcases hk with rfl | rfl
          · have hl : lookup σ (3, b, i) = tab.elems[i]?.map .ref := by
              rw [lookup_table _ _ _ _ (.inl rfl), htab]; rfl
            rw [hl]
            simp only [tableCell, Array.getElem?_append, Array.getElem?_replicate, hsz]
            by_cases h1 : i < size
            · have h2 : ¬(size ≤ i ∧ i < size + n.toNat) := by omega
              simp [h1, h2]
            · have hge : tab.elems[i]? = none := by
                rw [Array.getElem?_eq_none_iff, hsz]; omega
              by_cases h2 : i < size + n.toNat
              · have h3 : size ≤ i ∧ i < size + n.toNat := ⟨by omega, h2⟩
                simp [h1, h3, show i - size < n.toNat by omega]
              · have h3 : ¬(size ≤ i ∧ i < size + n.toNat) := by omega
                simp [h1, h3, show ¬(i - size < n.toNat) by omega, hge]
          · rcases i with _ | i
            · simp [tableCell, hsz, het, hmx]
            · simp only [tableCell]
              rw [lookup_table _ _ _ _ (.inr rfl), htab]
              simp [tableCell]
        · rw [ite_eq_right hk]
          have h1 : ¬(k = 4 ∧ b = ta ∧ i = 0) := fun h => hk ⟨.inr h.1, h.2.1⟩
          have h2 : ¬(k = 3 ∧ b = ta ∧ size ≤ i ∧ i < size + n.toNat) := fun h => hk ⟨.inl h.1, h.2.1⟩
          simp [h1, h2])
    (by
      intro σ _ _ hP l hq hp
      obtain ⟨tab, htab, hsz, -, -⟩ := tableInfo_fact (hP _ List.mem_cons_self)
      obtain ⟨k, b, i⟩ := l
      rw [lookup_cons_pair, lookup_entryCells] at hq
      rw [lookup_cons_pair] at hp
      simp only [Loc.tableInfo, Prod.mk.injEq, List.length_replicate] at hq hp
      split at hq
      · simp_all
      · split at hq
        · rename_i h
          obtain ⟨rfl, rfl, h1, -⟩ := h
          simp [htab, hsz, show ¬i < size by omega]
        · cases hq)
  simp only [Frame.withLocals_self] at key
  unfold tableInfoPt tableEntries
  iintro ⟨Hr, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hr]
  · iapply (single_cell _ _).2; iexact Hr
  · inext
    iintro HQ
    iapply HΦ
    iapply BigSepL.bigSepL_cons.1 $$ HQ

/-- `table.grow` when it fails: -1, and nothing changes. -/
theorem wpi_table_grow_fail (t ta size : Nat) (et : RefType) (mx : Option Nat) (r : Ref) (n : UInt32)
    (hta : f.mi.tableAddrs[t]? = some ta) (hfail : ¬TableGrowOk size mx n.toNat) :
    tableInfoPt ta size et mx ∗ ▷ (tableInfoPt ta size et mx -∗ Φ.normal (vs ++ [.i32 0xFFFFFFFF]) f)
      ⊢ wpi lim d f (vs ++ [.ref r, .i32 n]) [.table_grow t] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.ref r, .i32 n])
    (.table_grow t) (vs ++ [.i32 0xFFFFFFFF]) f.locals [] [(Loc.tableInfo ta, .tableInfo size et mx)]
    [(Loc.tableInfo ta, .tableInfo size et mx)] (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      obtain ⟨tab, htab, hsz, het, hmx⟩ := tableInfo_fact (hP _ List.mem_cons_self)
      refine ⟨σ, ?_, replaces_same hP⟩
      have hc := growCond_true (hsz ▸ hmx ▸ hfail)
      simp [Exec.instr, Exec.tableOf, Exec.i32, hta, htab, hsz] at hc ⊢
      intro h1 h2
      rcases hc with hc | hc
      · omega
      · rw [h2] at hc; cases hc)
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold tableInfoPt
  iintro ⟨Hr, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hr]
  · iapply (single_cell _ _).2; iexact Hr
  · inext
    iintro HQ
    iapply HΦ
    iapply (single_cell _ _).1 $$ HQ

/-- `table.fill` over a non-empty run of owned entries. -/
theorem wpi_table_fill (t ta : Nat) (i n : UInt32) (r : Ref) (old : List Ref)
    (hta : f.mi.tableAddrs[t]? = some ta) (hlen : old.length = n.toNat) (hne : old ≠ []) :
    ta ↦[wts][ i.toNat ] old ∗ ▷ (ta ↦[wts][ i.toNat ] List.replicate old.length r -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 i, .ref r, .i32 n]) [.table_fill t] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 i, .ref r, .i32 n])
    (.table_fill t) vs f.locals [] (entryCells ta i.toNat old)
    (entryCells ta i.toNat ((List.range old.length).map fun _ => r))
    (entryCells_nodup _ _ _) (entryCells_nodup _ _ _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨tab, htab, hb, -⟩ := entries_facts hne hP
      refine ⟨Exec.setTable σ ta { tab with elems := writeEntries tab.elems i.toNat old.length fun _ => r },
        ?_, replaces_writeEntries htab hb _⟩
      have hle : ¬(i.toNat + n.toNat > tab.elems.size) := by omega
      simp [Exec.instr, Exec.tableOf, Exec.i32, hta, htab, hle, writeEntries, hlen])
    (by
      intro σ _ _ _ l hq hp
      rw [lookup_entryCells] at hq hp
      simp only [List.length_map, List.length_range] at hq
      split at hp
      · cases hp
      · rename_i hc; simp_all)
  simp only [Frame.withLocals_self] at key
  rw [show (List.range old.length).map (fun _ => r) = List.replicate old.length r by
    rw [List.map_const', List.length_range]] at key
  unfold tableEntries
  iintro ⟨Hr, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hr]
  · iexact Hr
  · iexact HΦ

theorem elem_fact {σ : Store H} {a : Nat} {seg : ElemInst}
    (h : lookup σ (Loc.elem a) = some (.elem seg)) : σ.elems[a]? = some seg := by
  simp only [lookup_elem, Option.map_eq_some_iff] at h
  obtain ⟨e, he, hc⟩ := h
  cases hc; exact he

/-- `table.copy` between non-overlapping runs of owned entries. -/
theorem wpi_table_copy (x y ta tb : Nat) (dI sI n : UInt32) (old src : List Ref)
    (hta : f.mi.tableAddrs[x]? = some ta) (htb : f.mi.tableAddrs[y]? = some tb)
    (hlen : old.length = n.toNat) (hlen' : src.length = n.toNat) (hne : old ≠ [])
    (hdisj : ta ≠ tb ∨ dI.toNat + n.toNat ≤ sI.toNat ∨ sI.toNat + n.toNat ≤ dI.toNat) :
    ta ↦[wts][ dI.toNat ] old ∗ tb ↦[wts][ sI.toNat ] src ∗
      ▷ (ta ↦[wts][ dI.toNat ] src ∗ tb ↦[wts][ sI.toNat ] src -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 dI, .i32 sI, .i32 n]) [.table_copy x y] Φ := by
  have hne' : src ≠ [] := by
    intro h; subst h; simp at hlen'; exact hne (List.eq_nil_of_length_eq_zero (by omega))
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 dI, .i32 sI, .i32 n])
    (.table_copy x y) vs f.locals [] (entryCells ta dI.toNat old ++ entryCells tb sI.toNat src)
    (entryCells ta dI.toNat src ++ entryCells tb sI.toNat src)
    (entryCells_append_nodup (by rw [hlen, hlen']; exact hdisj))
    (entryCells_append_nodup (by rw [hlen']; exact hdisj))
    (by
      intro σ _ _ hP base L R
      obtain ⟨dtab, hdt, hdb, -⟩ := entries_facts hne fun p hp => hP p (List.mem_append_left _ hp)
      obtain ⟨stab, hst, hsb, hsk⟩ := entries_facts hne' fun p hp => hP p (List.mem_append_right _ hp)
      let g : Nat → Ref := fun k => ((List.range n.toNat).map fun k => stab.elems[sI.toNat + k]!)[k]!
      have hg : (List.range old.length).map g = src := by
        apply List.ext_getElem (by simp [hlen, hlen'])
        intro k h1 h2
        have hk : k < n.toNat := by simp at h1; omega
        have hs := hsk k (by omega)
        simp only [List.getElem_map, List.getElem_range, g, List.getElem!_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
        rw [getElem!_def, hs, List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2]
        rfl
      have hrep := replaces_writeEntries hdt hdb g
      rw [hg] at hrep
      refine ⟨_, ?_, replaces_append_same hrep ?_⟩
      · have hc : ¬(dI.toNat + n.toNat > dtab.elems.size || sI.toNat + n.toNat > stab.elems.size) := by
          simp; omega
        simp only [Bool.not_eq_true] at hc
        simp [Exec.instr, Exec.tableOf, Exec.i32, hta, htb, hdt, hst, hc, writeEntries, hlen, g]
      · intro p hp
        have hpσ := hP p (List.mem_append_right _ hp)
        obtain ⟨⟨k, b, i⟩, c⟩ := p
        have hpl := loc_of_mem_entryCells hp
        simp only at hpσ ⊢
        obtain ⟨rfl, rfl, hi1, hi2⟩ := hpl
        have ha : ta < σ.tables.size := (Array.getElem?_eq_some_iff.mp hdt).1
        rw [lookup_setTable _ _ _ ha]
        by_cases hb : b = ta
        · subst hb
          rw [hdt] at hst; cases hst
          rw [ite_eq_left ⟨.inl rfl, rfl⟩]
          obtain ⟨-, hj⟩ := writeEntries_spec dtab.elems dI.toNat old.length g hdb
          simp only [tableCell, hj]
          rw [ite_eq_right (by omega)]
          rw [lookup_table _ _ _ _ (.inl rfl), hdt] at hpσ
          exact hpσ
        · rw [ite_eq_right (by omega)]
          exact hpσ)
    (by
      intro σ _ _ _ l hq hp
      rw [List.lookup_append, lookup_entryCells, lookup_entryCells] at hq
      rw [List.lookup_append, lookup_entryCells, lookup_entryCells] at hp
      simp only [hlen, hlen'] at hq hp
      split at hq <;> split at hp <;> simp_all)
  simp only [Frame.withLocals_self] at key
  unfold tableEntries
  iintro ⟨Ho, Hs, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Ho Hs]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Ho]
    · iexact Ho
    · iexact Hs
  · inext
    iintro HQ
    iapply HΦ
    iapply BigSepL.bigSepL_append.1 $$ HQ

/-- `table.init`: copy a non-empty run of an element segment into owned
entries. -/
theorem wpi_table_init (x e ta a : Nat) (dI sI n : UInt32) (seg : ElemInst) (old : List Ref)
    (hta : f.mi.tableAddrs[x]? = some ta) (ha : f.mi.elemAddrs[e]? = some a)
    (hlen : old.length = n.toNat) (hne : old ≠ []) (hseg : sI.toNat + n.toNat ≤ seg.elems.size) :
    ta ↦[wts][ dI.toNat ] old ∗ a ↦[welem] seg ∗
      ▷ (ta ↦[wts][ dI.toNat ] ((List.range old.length).map fun k => seg.elems[sI.toNat + k]!) ∗
          a ↦[welem] seg -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 dI, .i32 sI, .i32 n]) [.table_init x e] Φ := by
  have hnd : ∀ rs : List Ref, ((entryCells (H := H) ta dI.toNat rs ++ [(Loc.elem a, (Cell.elem seg : Cell H))]).map
      (fun p : Loc × Cell H => p.1)).Nodup := by
    intro rs
    rw [List.map_append, List.nodup_append]
    refine ⟨entryCells_nodup _ _ _, by simp, ?_⟩
    intro l hl l' hl' hll
    obtain ⟨⟨⟨k, b, j⟩, _⟩, hp, rfl⟩ := List.mem_map.mp hl
    have := loc_of_mem_entryCells hp
    simp at hl'
    subst hl'
    simp only [Loc.elem, Prod.mk.injEq] at hll
    omega
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 dI, .i32 sI, .i32 n])
    (.table_init x e) vs f.locals [] (entryCells ta dI.toNat old ++ [(Loc.elem a, .elem seg)])
    (entryCells ta dI.toNat ((List.range old.length).map fun k => seg.elems[sI.toNat + k]!) ++
      [(Loc.elem a, .elem seg)]) (hnd _) (hnd _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨tab, htab, hb, -⟩ := entries_facts hne fun p hp => hP p (List.mem_append_left _ hp)
      have hseg' := elem_fact (hP _ (List.mem_append_right _ List.mem_cons_self))
      have hrep := replaces_writeEntries htab hb fun k => seg.elems[sI.toNat + k]!
      refine ⟨_, ?_, replaces_append_same hrep ?_⟩
      · have hc : ¬(dI.toNat + n.toNat > tab.elems.size || sI.toNat + n.toNat > seg.elems.size) := by
          simp; omega
        simp only [Bool.not_eq_true] at hc
        simp [Exec.instr, Exec.tableOf, Exec.i32, hta, ha, htab, hseg', hc, writeEntries, hlen]
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        have ha' : ta < σ.tables.size := (Array.getElem?_eq_some_iff.mp htab).1
        simp only [Loc.elem]
        rw [lookup_setTable _ _ _ ha', ite_eq_right (by omega)]
        exact hP _ (List.mem_append_right _ List.mem_cons_self))
    (by
      intro σ _ _ _ l hq hp
      rw [List.lookup_append, lookup_entryCells, lookup_cons_pair] at hq
      rw [List.lookup_append, lookup_entryCells, lookup_cons_pair] at hp
      simp only [List.length_map, List.length_range] at hq
      split at hq <;> split at hp <;> simp_all)
  simp only [Frame.withLocals_self] at key
  unfold tableEntries elemPt
  iintro ⟨Ho, Hs, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Ho Hs]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Ho]
    · iexact Ho
    · iapply (single_cell _ _).2; iexact Hs
  · inext
    iintro HQ
    iapply HΦ
    icases BigSepL.bigSepL_append.1 $$ HQ with ⟨HQ, Hs⟩
    isplitl [HQ]
    · iexact HQ
    · iapply (single_cell _ _).1 $$ Hs

/-- `elem.drop`: the segment becomes empty. -/
theorem wpi_elem_drop (e a : Nat) (seg : ElemInst) (ha : f.mi.elemAddrs[e]? = some a) :
    a ↦[welem] seg ∗ ▷ (a ↦[welem] { elems := #[] } -∗ Φ.normal vs f)
      ⊢ wpi lim d f vs [.elem_drop e] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs)
    (.elem_drop e) vs f.locals [] [(Loc.elem a, .elem seg)] [(Loc.elem a, .elem { elems := #[] })]
    (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      have hseg := elem_fact (hP _ List.mem_cons_self)
      have hlt : a < σ.elems.size := (Array.getElem?_eq_some_iff.mp hseg).1
      refine ⟨{ σ with elems := σ.elems.set! a { elems := #[] } }, ?_, ?_⟩
      · simp [Exec.instr, getElem!_def, ha]
      · intro ⟨k, b, i⟩
        rw [lookup_setElem _ _ _ hlt, lookup_cons_pair, lookup_cons_pair]
        simp only [Loc.elem, Prod.mk.injEq, List.lookup_nil]
        by_cases h : k = 7 ∧ b = a ∧ i = 0
        · obtain ⟨rfl, rfl, rfl⟩ := h; simp
        · simp [h])
    (by intro σ _ _ _ l hq hp; rw [lookup_cons_pair] at hq hp; split at hq <;> simp_all)
  simp only [Frame.withLocals_self] at key
  unfold elemPt
  iintro ⟨Hs, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hs]
  · iapply (single_cell _ _).2; iexact Hs
  · inext
    iintro HQ
    iapply HΦ
    iapply (single_cell _ _).1 $$ HQ

theorem data_fact {σ : Store H} {a : Nat} {dt : DataInst}
    (h : lookup σ (Loc.data a) = some (.data dt)) : σ.datas[a]? = some dt := by
  simp only [lookup_data, Option.map_eq_some_iff] at h
  obtain ⟨e, he, hc⟩ := h
  cases hc; exact he

/-- `memory.fill` over a non-empty run of owned bytes. -/
theorem wpi_memory_fill (n : Nat) (dI v cnt : UInt32) (old : List UInt8)
    (hn : f.mi.memAddrs[0]? = some n) (hlen : old.length = cnt.toNat) (hne : old ≠ []) :
    n ↦[wms][ dI.toNat ] old ∗
      ▷ (n ↦[wms][ dI.toNat ] List.replicate old.length (UInt8.ofNat v.toNat) -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 dI, .i32 v, .i32 cnt]) [.memory_fill] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 dI, .i32 v, .i32 cnt])
    .memory_fill vs f.locals [] (byteCells n dI.toNat old)
    (byteCells n dI.toNat ((List.range old.length).map fun _ => UInt8.ofNat v.toNat))
    (byteCells_nodup _ _ _) (byteCells_nodup _ _ _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, hwf, hb, _⟩ := bytes_facts hne hP
      refine ⟨_, ?_, replaces_write hmem hwf hb fun _ => UInt8.ofNat v.toNat⟩
      have hb' : dI.toNat + cnt.toNat ≤ mem.byteSize := by omega
      simp [Exec.instr, Exec.evalMemOp, Exec.i32, memOf_eq hn hmem, Memory.fill, Memory.inBounds, hb',
        Store.setMemOf, hn, Memory.writeRun, hlen])
    (by
      intro σ _ _ _ l hq hp
      rw [lookup_byteCells] at hq hp
      simp only [List.length_map, List.length_range] at hq
      split at hp
      · cases hp
      · rename_i hc; simp_all)
  simp only [Frame.withLocals_self] at key
  rw [show (List.range old.length).map (fun _ => UInt8.ofNat v.toNat) =
    List.replicate old.length (UInt8.ofNat v.toNat) by rw [List.map_const', List.length_range]] at key
  unfold memBytes
  iintro ⟨Hb, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hb]
  · iexact Hb
  · iexact HΦ

/-- `memory.copy` between non-overlapping runs of owned bytes. -/
theorem wpi_memory_copy (n : Nat) (dI sI cnt : UInt32) (old src : List UInt8)
    (hn : f.mi.memAddrs[0]? = some n) (hlen : old.length = cnt.toNat) (hlen' : src.length = cnt.toNat)
    (hne : old ≠ []) (hdisj : dI.toNat + cnt.toNat ≤ sI.toNat ∨ sI.toNat + cnt.toNat ≤ dI.toNat) :
    n ↦[wms][ dI.toNat ] old ∗ n ↦[wms][ sI.toNat ] src ∗
      ▷ (n ↦[wms][ dI.toNat ] src ∗ n ↦[wms][ sI.toNat ] src -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 dI, .i32 sI, .i32 cnt]) [.memory_copy] Φ := by
  have hne' : src ≠ [] := by
    intro h; subst h; simp at hlen'; exact hne (List.eq_nil_of_length_eq_zero (by omega))
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 dI, .i32 sI, .i32 cnt])
    .memory_copy vs f.locals [] (byteCells n dI.toNat old ++ byteCells n sI.toNat src)
    (byteCells n dI.toNat src ++ byteCells n sI.toNat src)
    (byteCells_append_nodup (by rw [hlen, hlen']; exact hdisj))
    (byteCells_append_nodup (by rw [hlen']; exact hdisj))
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, hwf, hb, -⟩ := bytes_facts hne fun p hp => hP p (List.mem_append_left _ hp)
      obtain ⟨mem', hmem', -, hsb, hsk⟩ := bytes_facts hne' fun p hp => hP p (List.mem_append_right _ hp)
      rw [hmem] at hmem'; cases hmem'
      let g : Nat → UInt8 := fun i => ((List.range cnt.toNat).map fun i => mem.read8 (sI.toNat + i))[i]!
      have hg : (List.range old.length).map g = src := by
        apply List.ext_getElem (by simp [hlen, hlen'])
        intro k h1 h2
        have hk : k < cnt.toNat := by simp at h1; omega
        simp only [List.getElem_map, List.getElem_range, g, List.getElem!_eq_getElem?_getD,
          List.getElem?_map, List.getElem?_range hk, Option.map_some, Option.getD_some]
        rw [hsk k (by omega), List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h2]
        rfl
      have hrep := replaces_write hmem hwf hb g
      rw [hg] at hrep
      obtain ⟨hwf', hsz', -, hrd'⟩ := Memory.writeRun_spec hwf hb g
      refine ⟨_, ?_, replaces_append_same hrep ?_⟩
      · have hb1 : dI.toNat + cnt.toNat ≤ mem.byteSize := by omega
        have hb2 : sI.toNat + cnt.toNat ≤ mem.byteSize := by omega
        simp [Exec.instr, Exec.evalMemOp, Exec.i32, memOf_eq hn hmem, Memory.copy, Memory.inBounds, hb1, hb2,
          Store.setMemOf, hn, Memory.writeRun, hlen, g]
      · intro p hp
        have hpσ := hP p (List.mem_append_right _ hp)
        obtain ⟨⟨k, b, i⟩, c⟩ := p
        have hpl := loc_of_mem_byteCells hp
        obtain ⟨rfl, hbn, hi1, hi2⟩ := hpl
        subst b
        have hnlt : n < σ.mems.size := (Array.getElem?_eq_some_iff.mp hmem).1
        simp only at hpσ ⊢
        rw [lookup_setMem _ _ _ hnlt, ite_eq_left ⟨.inl rfl, rfl⟩]
        rw [lookup_mem _ _ _ _ (.inl rfl), hmem, Option.bind_some] at hpσ
        have hread : (mem.writeRun dI.toNat old.length g).read8 i = mem.read8 i := by
          rw [hrd', ite_eq_right (by omega)]
        simp only [memCell, hwf', hsz', hread, hwf] at hpσ ⊢
        exact hpσ)
    (by
      intro σ _ _ _ l hq hp
      rw [List.lookup_append, lookup_byteCells, lookup_byteCells] at hq
      rw [List.lookup_append, lookup_byteCells, lookup_byteCells] at hp
      simp only [hlen, hlen'] at hq hp
      split at hq <;> split at hp <;> simp_all)
  simp only [Frame.withLocals_self] at key
  unfold memBytes
  iintro ⟨Ho, Hs, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Ho Hs]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Ho]
    · iexact Ho
    · iexact Hs
  · inext
    iintro HQ
    iapply HΦ
    iapply BigSepL.bigSepL_append.1 $$ HQ

/-- `memory.init`: copy a non-empty run of a data segment into owned bytes. -/
theorem wpi_memory_init (x a n : Nat) (dI sI cnt : UInt32) (seg : DataInst) (old : List UInt8)
    (hn : f.mi.memAddrs[0]? = some n) (ha : f.mi.dataAddrs[x]? = some a)
    (hlen : old.length = cnt.toNat) (hne : old ≠ []) (hseg : sI.toNat + cnt.toNat ≤ seg.bytes.size) :
    n ↦[wms][ dI.toNat ] old ∗ a ↦[wdata] seg ∗
      ▷ (n ↦[wms][ dI.toNat ] ((List.range old.length).map fun k => seg.bytes[sI.toNat + k]!) ∗
          a ↦[wdata] seg -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 dI, .i32 sI, .i32 cnt]) [.memory_init x] Φ := by
  have hnd : ∀ bs : List UInt8, ((byteCells (H := H) n dI.toNat bs ++ [(Loc.data a, (Cell.data seg : Cell H))]).map
      (fun p : Loc × Cell H => p.1)).Nodup := by
    intro bs
    rw [List.map_append, List.nodup_append]
    refine ⟨byteCells_nodup _ _ _, by simp, ?_⟩
    intro l hl l' hl' hll
    obtain ⟨⟨⟨k, b, j⟩, _⟩, hp, rfl⟩ := List.mem_map.mp hl
    have := loc_of_mem_byteCells hp
    simp at hl'
    subst hl'
    simp only [Loc.data, Prod.mk.injEq] at hll
    omega
  let bytes := seg.bytes.extract sI.toNat (sI.toNat + cnt.toNat)
  have hsize : bytes.size = cnt.toNat := by
    simp only [bytes, ByteArray.size_extract]; omega
  let g : Nat → UInt8 := fun i => bytes[i]!
  have hg : (List.range old.length).map g = (List.range old.length).map fun k => seg.bytes[sI.toNat + k]! := by
    apply List.map_congr_left
    intro k hk
    simp only [List.mem_range] at hk
    have h1 : k < bytes.size := by omega
    have h2 : sI.toNat + k < seg.bytes.size := by omega
    simp only [g]
    rw [getElem!_pos bytes k h1, getElem!_pos seg.bytes (sI.toNat + k) h2]
    exact ByteArray.getElem_extract h1
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 dI, .i32 sI, .i32 cnt])
    (.memory_init x) vs f.locals [] (byteCells n dI.toNat old ++ [(Loc.data a, .data seg)])
    (byteCells n dI.toNat ((List.range old.length).map g) ++ [(Loc.data a, .data seg)]) (hnd _) (hnd _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, hwf, hb, -⟩ := bytes_facts hne fun p hp => hP p (List.mem_append_left _ hp)
      have hseg' := data_fact (hP _ (List.mem_append_right _ List.mem_cons_self))
      refine ⟨_, ?_, replaces_append_same (replaces_write hmem hwf hb g) ?_⟩
      · have hc : ¬(sI.toNat + cnt.toNat > seg.bytes.size) := by omega
        have hb' : dI.toNat + bytes.size ≤ mem.byteSize := by omega
        have hb'' : dI.toNat + cnt.toNat ≤ mem.byteSize := by omega
        simp only [bytes] at hsize
        simp [Exec.instr, Exec.evalMemOp, Exec.i32, ha, hseg', hc, memOf_eq hn hmem, Memory.writeBytes,
          Memory.inBounds, hb'', Store.setMemOf, hn, Memory.writeRun, hsize, hlen, g, bytes]
      · intro p hp
        simp only [List.mem_singleton] at hp
        subst hp
        have hnlt : n < σ.mems.size := (Array.getElem?_eq_some_iff.mp hmem).1
        simp only [Loc.data]
        rw [lookup_setMem _ _ _ hnlt, ite_eq_right (by omega)]
        exact hP _ (List.mem_append_right _ List.mem_cons_self))
    (by
      intro σ _ _ _ l hq hp
      rw [List.lookup_append, lookup_byteCells, lookup_cons_pair] at hq
      rw [List.lookup_append, lookup_byteCells, lookup_cons_pair] at hp
      simp only [List.length_map, List.length_range] at hq
      split at hq <;> split at hp <;> simp_all)
  simp only [Frame.withLocals_self] at key
  rw [hg] at key
  unfold memBytes dataPt
  iintro ⟨Ho, Hs, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Ho Hs]
  · iapply BigSepL.bigSepL_append.2
    isplitl [Ho]
    · iexact Ho
    · iapply (single_cell _ _).2; iexact Hs
  · inext
    iintro HQ
    iapply HΦ
    icases BigSepL.bigSepL_append.1 $$ HQ with ⟨HQ, Hs⟩
    isplitl [HQ]
    · iexact HQ
    · iapply (single_cell _ _).1 $$ Hs

/-- `data.drop`: the segment becomes empty. -/
theorem wpi_data_drop (x a : Nat) (seg : DataInst) (ha : f.mi.dataAddrs[x]? = some a) :
    a ↦[wdata] seg ∗ ▷ (a ↦[wdata] { bytes := ByteArray.empty } -∗ Φ.normal vs f)
      ⊢ wpi lim d f vs [.data_drop x] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs)
    (.data_drop x) vs f.locals [] [(Loc.data a, .data seg)] [(Loc.data a, .data { bytes := ByteArray.empty })]
    (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      have hseg := data_fact (hP _ List.mem_cons_self)
      have hlt : a < σ.datas.size := (Array.getElem?_eq_some_iff.mp hseg).1
      refine ⟨{ σ with datas := σ.datas.set! a { bytes := ByteArray.empty } }, ?_, ?_⟩
      · simp [Exec.instr, getElem!_def, ha]
      · intro ⟨k, b, i⟩
        rw [lookup_setData _ _ _ hlt, lookup_cons_pair, lookup_cons_pair]
        simp only [Loc.data, Prod.mk.injEq, List.lookup_nil]
        by_cases h : k = 8 ∧ b = a ∧ i = 0
        · obtain ⟨rfl, rfl, rfl⟩ := h; simp
        · simp [h])
    (by intro σ _ _ _ l hq hp; rw [lookup_cons_pair] at hq hp; split at hq <;> simp_all)
  simp only [Frame.withLocals_self] at key
  unfold dataPt
  iintro ⟨Hs, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hs]
  · iapply (single_cell _ _).2; iexact Hs
  · inext
    iintro HQ
    iapply HΦ
    iapply (single_cell _ _).1 $$ HQ

end Rules

end WasmLogic
