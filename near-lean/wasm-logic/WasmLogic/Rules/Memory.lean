import WasmLogic.Rules.Pure

/-!
# Rules for memory and globals

Loads and stores own the bytes they touch (`↦[wms]`), `memory.size` and
`memory.grow` own the memory's length (`↦[wmlength]`) and see its limit
(`↪[wmlimit]`), globals own their cell (`↦[wg]`). As in Iris-Wasm the
memory is the frame's first one, `f.mi.memAddrs[0]`.
-/

namespace WasmLogic

open Wasm Iris Iris.BI Iris.ProgramLogic

/-! ## Byte cells -/

section Cells

variable {H : Type}

@[simp] theorem byteCells_length (n i : Nat) (bs : List UInt8) :
    (byteCells (H := H) n i bs).length = bs.length := by
  induction bs generalizing i <;> simp_all [byteCells]

theorem lookup_byteCells (n i : Nat) (bs : List UInt8) (l : Loc) :
    (byteCells (H := H) n i bs).lookup l =
      if l.1 = 0 ∧ l.2.1 = n ∧ i ≤ l.2.2 ∧ l.2.2 < i + bs.length then
        some (.byte bs[l.2.2 - i]!) else none := by
  induction bs generalizing i with
  | nil =>
    simp only [byteCells, List.length_nil, Nat.add_zero]
    split
    · omega
    · rfl
  | cons b bs ih =>
    obtain ⟨k, a, j⟩ := l
    rw [byteCells, lookup_cons_pair, ih]
    simp only [Loc.byte, Prod.mk.injEq, List.length_cons]
    by_cases hj : k = 0 ∧ a = n ∧ j = i
    · obtain ⟨rfl, rfl, rfl⟩ := hj
      simp
    · rw [ite_eq_right hj]
      by_cases hr : k = 0 ∧ a = n ∧ i + 1 ≤ j ∧ j < i + 1 + bs.length
      · have h1 : j - i = (j - (i + 1)) + 1 := by omega
        rw [ite_eq_left hr, ite_eq_left (by omega), h1]
        simp
      · rw [ite_eq_right hr, ite_eq_right (by omega)]

theorem byteCells_nodup (n i : Nat) (bs : List UInt8) :
    ((byteCells (H := H) n i bs).map (·.1)).Nodup := by
  induction bs generalizing i with
  | nil => simp [byteCells]
  | cons b bs ih =>
    simp only [byteCells, List.map_cons, List.nodup_cons]
    refine ⟨fun hmem => ?_, ih (i + 1)⟩
    obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hmem
    have := lookup_byteCells (H := H) n (i + 1) bs p.1
    rw [lookup_of_mem (ih (i + 1)) hp] at this
    split at this
    · rename_i h
      simp only [Loc.byte] at hp1
      rw [hp1] at h
      simp only at h
      omega
    · cases this

theorem mem_byteCells (n i : Nat) (bs : List UInt8) {k : Nat} (hk : k < bs.length) :
    (Loc.byte n (i + k), (Cell.byte bs[k]! : Cell H)) ∈ byteCells (H := H) n i bs := by
  induction bs generalizing i k with
  | nil => cases hk
  | cons b bs ih =>
    cases k with
    | zero => simp [byteCells]
    | succ k =>
      simp only [byteCells, List.mem_cons]
      right
      have := ih (i + 1) (k := k) (by simpa using hk)
      simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- What owning bytes says about the store. -/
theorem bytes_facts {σ : Store H} {n i : Nat} {bs : List UInt8} (hne : bs ≠ [])
    (h : ∀ p ∈ byteCells (H := H) n i bs, lookup σ p.1 = some p.2) :
    ∃ mem, σ.mems[n]? = some mem ∧ mem.wf ∧ i + bs.length ≤ mem.byteSize ∧
      ∀ k, k < bs.length → mem.read8 (i + k) = bs[k]! := by
  have hlen : 0 < bs.length := List.length_pos_iff.mpr hne
  have h0 := h _ (mem_byteCells n i bs hlen)
  simp only [lookup_byte, Option.bind_eq_some_iff] at h0
  obtain ⟨mem, hmem, h0⟩ := h0
  refine ⟨mem, hmem, ?_, ?_, ?_⟩
  · split at h0
    · rename_i hw; exact hw.1
    · cases h0
  · have hl := h _ (mem_byteCells n i bs (k := bs.length - 1) (by omega))
    simp only [lookup_byte, hmem, Option.bind_some] at hl
    split at hl
    · rename_i hw; omega
    · cases hl
  · intro k hk
    have hl := h _ (mem_byteCells n i bs hk)
    simp only [lookup_byte, hmem, Option.bind_some] at hl
    split at hl
    · simpa using hl
    · cases hl

/-- A step that leaves the store alone keeps every owned cell. -/
theorem replaces_same {σ : Store H} {P : List (Loc × Cell H)}
    (h : ∀ p ∈ P, lookup σ p.1 = some p.2) : Replaces σ σ P P := by
  intro l
  cases hl : P.lookup l with
  | none => simp
  | some c =>
    have hmem : (l, c) ∈ P := by
      clear h
      induction P with
      | nil => cases hl
      | cons q P ih =>
        obtain ⟨k, c'⟩ := q
        rw [lookup_cons_pair] at hl
        split at hl
        · cases hl; rename_i he; subst he; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih hl)
    simpa using h _ hmem

/-- The cells of one memory, by kind and offset. -/
def memCell (mem : Memory) : Nat × Nat → Option (Cell H)
  | (0, i) => if mem.wf ∧ i < mem.byteSize then some (.byte (mem.read8 i)) else none
  | (1, 0) => if mem.wf then some (.memLength mem.byteSize) else none
  | (1, 1) => if mem.wf then some (.memLimit mem.max) else none
  | _ => none

theorem lookup_mem (σ : Store H) (k a i : Nat) (hk : k = 0 ∨ k = 1) :
    lookup σ (k, a, i) = σ.mems[a]?.bind fun mem => memCell mem (k, i) := by
  rcases hk with rfl | rfl
  · rfl
  · rcases i with _ | _ | i
    · rfl
    · rfl
    · simp [lookup, memCell]

theorem lookup_setMem (σ : Store H) (n : Nat) (mem' : Memory) (hn : n < σ.mems.size)
    (k a i : Nat) : lookup { σ with mems := σ.mems.set! n mem' } (k, a, i) =
      if (k = 0 ∨ k = 1) ∧ a = n then memCell mem' (k, i) else lookup σ (k, a, i) := by
  by_cases hk : k = 0 ∨ k = 1
  · rw [lookup_mem _ _ _ _ hk, lookup_mem _ _ _ _ hk]
    by_cases ha : a = n
    · subst ha
      simp [hk, hn]
    · simp [ha, Ne.symm ha]
  · rw [lookup_with_mems _ _ _ (by simp only; omega)]
    simp [hk]

/-- Writing a run of bytes replaces exactly their cells. -/
theorem replaces_write {σ : Store H} {n addr : Nat} {mem : Memory}
    (hmem : σ.mems[n]? = some mem) (hwf : mem.wf) {old : List UInt8}
    (hb : addr + old.length ≤ mem.byteSize) (g : Nat → UInt8) :
    Replaces σ { σ with mems := σ.mems.set! n (mem.writeRun addr old.length g) }
      (byteCells n addr old) (byteCells n addr ((List.range old.length).map g)) := by
  obtain ⟨hwf', hsz, hmax, hrd'⟩ := Memory.writeRun_spec hwf hb g
  have hn : n < σ.mems.size := (Array.getElem?_eq_some_iff.mp hmem).1
  intro ⟨k, a, i⟩
  rw [lookup_setMem _ _ _ hn, lookup_byteCells, lookup_byteCells]
  simp only [List.length_map, List.length_range]
  by_cases hk : (k = 0 ∨ k = 1) ∧ a = n
  · rw [ite_eq_left hk]
    obtain ⟨hk, rfl⟩ := hk
    rw [lookup_mem _ _ _ _ hk, hmem, Option.bind_some]
    rcases hk with rfl | rfl
    · by_cases hi : addr ≤ i ∧ i < addr + old.length
      · have hlt : i < mem.byteSize := by omega
        have hidx : i - addr < old.length := by omega
        simp only [hi, and_self, ite_true, memCell, hwf', hsz, hrd', hlt, Option.some_or]
        simp [List.getElem?_range hidx]
      · have hi' : ¬(addr ≤ i ∧ i < addr + old.length) := hi
        simp [memCell, hwf, hwf', hsz, hrd', hi']
    · rcases i with _ | _ | i <;> simp [memCell, hwf, hwf', hsz, hmax]
  · rw [ite_eq_right hk]
    have : ¬(k = 0 ∧ a = n ∧ addr ≤ i ∧ i < addr + old.length) := fun h => hk ⟨.inl h.1, h.2.1⟩
    simp [this]

end Cells

/-! ## Loads and stores -/

/-- How many bytes a load reads. -/
def loadWidth (t : NumType) (packed : Option Packed) : Nat :=
  match packed with
  | some p => p.bits / 8
  | none => t.byteWidth

/-- The value a load produces from the little-endian number it read. -/
def loadValue (t : NumType) (packed : Option Packed) (raw : Nat) : Value :=
  match t, packed with
  | .i32, some p => .i32 (UInt32.ofNat (if p.signed then Numeric.signExtend 32 p.bits raw else raw))
  | .i64, some p => .i64 (UInt64.ofNat (if p.signed then Numeric.signExtend 64 p.bits raw else raw))
  | .i32, none => .i32 (UInt32.ofNat raw)
  | .i64, none => .i64 (UInt64.ofNat raw)
  | .f32, _ => .f32 (UInt32.ofNat raw)
  | .f64, _ => .f64 (UInt64.ofNat raw)

/-- How many bytes a store writes. -/
def storeWidth (t : NumType) (bits : Option Nat) : Nat :=
  match bits with
  | some b => b / 8
  | none => t.byteWidth

/-- The number a store writes, little-endian. -/
def storeRaw (v : Value) : Nat :=
  match v with
  | .i32 n | .f32 n => n.toNat
  | .i64 n | .f64 n => n.toNat
  | .ref _ => 0

/-- The bytes a store writes. -/
def storeBytes (v : Value) (len : Nat) : List UInt8 :=
  (List.range len).map fun i => UInt8.ofNat (storeRaw v >>> (8 * i))

section Rules

variable {H : Type} {GF : BundledGFunctors} [WasmGS H GF]
variable {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value} {Φ : Post H GF}

theorem memOf_eq {σ : Store H} {mi : ModuleInst} {n : Nat} {mem : Memory}
    (hn : mi.memAddrs[0]? = some n) (hmem : σ.mems[n]? = some mem) : σ.memOf mi = some mem := by
  simp [Store.memOf, hn, hmem]

theorem loadNat_eq {σ : Store H} {mi : ModuleInst} {n : Nat} {mem : Memory} {arg : MemArg}
    {a : UInt32} {bs : List UInt8} (hn : mi.memAddrs[0]? = some n) (hmem : σ.mems[n]? = some mem)
    (hb : a.toNat + arg.offset + bs.length ≤ mem.byteSize)
    (hrd : ∀ k, k < bs.length → mem.read8 (a.toNat + arg.offset + k) = bs[k]!) :
    Exec.loadNat σ mi arg a bs.length = some (Memory.decodeLE bs) := by
  simp only [Exec.loadNat, memOf_eq hn hmem]
  show mem.readNat (a.toNat + arg.offset) bs.length = _
  rw [Memory.readNat_eq hb]
  congr 2
  apply List.ext_getElem
  · simp
  · intro k h1 h2
    simp only [List.getElem_map, List.getElem_range]
    rw [hrd k h2, getElem!_pos bs k h2]

/-- Iris-Wasm's `wp_load`: read owned bytes. -/
theorem wpi_load (t : NumType) (packed : Option Packed) (arg : MemArg) (a : UInt32) (n : Nat)
    (bs : List UInt8) (hn : f.mi.memAddrs[0]? = some n) (hlen : bs.length = loadWidth t packed)
    (hne : bs ≠ []) :
    n ↦[wms][ a.toNat + arg.offset ] bs ∗
      ▷ (n ↦[wms][ a.toNat + arg.offset ] bs -∗
          Φ.normal (vs ++ [loadValue t packed (Memory.decodeLE bs)]) f)
      ⊢ wpi lim d f (vs ++ [.i32 a]) [.load t packed arg] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 a])
    (.load t packed arg) (vs ++ [loadValue t packed (Memory.decodeLE bs)]) f.locals []
    (byteCells n (a.toNat + arg.offset) bs) (byteCells n (a.toNat + arg.offset) bs)
    (byteCells_nodup _ _ _) (byteCells_nodup _ _ _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, _, hb, hrd⟩ := bytes_facts hne hP
      refine ⟨σ, ?_, replaces_same hP⟩
      have hload := loadNat_eq (arg := arg) (a := a) hn hmem hb hrd
      rw [hlen] at hload
      cases t <;> cases packed <;>
        simp_all [Exec.instr, Exec.i32, loadWidth, loadValue])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold memBytes
  iintro ⟨Hb, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hb]
  · iexact Hb
  · iexact HΦ

/-- Iris-Wasm's `wp_store`: overwrite owned bytes. -/
theorem wpi_store (t : NumType) (bits : Option Nat) (arg : MemArg) (a : UInt32) (v : Value)
    (n : Nat) (old : List UInt8) (hn : f.mi.memAddrs[0]? = some n)
    (hlen : old.length = storeWidth t bits) (hne : old ≠ []) :
    n ↦[wms][ a.toNat + arg.offset ] old ∗
      ▷ (n ↦[wms][ a.toNat + arg.offset ] storeBytes v old.length -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 a, v]) [.store t bits arg] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 a, v])
    (.store t bits arg) vs f.locals []
    (byteCells n (a.toNat + arg.offset) old)
    (byteCells n (a.toNat + arg.offset) (storeBytes v old.length))
    (byteCells_nodup _ _ _) (byteCells_nodup _ _ _)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, hwf, hb, _⟩ := bytes_facts hne hP
      let g := fun i => UInt8.ofNat (storeRaw v >>> (8 * i))
      refine ⟨{ σ with mems := σ.mems.set! n (mem.writeRun (a.toNat + arg.offset) old.length g) },
        ?_, replaces_write hmem hwf hb g⟩
      have hstore : Exec.storeNat σ f.mi arg a old.length (storeRaw v) =
          some { σ with mems := σ.mems.set! n (mem.writeRun (a.toNat + arg.offset) old.length g) } := by
        simp [Exec.storeNat, memOf_eq hn hmem, Memory.writeNat_eq hb, Store.setMemOf, hn, g]
      rw [hlen] at hstore
      cases bits <;> cases v <;>
        simp_all [Exec.instr, Exec.i32, storeWidth, storeRaw])
    (by
      intro σ _ _ _ l hq hp
      rw [lookup_byteCells] at hq hp
      simp only [storeBytes, List.length_map, List.length_range] at hq
      split at hp
      · cases hp
      · rename_i hc; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold memBytes
  iintro ⟨Hb, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hb]
  · iexact Hb
  · iexact HΦ

/-- What owning a memory's length says about the store. -/
theorem memLength_facts {σ : Store H} {n len : Nat}
    (h : lookup σ (Loc.memLength n) = some (Cell.memLength len)) :
    ∃ mem, σ.mems[n]? = some mem ∧ mem.wf ∧ mem.byteSize = len := by
  simp only [lookup_memLength, Option.bind_eq_some_iff] at h
  obtain ⟨mem, hmem, h⟩ := h
  split at h
  · cases h; exact ⟨mem, hmem, by assumption, rfl⟩
  · cases h

theorem memLimit_facts {σ : Store H} {n : Nat} {mx : Option Nat}
    (h : lookup σ (Loc.memLimit n) = some (Cell.memLimit mx)) :
    ∃ mem, σ.mems[n]? = some mem ∧ mem.max = mx := by
  simp only [lookup_memLimit, Option.bind_eq_some_iff] at h
  obtain ⟨mem, hmem, h⟩ := h
  split at h
  · cases h; exact ⟨mem, hmem, rfl⟩
  · cases h

theorem size_eq_div {mem : Memory} : mem.size = mem.byteSize / pageSize := by
  simp [Memory.byteSize, Memory.size, Nat.mul_div_cancel _ Memory.pageSize_pos]

/-- Iris-Wasm's `wp_current_memory`. -/
theorem wpi_memory_size (n len : Nat) (hn : f.mi.memAddrs[0]? = some n) :
    n ↦[wmlength] len ∗
      ▷ (n ↦[wmlength] len -∗ Φ.normal (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f)
      ⊢ wpi lim d f vs [.memory_size] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs)
    .memory_size (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f.locals []
    [(Loc.memLength n, .memLength len)] [(Loc.memLength n, .memLength len)]
    (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, _, hlen⟩ := memLength_facts (hP _ List.mem_cons_self)
      refine ⟨σ, ?_, replaces_same hP⟩
      simp [Exec.instr, memOf_eq hn hmem, size_eq_div, hlen])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold memLength
  iintro ⟨Hl, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hl]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ
    iapply HΦ
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    iexact HQ

/-- When `memory.grow` by `k` pages succeeds: the limits allow it. -/
def GrowOk (len : Nat) (mx : Option Nat) (k : Nat) : Prop :=
  len / pageSize + k ≤ maxPages ∧ ∀ m, mx = some m → len / pageSize + k ≤ m

theorem grow_eq {mem : Memory} {k : Nat} (h : GrowOk mem.byteSize mem.max k) :
    mem.grow k = some { mem with pages := mem.pages ++ Array.replicate k ByteArray.empty } := by
  obtain ⟨h1, h2⟩ := h
  rw [← size_eq_div] at h1 h2
  unfold Memory.grow
  dsimp only
  rw [ite_eq_right (by omega)]
  cases hm : mem.max with
  | none => simp
  | some m => have := h2 m hm; simp; omega

theorem grow_eq_none {mem : Memory} {k : Nat} (h : ¬GrowOk mem.byteSize mem.max k) :
    mem.grow k = none := by
  apply Memory.grow_none.mpr
  unfold GrowOk at h
  rw [← size_eq_div] at h
  cases hm : mem.max with
  | none => simp_all <;> omega
  | some m =>
    simp only [Option.any_some, decide_eq_true_eq]
    by_cases h1 : mem.size + k ≤ maxPages
    · right
      apply Classical.byContradiction
      intro h3
      exact h ⟨h1, fun m' hm' => by rw [hm] at hm'; cases hm'; omega⟩
    · left; omega

/-- The cells `memory.grow` by `k` pages leaves: the new length and the new
bytes, all zero. -/
def growCells (n len k : Nat) : List (Loc × Cell H) :=
  (Loc.memLength n, .memLength (len + k * pageSize)) :: byteCells n len (List.replicate (k * pageSize) 0)

theorem growCells_nodup (n len k : Nat) : ((growCells (H := H) n len k).map (·.1)).Nodup := by
  simp only [growCells, List.map_cons, List.nodup_cons]
  refine ⟨fun hmem => ?_, byteCells_nodup _ _ _⟩
  obtain ⟨p, hp, hp1⟩ := List.mem_map.mp hmem
  have := lookup_byteCells (H := H) n len (List.replicate (k * pageSize) 0) p.1
  rw [lookup_of_mem (byteCells_nodup _ _ _) hp] at this
  split at this
  · rename_i hc; rw [hp1] at hc; simp [] at hc
  · cases this

/-- `memory.grow` succeeding, as a step of the store. -/
theorem grow_step_ok {σ : Store H} {n len : Nat} {mem : Memory} {mi : ModuleInst}
    (hn : mi.memAddrs[0]? = some n) (hmem : σ.mems[n]? = some mem) (hwf : mem.wf)
    (hlen : mem.byteSize = len) (k : UInt32) (hok : GrowOk len mem.max k.toNat)
    (loc : Array Value) (base : List Value) (L : List Label) (R : List Instr) : ∃ σ',
    Exec.instr σ mi loc (base ++ [Value.i32 k]).toArray L .memory_grow R =
      ⟨σ', .continue (base ++ [Value.i32 (UInt32.ofNat (len / pageSize))]).toArray L R loc⟩ ∧
    Replaces σ σ' [(Loc.memLength n, .memLength len)] (growCells n len k.toNat) := by
  have hn' : n < σ.mems.size := (Array.getElem?_eq_some_iff.mp hmem).1
  have hgrow := grow_eq (k := k.toNat) (by rw [hlen]; exact hok)
  obtain ⟨hwf', hsz', hmax', _, hrd'⟩ := Memory.grow_spec hwf hgrow
  let mem' : Memory := { mem with pages := mem.pages ++ Array.replicate k.toNat ByteArray.empty }
  refine ⟨{ σ with mems := σ.mems.set! n mem' }, ?_, ?_⟩
  · simp [Exec.instr, Exec.i32, memOf_eq hn hmem, hgrow, Store.setMemOf, hn, size_eq_div, hlen, mem']
  · intro ⟨c, a, i⟩
    rw [lookup_setMem _ _ _ hn', growCells, lookup_cons_pair, lookup_byteCells, lookup_cons_pair]
    simp only [List.length_replicate, Loc.memLength, Prod.mk.injEq, List.lookup_nil]
    by_cases hc : (c = 0 ∨ c = 1) ∧ a = n
    · rw [ite_eq_left hc]
      obtain ⟨hc, rfl⟩ := hc
      rw [lookup_mem _ _ _ _ hc, hmem, Option.bind_some]
      rcases hc with rfl | rfl
      · by_cases hi : i < len
        · have : ¬(len ≤ i ∧ i < len + k.toNat * pageSize) := by omega
          simp [memCell, hwf, hwf', hsz', hrd', hi, hlen, mem',
            show i < len + k.toNat * pageSize by omega, show ¬len ≤ i by omega]
        · by_cases hi2 : i < len + k.toNat * pageSize
          · simp [memCell, hwf', hsz', hrd', hlen, hi, hi2, show len ≤ i by omega, mem',
              show i - len < k.toNat * pageSize by omega]
          · simp [memCell, hwf, hwf', hsz', hlen, hi, hi2, mem']
      · rcases i with _ | _ | i <;> simp [memCell, hwf, hwf', hsz', hlen, mem']
    · rw [ite_eq_right hc]
      have h1 : ¬(c = 1 ∧ a = n ∧ i = 0) := fun h => hc ⟨.inr h.1, h.2.1⟩
      have h2 : ¬(c = 0 ∧ a = n ∧ len ≤ i ∧ i < len + k.toNat * pageSize) :=
        fun h => hc ⟨.inl h.1, h.2.1⟩
      simp [h1, h2]

/-- The new bytes `memory.grow` adds are not cells of the store before it. -/
theorem grow_fresh {σ : Store H} {n len k : Nat}
    (hP : lookup σ (Loc.memLength n) = some (.memLength len)) (l : Loc)
    (hq : ((growCells (H := H) n len k).lookup l).isSome)
    (hp : [(Loc.memLength n, (Cell.memLength len : Cell H))].lookup l = none) : lookup σ l = none := by
  obtain ⟨mem, hmem, hwf, hlen⟩ := memLength_facts hP
  obtain ⟨c, a, i⟩ := l
  rw [growCells, lookup_cons_pair, lookup_byteCells] at hq
  rw [lookup_cons_pair] at hp
  simp only [Loc.memLength, Prod.mk.injEq, List.length_replicate, List.lookup_nil] at hq hp
  split at hq
  · rename_i h; rw [ite_eq_left h] at hp; cases hp
  · split at hq
    · rename_i _ h
      obtain ⟨rfl, rfl, h3, _⟩ := h
      simp [lookup_byte, hmem, hwf, hlen, show ¬ i < len by omega]
    · cases hq

/-- `memory.grow` failing, as a step of the store. -/
theorem grow_step_fail {σ : Store H} {n len : Nat} {mem : Memory} {mi : ModuleInst}
    (hn : mi.memAddrs[0]? = some n) (hmem : σ.mems[n]? = some mem)
    (hlen : mem.byteSize = len) (k : UInt32) (hfail : ¬GrowOk len mem.max k.toNat)
    (loc : Array Value) (base : List Value) (L : List Label) (R : List Instr) :
    Exec.instr σ mi loc (base ++ [Value.i32 k]).toArray L .memory_grow R =
      ⟨σ, .continue (base ++ [Value.i32 0xFFFFFFFF]).toArray L R loc⟩ := by
  have hgrow := grow_eq_none (mem := mem) (k := k.toNat) (by rw [hlen]; exact hfail)
  simp [Exec.instr, Exec.i32, memOf_eq hn hmem, hgrow]

open Classical in
/-- Iris-Wasm's `wp_grow_memory`: `memory.grow` either adds `k` pages of
zeros and returns the old size in pages, or fails and returns `-1`. Which
one depends on the memory's limit, which this rule does not need to know. -/
theorem wpi_memory_grow_either (n len : Nat) (k : UInt32) (hn : f.mi.memAddrs[0]? = some n) :
    n ↦[wmlength] len ∗
      ▷ ((⌜len / pageSize + k.toNat ≤ maxPages⌝ -∗ n ↦[wmlength] (len + k.toNat * pageSize) ∗
            n ↦[wms][ len ] List.replicate (k.toNat * pageSize) 0 -∗
          Φ.normal (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f) ∧
        (n ↦[wmlength] len -∗ Φ.normal (vs ++ [.i32 0xFFFFFFFF]) f))
      ⊢ wpi lim d f (vs ++ [.i32 k]) [.memory_grow] Φ := by
  let ok : Store H → Prop := fun σ =>
    ∃ mem, σ.mems[n]? = some mem ∧ GrowOk len mem.max k.toNat
  have key := wpi_instr_dep (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 k])
    .memory_grow (fun σ => if ok σ then vs ++ [.i32 (UInt32.ofNat (len / pageSize))]
      else vs ++ [.i32 0xFFFFFFFF]) f.locals [] [(Loc.memLength n, .memLength len)]
    (fun σ => if ok σ then growCells n len k.toNat else [(Loc.memLength n, .memLength len)])
    (by simp) (fun σ => by split <;> simp [growCells_nodup])
    (by
      intro σ _ _ hP base L R
      obtain ⟨mem, hmem, hwf, hlen⟩ := memLength_facts (hP _ List.mem_cons_self)
      by_cases hok : GrowOk len mem.max k.toNat
      · have hσ : ok σ := ⟨mem, hmem, hok⟩
        simp only [hσ, ite_true]
        have := grow_step_ok hn hmem hwf hlen k hok f.locals (base ++ vs) L R
        simpa only [List.append_assoc] using this
      · have hσ : ¬ok σ := fun ⟨m, hm, h⟩ => by rw [hmem] at hm; cases hm; exact hok h
        simp only [hσ, ite_false]
        refine ⟨σ, ?_, replaces_same hP⟩
        have := grow_step_fail hn hmem hlen k hok f.locals (base ++ vs) L R
        simpa only [List.append_assoc] using this)
    (by
      intro σ _ _ hP l hq hp
      split at hq
      · exact grow_fresh (hP _ List.mem_cons_self) l hq hp
      · simp_all)
  simp only [Frame.withLocals_self] at key
  unfold memLength memBytes
  iintro ⟨Hl, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hl]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro %σ %_ HQ
    by_cases hσ : ok σ
    · obtain ⟨_, _, hok⟩ := hσ
      have hσ' : ok σ := ⟨_, by assumption, hok⟩
      simp only [hσ', ite_true, growCells]
      icases HΦ with ⟨HΦ, -⟩
      icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ1, HQ2⟩
      ispecialize HΦ $$ %hok.1
      iapply HΦ
      isplitl [HQ1]
      · iexact HQ1
      · iexact HQ2
    · simp only [hσ, ite_false]
      icases HΦ with ⟨-, HΦ⟩
      icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
      iapply HΦ $$ HQ

/-- `memory.grow` when the limit allows it: `k` new pages of zeros. -/
theorem wpi_memory_grow (n len : Nat) (mx : Option Nat) (k : UInt32)
    (hn : f.mi.memAddrs[0]? = some n) (hok : GrowOk len mx k.toNat) :
    n ↦[wmlength] len ∗ n ↪[wmlimit] mx ∗
      ▷ (n ↦[wmlength] (len + k.toNat * pageSize) ∗
          n ↦[wms][ len ] List.replicate (k.toNat * pageSize) 0 -∗
        Φ.normal (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f)
      ⊢ wpi lim d f (vs ++ [.i32 k]) [.memory_grow] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 k])
    .memory_grow (vs ++ [.i32 (UInt32.ofNat (len / pageSize))]) f.locals
    [(Loc.memLimit n, .memLimit mx)] [(Loc.memLength n, .memLength len)]
    (growCells n len k.toNat) (by simp) (growCells_nodup _ _ _)
    (by
      intro σ _ hRd hP base L R
      obtain ⟨mem, hmem, hwf, hlen⟩ := memLength_facts (hP _ List.mem_cons_self)
      obtain ⟨mem', hmem', hmax⟩ := memLimit_facts (hRd _ List.mem_cons_self)
      rw [hmem] at hmem'; cases hmem'
      have := grow_step_ok hn hmem hwf hlen k (by rw [hmax]; exact hok) f.locals (base ++ vs) L R
      simpa only [List.append_assoc] using this)
    (fun σ _ _ hP l hq hp => grow_fresh (hP _ List.mem_cons_self) l hq hp)
  simp only [Frame.withLocals_self] at key
  unfold memLength memLimit memBytes
  iintro ⟨Hl, #Hm, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexact Hm
    · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hl]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ
    simp only [growCells]
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ1, HQ2⟩
    iapply HΦ
    isplitl [HQ1]
    · iexact HQ1
    · iexact HQ2

/-- `memory.grow` when the limit forbids it: `-1`, nothing changes. -/
theorem wpi_memory_grow_fail (n len : Nat) (mx : Option Nat) (k : UInt32)
    (hn : f.mi.memAddrs[0]? = some n) (hfail : ¬GrowOk len mx k.toNat) :
    n ↦[wmlength] len ∗ n ↪[wmlimit] mx ∗
      ▷ (n ↦[wmlength] len -∗ Φ.normal (vs ++ [.i32 0xFFFFFFFF]) f)
      ⊢ wpi lim d f (vs ++ [.i32 k]) [.memory_grow] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [.i32 k])
    .memory_grow (vs ++ [.i32 0xFFFFFFFF]) f.locals
    [(Loc.memLimit n, .memLimit mx)] [(Loc.memLength n, .memLength len)]
    [(Loc.memLength n, .memLength len)] (by simp) (by simp)
    (by
      intro σ _ hRd hP base L R
      obtain ⟨mem, hmem, _, hlen⟩ := memLength_facts (hP _ List.mem_cons_self)
      obtain ⟨mem', hmem', hmax⟩ := memLimit_facts (hRd _ List.mem_cons_self)
      rw [hmem] at hmem'; cases hmem'
      refine ⟨σ, ?_, replaces_same hP⟩
      have := grow_step_fail hn hmem hlen k (by rw [hmax]; exact hfail) f.locals (base ++ vs) L R
      simpa only [List.append_assoc] using this)
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold memLength memLimit
  iintro ⟨Hl, #Hm, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_cons.2
    isplitr
    · iexact Hm
    · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hl]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hl]
    · iexact Hl
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ
    iapply HΦ
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    iexact HQ

/-! ## Globals -/

theorem global_facts {σ : Store H} {a : Nat} {gi : GlobalInst}
    (h : lookup σ (Loc.global a) = some (Cell.global gi)) : σ.globals[a]? = some gi := by
  simp only [lookup_global, Option.map_eq_some_iff] at h
  obtain ⟨g, hg, he⟩ := h
  cases he; exact hg

theorem lookup_modifyGlobal (σ : Store H) (a : Nat) (F : GlobalInst → GlobalInst) (k b i : Nat) :
    lookup { σ with globals := σ.globals.modify a F } (k, b, i) =
      if k = 2 ∧ b = a ∧ i = 0 then σ.globals[a]?.map (fun g => .global (F g))
      else lookup σ (k, b, i) := by
  by_cases hk : k = 2
  · subst hk
    rcases i with _ | i
    · by_cases hb : b = a
      · subst hb; simp [lookup, Array.getElem?_modify]; rfl
      · simp [lookup, Array.getElem?_modify, hb, Ne.symm hb]
    · simp [lookup]
  · rw [lookup_with_globals _ _ _ (by simpa using hk)]
    simp [hk]

/-- Iris-Wasm's `wp_get_global`. -/
theorem wpi_global_get (g a : Nat) (gi : GlobalInst) (ha : f.mi.globalAddrs[g]? = some a) :
    a ↦[wg] gi ∗ ▷ (a ↦[wg] gi -∗ Φ.normal (vs ++ [gi.value]) f)
      ⊢ wpi lim d f vs [.global_get g] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs)
    (.global_get g) (vs ++ [gi.value]) f.locals [] [(Loc.global a, .global gi)]
    [(Loc.global a, .global gi)] (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      have hg := global_facts (hP _ List.mem_cons_self)
      refine ⟨σ, ?_, replaces_same hP⟩
      simp [Exec.instr, getElem!_def, ha, hg])
    (by intro σ _ _ _ l hq hp; simp_all)
  simp only [Frame.withLocals_self] at key
  unfold globalPt
  iintro ⟨Hg, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hg]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hg]
    · iexact Hg
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ
    iapply HΦ
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    iexact HQ

/-- Iris-Wasm's `wp_set_global`. -/
theorem wpi_global_set (g a : Nat) (gi : GlobalInst) (v : Value)
    (ha : f.mi.globalAddrs[g]? = some a) :
    a ↦[wg] gi ∗ ▷ (a ↦[wg] { gi with value := v } -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [v]) [.global_set g] Φ := by
  have key := wpi_instr (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs ++ [v])
    (.global_set g) vs f.locals [] [(Loc.global a, .global gi)]
    [(Loc.global a, .global { gi with value := v })] (by simp) (by simp)
    (by
      intro σ _ _ hP base L R
      have hg := global_facts (hP _ List.mem_cons_self)
      refine ⟨{ σ with globals := σ.globals.modify a ({ · with value := v }) }, ?_, ?_⟩
      · simp [Exec.instr, getElem!_def, ha]
      · intro ⟨k, b, i⟩
        rw [lookup_modifyGlobal, lookup_cons_pair, lookup_cons_pair]
        simp only [Loc.global, Prod.mk.injEq, List.lookup_nil]
        by_cases h : k = 2 ∧ b = a ∧ i = 0
        · obtain ⟨rfl, rfl, rfl⟩ := h
          simp [hg]
        · simp [h])
    (by intro σ _ _ _ l hq hp; rw [lookup_cons_pair] at hq hp; split at hq <;> simp_all)
  simp only [Frame.withLocals_self] at key
  unfold globalPt
  iintro ⟨Hg, HΦ⟩
  iapply key
  isplitr
  · iapply BigSepL.bigSepL_nil.2; iempintro
  isplitl [Hg]
  · iapply BigSepL.bigSepL_cons.2
    isplitl [Hg]
    · iexact Hg
    · iapply BigSepL.bigSepL_nil.2; iempintro
  · inext
    iintro HQ
    iapply HΦ
    icases BigSepL.bigSepL_cons.1 $$ HQ with ⟨HQ, -⟩
    iexact HQ

/-! ## Runs of bytes and 32-bit words -/

theorem byteCells_append (n i : Nat) (bs₁ bs₂ : List UInt8) :
    byteCells (H := H) n i (bs₁ ++ bs₂) = byteCells n i bs₁ ++ byteCells n (i + bs₁.length) bs₂ := by
  induction bs₁ generalizing i with
  | nil => simp [byteCells]
  | cons b bs ih => simp [byteCells, ih, Nat.add_assoc, Nat.add_comm 1]

/-- Iris-Wasm's splitting of `↦[wms]` at a point. -/
theorem memBytes_append (n i : Nat) (bs₁ bs₂ : List UInt8) :
    memBytes (GF := GF) n i (bs₁ ++ bs₂) ⊣⊢ memBytes n i bs₁ ∗ memBytes n (i + bs₁.length) bs₂ := by
  unfold memBytes
  rw [byteCells_append]
  exact BigSepL.bigSepL_append (PROP := IProp GF)
    (Φ := fun (_ : Nat) (p : Loc × Cell H) => iprop(p.1 ↦ₛ p.2))
    (l₁ := byteCells n i bs₁) (l₂ := byteCells n (i + bs₁.length) bs₂)

theorem memBytes_congr {n i j : Nat} {bs : List UInt8} (h : i = j) :
    memBytes (GF := GF) n i bs ⊣⊢ memBytes n j bs := by subst h; exact .rfl

@[simp] theorem bytes32_length (v : UInt32) : (bytes32 v).length = 4 := by simp [bytes32]

theorem decodeLE_bytes32 (v : UInt32) : Memory.decodeLE (bytes32 v) = v.toNat := by
  have hv := v.toNat_lt
  simp [bytes32, Memory.decodeLE, List.range, List.range.loop, Nat.shiftRight_eq_div_pow]
  omega

theorem storeBytes_i32 (w : UInt32) : storeBytes (.i32 w) 4 = bytes32 w := rfl

/-- Iris-Wasm's `wp_load` at `i32`: read an owned word. -/
theorem wpi_load_i32 (arg : MemArg) (a : UInt32) (n k : Nat) (w : UInt32)
    (hn : f.mi.memAddrs[0]? = some n) (hk : a.toNat + arg.offset = k) :
    n ↦[i32][ k ] w ∗ ▷ (n ↦[i32][ k ] w -∗ Φ.normal (vs ++ [.i32 w]) f)
      ⊢ wpi lim d f (vs ++ [.i32 a]) [.load .i32 none arg] Φ := by
  subst hk
  have h := wpi_load (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs) .i32 none arg a n (bytes32 w) hn
    (by simp [loadWidth, NumType.byteWidth]) (by simp [bytes32])
  simp only [loadValue, decodeLE_bytes32, UInt32.ofNat_toNat] at h
  exact h

/-- Iris-Wasm's `wp_store` at `i32`: overwrite four owned bytes with a word. -/
theorem wpi_store_i32 (arg : MemArg) (a : UInt32) (n k : Nat) (w : UInt32) (old : List UInt8)
    (hn : f.mi.memAddrs[0]? = some n) (hk : a.toNat + arg.offset = k) (hold : old.length = 4) :
    n ↦[wms][ k ] old ∗ ▷ (n ↦[i32][ k ] w -∗ Φ.normal vs f)
      ⊢ wpi lim d f (vs ++ [.i32 a, .i32 w]) [.store .i32 none arg] Φ := by
  subst hk
  have h := wpi_store (Φ := Φ) (lim := lim) (d := d) (f := f) (vs := vs) .i32 none arg a (.i32 w) n old hn
    (by simp [storeWidth, NumType.byteWidth, hold]) (by intro h; simp [h] at hold)
  rw [hold, storeBytes_i32] at h
  exact h

end Rules

end WasmLogic
