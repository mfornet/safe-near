import Wasm

/-!
# Lemmas about linear memory

The runtime's `Memory` is an array of pages, each empty (all zeros) or
materialised. Its byte API behaves like a flat byte array when every page is
empty or exactly one page long; `Memory.wf` says so. Every operation the
runtime performs keeps memories well formed, and the heap view
(`WasmLogic.lookup`) only shows the cells of well-formed memories, so the
logic can use these lemmas wherever it owns a byte.

Lemmas only: nothing here changes the runtime.
-/

namespace Wasm.Memory

/-- Every page is empty or one page long. -/
def wf (m : Memory) : Bool := m.pages.all fun p => p.size == 0 || p.size == pageSize

theorem pageSize_pos : 0 < pageSize := by decide

theorem wf_iff (m : Memory) :
    m.wf ↔ ∀ i (h : i < m.pages.size), m.pages[i].size = 0 ∨ m.pages[i].size = pageSize := by
  simp [wf, Array.all_iff_forall]

theorem byteSize_eq (m : Memory) : m.byteSize = m.pages.size * pageSize := rfl

theorem page_lt {m : Memory} {a : Nat} (ha : a < m.byteSize) : a / pageSize < m.pages.size := by
  rw [byteSize_eq] at ha
  exact (Nat.div_lt_iff_lt_mul pageSize_pos).mpr ha

theorem wf_get? {m : Memory} (hwf : m.wf) {q : Nat} {p : ByteArray} (hp : m.pages[q]? = some p) :
    p.size = 0 ∨ p.size = pageSize := by
  obtain ⟨hq, rfl⟩ := Array.getElem?_eq_some_iff.mp hp
  exact (wf_iff m).mp hwf q hq

theorem materialise_size {p : ByteArray} (h : p.size = 0 ∨ p.size = pageSize) :
    (materialise p).size = pageSize := by
  unfold materialise
  split
  · show (Array.replicate pageSize (0 : UInt8)).size = pageSize
    simp
  · omega

theorem materialise_get! {p : ByteArray} {k : Nat} (hk : k < pageSize) :
    (materialise p)[k]! = if p.size = 0 then 0 else p[k]! := by
  by_cases h0 : p.size = 0
  · have : k < (ByteArray.mk (Array.replicate pageSize 0)).size := by
      show k < (Array.replicate _ _).size; simp [hk]
    simp only [materialise, h0, ite_true]
    rw [getElem!_pos (ByteArray.mk (Array.replicate pageSize 0)) k this]
    simp [ByteArray.getElem_eq_getElem_data]
  · simp [materialise, h0]

@[simp] theorem write8_byteSize (m : Memory) (a : Nat) (b : UInt8) :
    (m.write8 a b).byteSize = m.byteSize := by
  simp [write8, byteSize]

@[simp] theorem write8_size (m : Memory) (a : Nat) (b : UInt8) : (m.write8 a b).size = m.size := by
  simp [write8, size]

@[simp] theorem write8_max (m : Memory) (a : Nat) (b : UInt8) : (m.write8 a b).max = m.max := rfl

theorem write8_wf {m : Memory} (hwf : m.wf) (a : Nat) (b : UInt8) : (m.write8 a b).wf := by
  rw [wf_iff] at hwf ⊢
  intro i hi
  simp only [write8, Array.size_modify] at hi ⊢
  rw [Array.getElem_modify]
  split
  · right
    rw [ByteArray.size_set!]
    exact materialise_size (hwf i hi)
  · exact hwf i hi

theorem read8_write8 {m : Memory} (hwf : m.wf) {a : Nat} (ha : a < m.byteSize) (b : UInt8)
    (j : Nat) : (m.write8 a b).read8 j = if j = a then b else m.read8 j := by
  obtain ⟨p, hp⟩ : ∃ p, m.pages[a / pageSize]? = some p :=
    ⟨_, Array.getElem?_eq_getElem (page_lt ha)⟩
  have hwfp := wf_get? hwf hp
  have hpsz := materialise_size hwfp
  have hamod : a % pageSize < pageSize := Nat.mod_lt _ pageSize_pos
  have hpos : pageSize ≠ 0 := by decide
  unfold read8 write8
  simp only [Array.getElem?_modify]
  by_cases hpage : a / pageSize = j / pageSize
  · rw [ite_eq_left hpage, ← hpage, hp]
    simp only [Option.map_some, ByteArray.size_set!, hpsz, hpos, ite_false]
    by_cases hja : j = a
    · subst hja
      simp [ByteArray.getElem!_set!_self _ _ _ (by rw [hpsz]; exact hamod)]
    · have hne : a % pageSize ≠ j % pageSize := by
        intro h
        apply hja
        rw [← Nat.div_add_mod j pageSize, ← Nat.div_add_mod a pageSize, hpage, h]
      rw [ByteArray.getElem!_set!_ne _ _ _ _ hne, ite_eq_right hja,
        materialise_get! (Nat.mod_lt _ pageSize_pos)]
  · have hja : j ≠ a := fun h => hpage (h ▸ rfl)
    rw [ite_eq_right hpage, ite_eq_right hja]

/-! ## Writing a run of bytes -/

/-- Write `g i` at `addr + i` for `i < len`, as `writeNat` and friends do. -/
def writeRun (m : Memory) (addr len : Nat) (g : Nat → UInt8) : Memory :=
  (List.range len).foldl (fun m i => m.write8 (addr + i) (g i)) m

theorem writeRun_succ (m : Memory) (addr len : Nat) (g : Nat → UInt8) :
    m.writeRun addr (len + 1) g = (m.writeRun addr len g).write8 (addr + len) (g len) := by
  simp [writeRun, List.range_succ, List.foldl_append]

theorem writeRun_spec {m : Memory} (hwf : m.wf) {addr len : Nat} (hb : addr + len ≤ m.byteSize)
    (g : Nat → UInt8) :
    (m.writeRun addr len g).wf ∧ (m.writeRun addr len g).byteSize = m.byteSize ∧
      (m.writeRun addr len g).max = m.max ∧
      ∀ j, (m.writeRun addr len g).read8 j =
        if addr ≤ j ∧ j < addr + len then g (j - addr) else m.read8 j := by
  induction len with
  | zero => simp [writeRun, hwf]; omega
  | succ n ih =>
    obtain ⟨hwf', hsz, hmax, hrd⟩ := ih (by omega)
    rw [writeRun_succ]
    refine ⟨write8_wf hwf' _ _, by simp [hsz], by simp [hmax], fun j => ?_⟩
    rw [read8_write8 hwf' (by omega), hrd]
    by_cases hj : j = addr + n
    · subst hj; simp
    · simp only [hj, ite_false]
      by_cases h1 : addr ≤ j ∧ j < addr + n
      · simp [h1, show addr ≤ j ∧ j < addr + (n + 1) from ⟨h1.1, by omega⟩]
      · have : ¬(addr ≤ j ∧ j < addr + (n + 1)) := by omega
        simp [h1, this]

theorem writeNat_eq {m : Memory} {addr len v : Nat} (hb : addr + len ≤ m.byteSize) :
    m.writeNat addr len v = some (m.writeRun addr len fun i => UInt8.ofNat (v >>> (8 * i))) := by
  simp [writeNat, inBounds, hb, writeRun]

/-! ## Reading a run of bytes -/

/-- Little-endian decoding, as `readNat` does it. -/
def decodeLE (bs : List UInt8) : Nat := bs.foldr (fun b acc => acc * 256 + b.toNat) 0

theorem readNat_eq {m : Memory} {addr len : Nat} (hb : addr + len ≤ m.byteSize) :
    m.readNat addr len = some (decodeLE ((List.range len).map fun i => m.read8 (addr + i))) := by
  simp [readNat, inBounds, hb, decodeLE, List.foldr_map]

/-! ## Growing -/

theorem grow_spec {m : Memory} (hwf : m.wf) {delta : Nat} {m' : Memory}
    (h : m.grow delta = some m') :
    m'.wf ∧ m'.byteSize = m.byteSize + delta * pageSize ∧ m'.max = m.max ∧
      m'.size = m.size + delta ∧
      ∀ j, m'.read8 j = if j < m.byteSize then m.read8 j else 0 := by
  unfold grow at h
  dsimp only at h
  split at h
  · cases h
  split at h
  · cases h
  cases h
  refine ⟨?_, ?_, rfl, by simp [size], fun j => ?_⟩
  · rw [wf_iff] at hwf ⊢
    intro i hi
    simp only [Array.size_append, Array.size_replicate] at hi
    rw [Array.getElem_append]
    split
    · exact hwf i (by assumption)
    · left; simp
  · simp [byteSize, Nat.add_mul]
  · by_cases hj : j < m.byteSize
    · simp only [hj, ite_true, read8]
      rw [Array.getElem?_append_left (page_lt hj)]
    · simp only [hj, ite_false, read8]
      rw [Array.getElem?_append_right (by rw [byteSize_eq] at hj; exact
        (Nat.le_div_iff_mul_le pageSize_pos).mpr (by omega))]
      cases h : (Array.replicate delta ByteArray.empty)[j / pageSize - m.pages.size]? with
      | none => rfl
      | some p =>
        have := Array.getElem?_replicate.symm.trans h
        split at this <;> simp_all

theorem grow_none {m : Memory} {delta : Nat} :
    m.grow delta = none ↔ (m.size + delta > maxPages ∨ m.max.any (m.size + delta > ·)) := by
  unfold grow
  dsimp only
  split
  · simp_all
  · split <;> simp_all

end Wasm.Memory
