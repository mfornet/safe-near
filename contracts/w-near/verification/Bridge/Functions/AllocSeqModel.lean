import Bridge.Functions.AllocFresh

/-!
# The heap model after an allocation from a one-cell free list (M4)

`AllocInv.heapInv n maxP len live 1` already pins down the free list an allocation without
frees leaves: at most one cell, and (`one_cell`) that cell's `next_free` is 0 (`fl_link`
gives `next_free < 4`, `nf_lo` clears bit 1, and `fl_merge` would need a second list cell
for `CAN_MERGE`). `AllocFirstFit.f580_one` walks exactly such a list. This file gives the
models of its two successful outcomes on the listed cell `c` (the cells being
`s ++ c :: t`, `d` the next neighbour when `c` is not last):

* `modelW` (*whole*): `c` allocated in place, the list emptied (`wf_whole`);
* `modelS` (*split* at `m`): `c` shrunk to `[c, m)` and still listed, the allocated cell
  `nS c m = [m, c.next)` inserted right after it, the next neighbour's `prev` set to `m`
  (`tS`); `wf_split`. The new cell goes in the middle of the list: sortedness and
  non-overlap come from `pos_s` / `pos_t` (by `Geo.disj`: every cell after `c` starts at or
  past `c.next`).

`lives_gen` is `AllocFresh.lives_append` for a new allocated cell anywhere.
-/

namespace WNear.Binary.AllocSeqModel

open WNear.Binary.AllocInv
open WNear.Binary.AllocDealloc (upd mem_map_upd addrs_map_upd nodup_of_sorted cellAt_iff' mem_unique geo_map)
open WNear.Binary.AllocFresh (lists_one lists_nil)

/-- The listed cell of a one-cell free list has `next_free = 0`. -/
theorem one_cell {H : HeapModel} {live : List (Nat × Nat)} (hw : H.wf live 1) {a : Nat}
    (hfl : H.freeList = [a]) : ∃ c, H.cellAt a = some c ∧ c.allocated = false ∧ c.nextFree = 0 := by
  have hi : 0 < H.freeList.length := by simp [hfl]
  obtain ⟨c, hc, hlink⟩ := hw.lists.fl_link 0 hi
  have e0 : H.freeList[0] = a := by simp [hfl]
  rw [e0] at hc
  obtain ⟨c', hc', hcf⟩ := hw.lists.fl_free a (by simp [hfl])
  rw [hc] at hc'; cases hc'
  refine ⟨c, hc, hcf, ?_⟩
  have hl : H.freeList.getD (0 + 1) 0 = 0 := by simp [hfl]
  rw [hl] at hlink
  have hcm := (cellAt_iff' (nodup_of_sorted hw.geo.sorted)).mp hc
  have hlo := hw.nf_lo c hcm.1
  have hodd : c.nextFree % 2 = 0 := by
    by_contra hne
    obtain ⟨d, hd, -⟩ := hw.lists.fl_merge 0 hi c (by rw [e0]; exact hc) (by omega)
    simp [hfl] at hd
  omega

/-- A new allocated cell `cA` at `a`, lent as `(a + 8, s)`; every old allocated cell has a
cell at its address, allocated, at least as large; every new allocated cell but `cA` has
an old one at its address; no old allocated cell is at `a`. -/
theorem lives_gen {H H' : HeapModel} {live : List (Nat × Nat)} (hv : Lives H live) {a s : Nat}
    {cA : CellM} (hcA : cA ∈ H'.cells) (hA : cA.allocated = true) (hAa : cA.addr = a) (hs0 : 0 < s)
    (hs : s ≤ cA.size)
    (hold : ∀ x ∈ H.cells, x.allocated = true → ∃ y ∈ H'.cells, y.allocated = true ∧ y.addr = x.addr ∧
      x.size ≤ y.size)
    (hnew : ∀ z ∈ H'.cells, z.allocated = true → z = cA ∨ ∃ x ∈ H.cells, x.allocated = true ∧ x.addr = z.addr)
    (hfr : ∀ x ∈ H.cells, x.allocated = true → x.addr ≠ a) : Lives H' ((a + 8, s) :: live) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p s' hm
    rcases List.mem_cons.mp hm with e | hm
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨hs0, cA, hcA, hA, by rw [hAa], hs⟩
    · obtain ⟨hpos, x, hx, hxa, hp, hle⟩ := hv.live_cell _ _ hm
      obtain ⟨y, hy, hya, hyx, hsz⟩ := hold x hx hxa
      exact ⟨hpos, y, hy, hya, by rw [hyx]; exact hp, by omega⟩
  · intro z hz hza
    rcases hnew z hz hza with rfl | ⟨x, hx, hxa, hxz⟩
    · exact ⟨s, by rw [hAa]; exact List.mem_cons_self⟩
    · obtain ⟨s', h⟩ := hv.cell_live x hx hxa
      exact ⟨s', List.mem_cons_of_mem _ (by rw [← hxz]; exact h)⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hv.live_nodup⟩
    intro hm
    obtain ⟨⟨p, s'⟩, hps, hp⟩ := List.mem_map.mp hm
    simp only at hp; subst hp
    obtain ⟨-, x, hx, hxa, hpx, -⟩ := hv.live_cell _ _ hps
    exact hfr x hx hxa (by omega)

/-! ## The position of a cell in the sorted list -/

section Pos

variable {H : HeapModel} {s t : List CellM} {c : CellM}

theorem mem_cells (hc : H.cells = s ++ c :: t) (z : CellM) : z ∈ H.cells ↔ z ∈ s ∨ z = c ∨ z ∈ t := by
  rw [hc, List.mem_append, List.mem_cons]

theorem sorted_parts (hg : Geo H) (hc : H.cells = s ++ c :: t) :
    (s.map (·.addr)).Pairwise (· < ·) ∧ (t.map (·.addr)).Pairwise (· < ·) ∧
      (∀ x ∈ s, x.addr < c.addr) ∧ (∀ x ∈ t, c.addr < x.addr) := by
  have hs := hg.sorted
  rw [hc, List.map_append, List.map_cons, List.pairwise_append, List.pairwise_cons] at hs
  refine ⟨hs.1, hs.2.1.2, ?_, ?_⟩
  · intro x hx; exact hs.2.2 _ (List.mem_map_of_mem hx) _ List.mem_cons_self
  · intro x hx; exact hs.2.1.1 _ (List.mem_map_of_mem hx)

theorem pos_s (hg : Geo H) (hc : H.cells = s ++ c :: t) : ∀ x ∈ s, x.addr < c.addr ∧ x.next ≤ c.addr := by
  intro x hx
  have h1 := (sorted_parts hg hc).2.2.1 x hx
  exact ⟨h1, hg.disj x ((mem_cells hc x).mpr (Or.inl hx)) c ((mem_cells hc c).mpr (Or.inr (Or.inl rfl))) h1⟩

theorem pos_t (hg : Geo H) (hc : H.cells = s ++ c :: t) : ∀ x ∈ t, c.addr < x.addr ∧ c.next ≤ x.addr := by
  intro x hx
  have h1 := (sorted_parts hg hc).2.2.2 x hx
  exact ⟨h1, hg.disj c ((mem_cells hc c).mpr (Or.inr (Or.inl rfl))) x ((mem_cells hc x).mpr (Or.inr (Or.inr hx))) h1⟩

/-- The next neighbour of a cell that is not last comes after it. -/
theorem nbr_t (hg : Geo H) (hc : H.cells = s ++ c :: t) (hl : c.last = false) :
    ∃ d ∈ t, d.addr = c.next ∧ d.prev = c.addr := by
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  obtain ⟨d, hd, h1, h2⟩ := hg.next_nb c hcc hl
  have hb := hg.bounds c hcc
  rcases (mem_cells hc d).mp hd with hds | rfl | hdt
  · have := (pos_s hg hc d hds).1; omega
  · omega
  · exact ⟨d, hdt, h1, h2⟩

end Pos

/-! ## Whole: the listed cell allocated in place -/

/-- The listed cell, allocated. -/
def cW (c : CellM) : CellM := { c with allocated := true }

def modelW (H : HeapModel) (s t : List CellM) (c : CellM) : HeapModel :=
  { H with cells := s ++ cW c :: t, freeList := [] }

theorem wf_whole {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
    {s t : List CellM} {c : CellM} (hc : H.cells = s ++ c :: t) (hcf : c.allocated = false)
    {size : Nat} (hs0 : 0 < size) (hsz : c.addr + 8 + size ≤ c.next) (F' : Nat) :
    (modelW H s t c).wf ((c.addr + 8, size) :: live) F' := by
  have hg := hw.geo
  have hnd := nodup_of_sorted hg.sorted
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hmap : (modelW H s t c).cells = H.cells.map (upd c.addr (cW c)) := by
    show s ++ cW c :: t = H.cells.map (upd c.addr (cW c))
    rw [hc, List.map_append, List.map_cons]
    have e1 : s.map (upd c.addr (cW c)) = s := by
      refine (List.map_congr_left (g := id) ?_).trans (List.map_id s)
      intro x hx; have := (pos_s hg hc x hx).1; simp [upd, show x.addr ≠ c.addr by omega]
    have e2 : t.map (upd c.addr (cW c)) = t := by
      refine (List.map_congr_left (g := id) ?_).trans (List.map_id t)
      intro x hx; have := (pos_t hg hc x hx).1; simp [upd, show x.addr ≠ c.addr by omega]
    rw [e1, e2]; simp [upd]
  have hmem : ∀ z, z ∈ (modelW H s t c).cells ↔ z ∈ s ∨ z = cW c ∨ z ∈ t := by
    intro z; show z ∈ s ++ cW c :: t ↔ _; rw [List.mem_append, List.mem_cons]
  refine ⟨hw.mem0_al, hw.mem0_pos, hw.len_al, hw.mem0_le, hw.len_lt, ?_, lists_nil rfl, ?_, ?_⟩
  · refine geo_map hg (upd c.addr (cW c)) rfl rfl hmap ?_
    intro x hx
    unfold upd; split
    · rename_i e
      have := mem_unique hnd hx hcc e; subst this
      exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  · apply lives_gen hw.lives ((hmem _).mpr (Or.inr (Or.inl rfl))) rfl rfl hs0
      (by simp only [cW, CellM.size]; omega)
    · intro x hx hxa
      refine ⟨x, (hmem x).mpr ?_, hxa, rfl, le_refl _⟩
      rcases (mem_cells hc x).mp hx with h | rfl | h
      · exact Or.inl h
      · rw [hcf] at hxa; cases hxa
      · exact Or.inr (Or.inr h)
    · intro z hz hza
      rcases (hmem z).mp hz with h | rfl | h
      · exact Or.inr ⟨z, (mem_cells hc z).mpr (Or.inl h), hza, rfl⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨z, (mem_cells hc z).mpr (Or.inr (Or.inr h)), hza, rfl⟩
    · intro x hx hxa e
      have := mem_unique hnd hx hcc e; subst this
      rw [hcf] at hxa; cases hxa
  · intro z hz
    rcases (hmem z).mp hz with h | rfl | h
    · exact hw.nf_lo z ((mem_cells hc z).mpr (Or.inl h))
    · exact hw.nf_lo c hcc
    · exact hw.nf_lo z ((mem_cells hc z).mpr (Or.inr (Or.inr h)))

/-! ## Split: the allocated tail inserted after the listed cell -/

/-- The listed cell, shrunk to `[c, m)`. -/
def cS (c : CellM) (m : Nat) : CellM := { c with next := m, last := false }

/-- The new allocated cell `[m, c.next)`. -/
def nS (c : CellM) (m : Nat) : CellM :=
  { addr := m, next := c.next, prev := c.addr, last := c.last, allocated := true, nextFree := 0 }

/-- The cells after `c`, the next neighbour `d` (if `c` is not last) with `prev := v`. -/
def tS (c : CellM) (v : Nat) (d : CellM) (t : List CellM) : List CellM :=
  if c.last then t else t.map (upd d.addr { d with prev := v })

def modelS (H : HeapModel) (s t : List CellM) (c : CellM) (m : Nat) (d : CellM) : HeapModel :=
  { H with cells := s ++ cS c m :: nS c m :: tS c m d t }

section Split

variable {H : HeapModel} {live : List (Nat × Nat)} (hw : H.wf live 1)
  {s t : List CellM} {c d : CellM} (hc : H.cells = s ++ c :: t)
  (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr)

theorem tS_addrs (v : Nat) : (tS c v d t).map (·.addr) = t.map (·.addr) := by
  unfold tS; split
  · rfl
  · exact addrs_map_upd rfl

include hw hc hd

theorem tS_src (v : Nat) : ∀ z ∈ tS c v d t, ∃ x ∈ t, z.addr = x.addr ∧ z.next = x.next ∧ z.last = x.last ∧
    z.allocated = x.allocated ∧ z.nextFree = x.nextFree ∧
    ((z.prev = x.prev ∧ ¬(c.last = false ∧ x.addr = c.next)) ∨ (c.last = false ∧ x.addr = c.next ∧ z.prev = v)) := by
  intro z hz
  unfold tS at hz
  split at hz
  · rename_i hl
    exact ⟨z, hz, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, by simp [hl]⟩⟩
  · rename_i hl
    have hl' : c.last = false := by simpa using hl
    obtain ⟨hdt, hda, -⟩ := hd hl'
    rcases (mem_map_upd (y := { d with prev := v }) rfl ⟨d, hdt, rfl⟩).mp hz with rfl | ⟨hzt, hza⟩
    · exact ⟨d, hdt, rfl, rfl, rfl, rfl, rfl, Or.inr ⟨hl', hda, rfl⟩⟩
    · exact ⟨z, hzt, rfl, rfl, rfl, rfl, rfl, Or.inl ⟨rfl, fun h => hza (by rw [h.2, hda])⟩⟩

theorem tS_tgt (v : Nat) : ∀ x ∈ t, ∃ z ∈ tS c v d t, z.addr = x.addr ∧ z.next = x.next ∧ z.last = x.last ∧
    z.allocated = x.allocated ∧ (¬(c.last = false ∧ x.addr = c.next) → z.prev = x.prev) := by
  have hnd := nodup_of_sorted hw.geo.sorted
  intro x hx
  unfold tS
  split
  · exact ⟨x, hx, rfl, rfl, rfl, rfl, fun _ => rfl⟩
  · rename_i hl
    have hl' : c.last = false := by simpa using hl
    obtain ⟨hdt, hda, -⟩ := hd hl'
    have hxc : x ∈ H.cells := (mem_cells hc x).mpr (Or.inr (Or.inr hx))
    have hdc : d ∈ H.cells := (mem_cells hc d).mpr (Or.inr (Or.inr hdt))
    by_cases hxa : x.addr = d.addr
    · have := mem_unique hnd hxc hdc hxa; subst this
      refine ⟨{ x with prev := v }, (mem_map_upd (y := { x with prev := v }) rfl ⟨x, hx, rfl⟩).mpr (Or.inl rfl), rfl, rfl, rfl, rfl, ?_⟩
      intro h; exact absurd ⟨hl', hda⟩ h
    · exact ⟨x, (mem_map_upd (y := { d with prev := v }) rfl ⟨d, hdt, rfl⟩).mpr (Or.inr ⟨hx, hxa⟩), rfl, rfl, rfl, rfl, fun _ => rfl⟩

theorem tS_nbr (v : Nat) (hl : c.last = false) : { d with prev := v } ∈ tS c v d t := by
  obtain ⟨hdt, -, -⟩ := hd hl
  unfold tS; rw [if_neg (by simp [hl])]
  exact (mem_map_upd (y := { d with prev := v }) rfl ⟨d, hdt, rfl⟩).mpr (Or.inl rfl)

/-- `tS` with the neighbour's own `prev` is `t`. -/
theorem tS_self : tS c c.addr d t = t := by
  have hnd := nodup_of_sorted hw.geo.sorted
  unfold tS; split
  · rfl
  · rename_i hl
    have hl' : c.last = false := by simpa using hl
    obtain ⟨hdt, -, hdp⟩ := hd hl'
    have hdc : d ∈ H.cells := (mem_cells hc d).mpr (Or.inr (Or.inr hdt))
    refine (List.map_congr_left (g := id) ?_).trans (List.map_id t)
    intro x hx
    unfold upd; split
    · rename_i e
      have := mem_unique hnd ((mem_cells hc x).mpr (Or.inr (Or.inr hx))) hdc e; subst this
      rw [← hdp]; rfl
    · rfl

theorem wf_split (hfl : H.freeList = [c.addr]) (hcf : c.allocated = false) (hnf : c.nextFree = 0)
    (ha0 : 0 < c.addr) {m : Nat} (hm1 : c.addr + 12 ≤ m) (hm2 : m % 4 = 0) (hm3 : m + 12 ≤ c.next)
    {size : Nat} (hs0 : 0 < size) (hsz : m + 8 + size ≤ c.next) :
    (modelS H s t c m d).wf ((m + 8, size) :: live) 1 := by
  have hg := hw.geo
  have hnd := nodup_of_sorted hg.sorted
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hcb := hg.bounds c hcc
  have hS := pos_s hg hc
  have hT := pos_t hg hc
  have src := tS_src hw hc hd m
  have tgt := tS_tgt hw hc hd m
  have hin : ∀ x ∈ H.cells, x ≠ c → x ∈ s ∨ x ∈ t := by
    intro x hx hne
    rcases (mem_cells hc x).mp hx with h | h | h
    · exact Or.inl h
    · exact absurd h hne
    · exact Or.inr h
  have hmem : ∀ z, z ∈ (modelS H s t c m d).cells ↔ z ∈ s ∨ z = cS c m ∨ z = nS c m ∨ z ∈ tS c m d t := by
    intro z; show z ∈ s ++ cS c m :: nS c m :: tS c m d t ↔ _
    rw [List.mem_append, List.mem_cons, List.mem_cons]
  have hsS : ∀ x ∈ s, x ∈ (modelS H s t c m d).cells := fun x hx => (hmem x).mpr (Or.inl hx)
  have hcS : cS c m ∈ (modelS H s t c m d).cells := (hmem _).mpr (Or.inr (Or.inl rfl))
  have hnS : nS c m ∈ (modelS H s t c m d).cells := (hmem _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have htS : ∀ z ∈ tS c m d t, z ∈ (modelS H s t c m d).cells :=
    fun z hz => (hmem z).mpr (Or.inr (Or.inr (Or.inr hz)))
  have hsH : ∀ x ∈ s, x ∈ H.cells := fun x hx => (mem_cells hc x).mpr (Or.inl hx)
  have htH : ∀ x ∈ t, x ∈ H.cells := fun x hx => (mem_cells hc x).mpr (Or.inr (Or.inr hx))
  -- the next neighbour, when `c` is not last
  have hdd : c.last = false → { d with prev := m } ∈ (modelS H s t c m d).cells ∧ d.addr = c.next :=
    fun hl => ⟨htS _ (tS_nbr hw hc hd m hl), (hd hl).2.1⟩
  have hg' : Geo (modelS H s t c m d) := by
    constructor
    · intro z hz
      show H.mem0 ≤ z.addr ∧ z.addr + 12 ≤ z.next ∧ z.next ≤ H.len ∧ z.addr % 4 = 0
      rcases (hmem z).mp hz with h | rfl | rfl | h
      · exact hg.bounds z (hsH z h)
      · simp only [cS]; omega
      · simp only [nS]; omega
      · obtain ⟨x, hx, e1, e2, -⟩ := src z h
        have := hg.bounds x (htH x hx); rw [e1, e2]; exact this
    · intro z hz
      rcases (hmem z).mp hz with h | rfl | rfl | h
      · exact hg.next_al z (hsH z h)
      · exact hm2
      · exact hg.next_al c hcc
      · obtain ⟨x, hx, -, e2, -⟩ := src z h
        rw [e2]; exact hg.next_al x (htH x hx)
    · show ((s ++ cS c m :: nS c m :: tS c m d t).map (·.addr)).Pairwise (· < ·)
      obtain ⟨p1, p2, p3, p4⟩ := sorted_parts hg hc
      rw [List.map_append, List.map_cons, List.map_cons, tS_addrs, List.pairwise_append,
        List.pairwise_cons, List.pairwise_cons]
      refine ⟨p1, ⟨?_, ?_, p2⟩, ?_⟩
      · intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · (try simp only [nS, cS] at *); omega
        · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; simp only [cS]; exact p4 x hx
      · intro b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb; simp only [nS]; have := hT x hx; omega
      · intro a ha b hb
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
        have := p3 x hx
        rcases List.mem_cons.mp hb with rfl | hb
        · (try simp only [cS] at *); omega
        rcases List.mem_cons.mp hb with rfl | hb
        · (try simp only [nS] at *); omega
        · obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb; have := p4 y hy; omega
    · intro z hz hzl
      rcases (hmem z).mp hz with h | rfl | rfl | h
      · obtain ⟨y, hy, e1, e2⟩ := hg.next_nb z (hsH z h) hzl
        rcases (mem_cells hc y).mp hy with hy' | hyc | hy'
        · exact ⟨y, hsS y hy', e1, e2⟩
        · exact ⟨cS c m, hcS, by rw [← hyc]; exact e1, by rw [← hyc]; exact e2⟩
        · obtain ⟨z', hz', f1, -, -, -, f5⟩ := tgt y hy'
          refine ⟨z', htS z' hz', by rw [f1, e1], ?_⟩
          rw [f5]; · exact e2
          rintro ⟨hl, hya⟩
          have := (hd hl).2.2
          have := mem_unique hnd hy ((mem_cells hc d).mpr (Or.inr (Or.inr (hd hl).1))) (by rw [hya, (hd hl).2.1])
          subst this
          have := (hS z h).1; omega
      · exact ⟨nS c m, hnS, rfl, rfl⟩
      · obtain ⟨h1, h2⟩ := hdd hzl
        exact ⟨_, h1, h2, rfl⟩
      · obtain ⟨x, hx, e1, e2, e3, -, -, hp⟩ := src z h
        obtain ⟨y, hy, f1, f2⟩ := hg.next_nb x (htH x hx) (by rw [← e3]; exact hzl)
        have hxb := hg.bounds x (htH x hx)
        have hyb := hg.bounds y hy
        rcases (mem_cells hc y).mp hy with hy' | rfl | hy'
        · have := (hS y hy').1; have := (hT x hx).1; omega
        · have := (hT x hx).1; omega
        · obtain ⟨z', hz', g1, -, -, -, g5⟩ := tgt y hy'
          refine ⟨z', htS z' hz', by rw [g1, f1, e2], ?_⟩
          rw [g5, f2, e1]
          rintro ⟨hl, hya⟩
          have := mem_unique hnd hy ((mem_cells hc d).mpr (Or.inr (Or.inr (hd hl).1))) (by rw [hya, (hd hl).2.1])
          subst this
          have := (hd hl).2.2; have := (hT x hx).1; omega
    · intro z hz hzp
      rcases (hmem z).mp hz with h | rfl | rfl | h
      · obtain ⟨y, hy, e1, e2, e3⟩ := hg.prev_nb z (hsH z h) hzp
        rcases (mem_cells hc y).mp hy with hy' | rfl | hy'
        · exact ⟨y, hsS y hy', e1, e2, e3⟩
        · have := (hS z h).1; omega
        · obtain ⟨z', hz', f1, f2, f3, -⟩ := tgt y hy'
          exact ⟨z', htS z' hz', by rw [f1, e1], by rw [f2, e2], by rw [f3, e3]⟩
      · obtain ⟨y, hy, e1, e2, e3⟩ := hg.prev_nb c hcc hzp
        rcases (mem_cells hc y).mp hy with hy' | rfl | hy'
        · exact ⟨y, hsS y hy', e1, e2, e3⟩
        · omega
        · have := (hT y hy').1; have := hg.bounds y hy; omega
      · exact ⟨cS c m, hcS, rfl, rfl, rfl⟩
      · obtain ⟨x, hx, e1, -, -, -, -, hp⟩ := src z h
        rcases hp with ⟨hp, hnot⟩ | ⟨hl, hxa, hzp'⟩
        · obtain ⟨y, hy, f1, f2, f3⟩ := hg.prev_nb x (htH x hx) (by rw [← hp]; exact hzp)
          rcases (mem_cells hc y).mp hy with hy' | rfl | hy'
          · exact ⟨y, hsS y hy', by rw [f1, hp], by rw [f2, e1], f3⟩
          · exact absurd ⟨f3, f2.symm⟩ hnot
          · obtain ⟨z', hz', g1, g2, g3, -⟩ := tgt y hy'
            exact ⟨z', htS z' hz', by rw [g1, f1, hp], by rw [g2, f2, e1], by rw [g3, f3]⟩
        · exact ⟨nS c m, hnS, by rw [hzp']; rfl, by rw [e1, hxa]; rfl, by simp [nS, hl]⟩
    · intro z hz hzp
      rcases (hmem z).mp hz with h | rfl | rfl | h
      · exact hg.first z (hsH z h) hzp
      · exact hg.first c hcc hzp
      · simp [nS] at hzp; omega
      · obtain ⟨x, hx, e1, -, -, -, -, hp⟩ := src z h
        rcases hp with ⟨hp, -⟩ | ⟨-, -, hzp'⟩
        · rw [e1]; exact hg.first x (htH x hx) (by rw [← hp]; exact hzp)
        · omega
    · intro x hx y hy hxy
      -- every new cell has an old one with the same bounds, or is one of the two halves of `c`
      have key : ∀ z ∈ (modelS H s t c m d).cells, (∃ w ∈ H.cells, w ≠ c ∧ w.addr = z.addr ∧ w.next = z.next) ∨
          z = cS c m ∨ z = nS c m := by
        intro z hz
        rcases (hmem z).mp hz with h | rfl | rfl | h
        · refine Or.inl ⟨z, hsH z h, ?_, rfl, rfl⟩
          rintro rfl; have := (hS _ h).1; omega
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr rfl)
        · obtain ⟨w, hw', e1, e2, -⟩ := src z h
          refine Or.inl ⟨w, htH w hw', ?_, e1.symm, e2.symm⟩
          rintro rfl; have := (hT _ hw').1; omega
      have side : ∀ w ∈ H.cells, w ≠ c → (w.addr < c.addr ∧ w.next ≤ c.addr) ∨ c.next ≤ w.addr := by
        intro w hw' hne
        rcases hin w hw' hne with h | h
        · exact Or.inl (hS w h)
        · exact Or.inr (hT w h).2
      rcases key x hx with ⟨w, hw', hwc, e1, e2⟩ | rfl | rfl <;>
        rcases key y hy with ⟨w', hw'', hwc', f1, f2⟩ | rfl | rfl
      · rw [← e2, ← f1]; exact hg.disj w hw' w' hw'' (by omega)
      · have := side w hw' hwc; simp only [cS] at hxy ⊢; omega
      · have := side w hw' hwc; simp only [nS] at hxy ⊢; omega
      · have := side w' hw'' hwc'; simp only [cS] at hxy ⊢; omega
      · omega
      · simp only [cS, nS]; omega
      · have := side w' hw'' hwc'; simp only [nS] at hxy ⊢; omega
      · simp only [cS, nS] at hxy; omega
      · omega
  refine ⟨hw.mem0_al, hw.mem0_pos, hw.len_al, hw.mem0_le, hw.len_lt, hg', ?_, ?_, ?_⟩
  · apply lists_one (H := modelS H s t c m d) (c := cS c m) (by exact hfl) _ hcf hnf
    exact (cellAt_iff' (nodup_of_sorted hg'.sorted)).mpr ⟨hcS, rfl⟩
  · apply lives_gen hw.lives hnS rfl rfl hs0 (by simp only [nS, CellM.size]; omega)
    · intro x hx hxa
      rcases (mem_cells hc x).mp hx with h | rfl | h
      · exact ⟨x, hsS x h, hxa, rfl, le_refl _⟩
      · rw [hcf] at hxa; cases hxa
      · obtain ⟨z, hz, f1, f2, -, f4, -⟩ := tgt x h
        exact ⟨z, htS z hz, by rw [f4]; exact hxa, f1, by simp only [CellM.size]; omega⟩
    · intro z hz hza
      rcases (hmem z).mp hz with h | rfl | rfl | h
      · exact Or.inr ⟨z, hsH z h, hza, rfl⟩
      · simp [cS, hcf] at hza
      · exact Or.inl rfl
      · obtain ⟨x, hx, e1, -, -, e4, -⟩ := src z h
        exact Or.inr ⟨x, htH x hx, by rw [← e4]; exact hza, e1.symm⟩
    · intro x hx hxa e
      rcases (mem_cells hc x).mp hx with h | rfl | h
      · have := (hS x h).1; simp only [nS] at e; omega
      · rw [hcf] at hxa; cases hxa
      · have := (hT x h).2; simp only [nS] at e; omega
  · intro z hz
    rcases (hmem z).mp hz with h | rfl | rfl | h
    · exact hw.nf_lo z (hsH z h)
    · exact hw.nf_lo c hcc
    · simp [nS]
    · obtain ⟨x, hx, -, -, -, -, e5, -⟩ := src z h
      rw [e5]; exact hw.nf_lo x (htH x hx)

end Split

end WNear.Binary.AllocSeqModel
