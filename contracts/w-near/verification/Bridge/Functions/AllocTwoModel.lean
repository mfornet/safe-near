import Bridge.Functions.AllocSeqPack

/-!
# The heap models of an allocation from a two-cell free list (M4)

`heapInv … 2` allows a free list `[a, b]` (what one `dealloc` leaves on a list of one cell).
`two_facts`: `b`'s `next_free` is 0, `a`'s is `b` or `b | CAN_MERGE`, and in the latter case `b`
is `a`'s previous neighbour. The models after 580's walk:

* `skipM` (`a` too small, unlinked and leaked): the same cells, the list `[b]` (`wf_skip`);
* `modelW2` (`a` taken whole): `a` allocated, the list `[b]` (`wf_whole2`, from
  `AllocSeqModel.wf_whole`);
* `modelS` with the list `[a, b]` (`a` split): `wf_split2`, `AllocSeqModel.wf_split` for any
  bound `F` and a list kept by `AllocDealloc.lists_same`;
* the merge of `a` into `b`: `AllocDealloc`'s case A (`modelA1`, `modelA2`) applied to the model
  where `a` is marked allocated (`starM`, `wf_star`), the list `[b]` (`wf_merged1`/`2`).
-/

namespace WNear.Binary.AllocTwo

open WNear.Binary.AllocInv WNear.Binary.AllocSeqModel
open WNear.Binary.AllocDealloc (upd mem_map_upd addrs_map_upd nodup_of_sorted cellAt_iff cellAt_iff' mem_unique
  geo_map lists_same Keeps)
open WNear.Binary.AllocFresh (lists_one lists_nil)

/-- What a two-cell free list `[a, b]` says about its cells. -/
theorem two_facts {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) {a b : Nat}
    (hfl : H.freeList = [a, b]) :
    ∃ ca cb, H.cellAt a = some ca ∧ H.cellAt b = some cb ∧ ca.allocated = false ∧ cb.allocated = false ∧
      a ≠ b ∧ cb.nextFree = 0 ∧ (ca.nextFree = b ∨ (ca.nextFree = b + 1 ∧ ca.prev = b)) := by
  have hl := hw.lists
  have hnd := nodup_of_sorted hw.geo.sorted
  obtain ⟨ca, hca, hcaf⟩ := hl.fl_free a (by simp [hfl])
  obtain ⟨cb, hcb, hcbf⟩ := hl.fl_free b (by simp [hfl])
  have hab : a ≠ b := by
    have := hl.fl_nodup; rw [hfl] at this; simpa using this
  have h0 : (0 : Nat) < H.freeList.length := by simp [hfl]
  have h1 : (1 : Nat) < H.freeList.length := by simp [hfl]
  obtain ⟨ca', hca', hla⟩ := hl.fl_link 0 h0
  obtain ⟨cb', hcb', hlb⟩ := hl.fl_link 1 h1
  have e0 : H.freeList[0] = a := by simp [hfl]
  have e1 : H.freeList[1] = b := by simp [hfl]
  rw [e0, hca] at hca'; cases hca'
  rw [e1, hcb] at hcb'; cases hcb'
  have g0 : H.freeList.getD (0 + 1) 0 = b := by simp [hfl]
  have g1 : H.freeList.getD (1 + 1) 0 = 0 := by simp [hfl]
  rw [g0] at hla; rw [g1] at hlb
  have hca_m := (cellAt_iff' hnd).mp hca
  have hcb_m := (cellAt_iff' hnd).mp hcb
  have loa := hw.nf_lo ca hca_m.1
  have lob := hw.nf_lo cb hcb_m.1
  have hbo : cb.nextFree % 2 = 0 := by
    by_contra hne
    obtain ⟨d, hd, -⟩ := hl.fl_merge 1 h1 cb (by rw [e1]; exact hcb) (by omega)
    simp [hfl] at hd
  refine ⟨ca, cb, hca, hcb, hcaf, hcbf, hab, by omega, ?_⟩
  by_cases hao : ca.nextFree % 2 = 1
  · obtain ⟨d, hd, hd2, -, hd4⟩ := hl.fl_merge 0 h0 ca (by rw [e0]; exact hca) hao
    have : d.addr = b := by simpa [hfl] using hd.symm
    exact Or.inr ⟨by omega, by rw [hd4, this]⟩
  · exact Or.inl (by omega)

/-! ## `a` unlinked -/

/-- `a` unlinked: the same cells, the list `[b]`. -/
def skipM (H : HeapModel) (b : Nat) : HeapModel := { H with freeList := [b] }

theorem wf_skip {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) {b : Nat} {cb : CellM}
    (hcb : H.cellAt b = some cb) (hcbf : cb.allocated = false) (hnf : cb.nextFree = 0) :
    (skipM H b).wf live 1 :=
  ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt,
    ⟨hw.geo.bounds, hw.geo.next_al, hw.geo.sorted, hw.geo.next_nb, hw.geo.prev_nb, hw.geo.first, hw.geo.disj⟩,
    lists_one (H := skipM H b) rfl hcb hcbf hnf,
    ⟨hw.lives.live_cell, hw.lives.cell_live, hw.lives.live_nodup⟩, hw.nf_lo⟩

/-! ## `a` taken whole -/

def modelW2 (H : HeapModel) (s t : List CellM) (c : CellM) (b : Nat) : HeapModel :=
  { H with cells := s ++ cW c :: t, freeList := [b] }

theorem wf_whole2 {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
    {s t : List CellM} {c : CellM} (hc : H.cells = s ++ c :: t) (hcf : c.allocated = false)
    {size : Nat} (hs0 : 0 < size) (hsz : c.addr + 8 + size ≤ c.next) {b : Nat} {cb : CellM}
    (hcb : H.cellAt b = some cb) (hcbf : cb.allocated = false) (hnf : cb.nextFree = 0) (hbc : b ≠ c.addr) :
    (modelW2 H s t c b).wf ((c.addr + 8, size) :: live) 1 := by
  have h := wf_whole hw hc hcf hs0 hsz 1
  have hnd := nodup_of_sorted hw.geo.sorted
  obtain ⟨hcbm, hcba⟩ := (cellAt_iff' hnd).mp hcb
  have hcb' : (modelW2 H s t c b).cellAt b = some cb := by
    apply (cellAt_iff' (nodup_of_sorted h.geo.sorted)).mpr
    refine ⟨?_, hcba⟩
    show cb ∈ s ++ cW c :: t
    rw [hc] at hcbm
    rcases List.mem_append.mp hcbm with h1 | h1
    · exact List.mem_append_left _ h1
    · rcases List.mem_cons.mp h1 with rfl | h2
      · exact absurd hcba.symm hbc
      · exact List.mem_append_right _ (List.mem_cons_of_mem _ h2)
  exact ⟨h.mem0_al, h.len_al, h.mem0_le, h.len_lt,
    ⟨h.geo.bounds, h.geo.next_al, h.geo.sorted, h.geo.next_nb, h.geo.prev_nb, h.geo.first, h.geo.disj⟩,
    lists_one (H := modelW2 H s t c b) rfl hcb' hcbf hnf,
    ⟨h.lives.live_cell, h.lives.cell_live, h.lives.live_nodup⟩, h.nf_lo⟩

/-! ## `a` split: `AllocSeqModel.wf_split` for any bound, the list kept -/

section Split

variable {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
  {s t : List CellM} {c d : CellM} (hc : H.cells = s ++ c :: t)
  (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr)

theorem tS_addrs2 (v : Nat) : (tS c v d t).map (·.addr) = t.map (·.addr) := by
  unfold tS; split
  · rfl
  · exact addrs_map_upd rfl

include hw hc hd

theorem tS_src2 (v : Nat) : ∀ z ∈ tS c v d t, ∃ x ∈ t, z.addr = x.addr ∧ z.next = x.next ∧ z.last = x.last ∧
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

theorem tS_tgt2 (v : Nat) : ∀ x ∈ t, ∃ z ∈ tS c v d t, z.addr = x.addr ∧ z.next = x.next ∧ z.last = x.last ∧
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

theorem tS_nbr2 (v : Nat) (hl : c.last = false) : { d with prev := v } ∈ tS c v d t := by
  obtain ⟨hdt, -, -⟩ := hd hl
  unfold tS; rw [if_neg (by simp [hl])]
  exact (mem_map_upd (y := { d with prev := v }) rfl ⟨d, hdt, rfl⟩).mpr (Or.inl rfl)

/-- `tS` with the neighbour's own `prev` is `t`. -/
theorem tS_self2 : tS c c.addr d t = t := by
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

theorem wf_split2 (hcf : c.allocated = false)
    (hnm : ∀ x ∈ t, x.addr ∈ H.freeList → x.nextFree % 2 = 0)
    (ha0 : 0 < c.addr) {m : Nat} (hm1 : c.addr + 12 ≤ m) (hm2 : m % 4 = 0) (hm3 : m + 12 ≤ c.next)
    {size : Nat} (hs0 : 0 < size) (hsz : m + 8 + size ≤ c.next) :
    (modelS H s t c m d).wf ((m + 8, size) :: live) F := by
  have hg := hw.geo
  have hnd := nodup_of_sorted hg.sorted
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hcb := hg.bounds c hcc
  have hS := pos_s hg hc
  have hT := pos_t hg hc
  have src := tS_src2 hw hc hd m
  have tgt := tS_tgt2 hw hc hd m
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
    fun hl => ⟨htS _ (tS_nbr2 hw hc hd m hl), (hd hl).2.1⟩
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
      rw [List.map_append, List.map_cons, List.map_cons, tS_addrs2, List.pairwise_append,
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
  refine ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt, hg', ?_, ?_, ?_⟩
  · have hnd' := nodup_of_sorted hg'.sorted
    apply lists_same (H := H) hw.lists _ hnd hnd' (le_refl F)
    intro x hx hxl
    rcases (mem_cells hc x).mp hx with h | rfl | h
    · exact ⟨x, (hmem x).mpr (Or.inl h), rfl, rfl, rfl, fun _ => rfl⟩
    · exact ⟨cS x m, hcS, rfl, rfl, rfl, fun _ => rfl⟩
    · obtain ⟨z, hz, f1, -, -, f4, -⟩ := tgt x h
      obtain ⟨x2, hx2, g1, -, -, -, g5, -⟩ := src z hz
      have e : x2 = x := mem_unique hnd (htH x2 hx2) (htH x h) (by rw [← g1, f1])
      subst e
      exact ⟨z, htS z hz, f1, f4, g5, fun hodd => absurd hodd (by have := hnm x2 h hxl; omega)⟩
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

/-! ## The merge of `a` into `b` -/

/-- A bound on the free list is any number at least its length. -/
theorem wf_relen {H : HeapModel} {live : List (Nat × Nat)} {F F' : Nat} (hw : H.wf live F)
    (h : H.freeList.length ≤ F') : H.wf live F' :=
  { hw with lists := { hw.lists with fl_len := h } }

/-- `a` marked allocated (lent whole), the list `[b]`: the model case A of `dealloc` starts from. -/
def starM (H : HeapModel) (ca : CellM) (b : Nat) : HeapModel :=
  { H with cells := H.cells.map (upd ca.addr { ca with allocated := true }), freeList := [b] }

theorem wf_star {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) {ca cb : CellM}
    (hca : ca ∈ H.cells) (hcaf : ca.allocated = false) (hcb : cb ∈ H.cells) (hcbf : cb.allocated = false)
    (hnf : cb.nextFree = 0) (hab : cb.addr ≠ ca.addr) :
    (starM H ca cb.addr).wf ((ca.addr + 8, ca.size) :: live) 1 := by
  have hg := hw.geo
  have hnd := nodup_of_sorted hg.sorted
  have hb := hg.bounds ca hca
  have hmem := fun z => mem_map_upd (L := H.cells) (z := z) (a := ca.addr) (y := { ca with allocated := true })
    rfl ⟨ca, hca, rfl⟩
  have hcells : (starM H ca cb.addr).cells = H.cells.map (upd ca.addr { ca with allocated := true }) := rfl
  have hstar : { ca with allocated := true } ∈ (starM H ca cb.addr).cells := by
    rw [hcells]; exact (hmem _).mpr (Or.inl rfl)
  have hold : ∀ x ∈ H.cells, x.addr ≠ ca.addr → x ∈ (starM H ca cb.addr).cells := by
    intro x hx hxa; rw [hcells]; exact (hmem x).mpr (Or.inr ⟨hx, hxa⟩)
  have hg' : Geo (starM H ca cb.addr) := by
    refine geo_map hg (upd ca.addr { ca with allocated := true }) rfl rfl hcells ?_
    intro x hx; unfold upd; split
    · rename_i e; obtain rfl := mem_unique hnd hx hca e; exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt, hg', ?_, ?_, ?_⟩
  · apply lists_one (H := starM H ca cb.addr) rfl _ hcbf hnf
    exact (cellAt_iff' (nodup_of_sorted hg'.sorted)).mpr ⟨hold cb hcb hab, rfl⟩
  · have hs0 : 0 < ca.size := by unfold CellM.size; omega
    apply lives_gen (a := ca.addr) (s := ca.size) hw.lives hstar rfl rfl hs0 (le_refl _)
    · intro x hx hxa
      have hxc : x.addr ≠ ca.addr := fun e => by
        obtain rfl := mem_unique hnd hx hca e; rw [hcaf] at hxa; cases hxa
      exact ⟨x, hold x hx hxc, hxa, rfl, le_refl _⟩
    · intro z hz hza
      rw [hcells] at hz
      rcases (hmem z).mp hz with rfl | ⟨hz', hza'⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨z, hz', hza, rfl⟩
    · intro x hx hxa e
      obtain rfl := mem_unique hnd hx hca e; rw [hcaf] at hxa; cases hxa
  · intro z hz
    rw [hcells] at hz
    rcases (hmem z).mp hz with rfl | ⟨hz', -⟩
    · exact hw.nf_lo ca hca
    · exact hw.nf_lo z hz'

section Merged

open WNear.Binary.AllocDealloc (cellA nbrA modelA1 modelA2 wf_caseA1 wf_caseA2)

/-- `b` grown to `a`'s end. -/
def bM (cb ca : CellM) : CellM := { cb with next := ca.next, last := ca.last }

/-- The merged model: `a` gone, `b` grown, `a`'s next neighbour `m` (if any) with `prev = b`. -/
def mergedM (H : HeapModel) (s t : List CellM) (cb ca : CellM) : HeapModel :=
  { H with cells := s ++ bM cb ca :: (match t with
      | [] => []
      | m :: t' => if ca.last then m :: t' else { m with prev := cb.addr } :: t'), freeList := [cb.addr] }

theorem map_upd_out {L : List CellM} {a : Nat} {y : CellM} (h : ∀ x ∈ L, x.addr ≠ a) : L.map (upd a y) = L := by
  refine (List.map_congr_left (g := id) ?_).trans (List.map_id L)
  intro x hx; simp [upd, h x hx]

variable {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
  {s t : List CellM} {cb ca : CellM} (hc : H.cells = s ++ cb :: ca :: t)
include hw hc

theorem mergedM_pos : (∀ x ∈ s, x.addr < cb.addr) ∧ cb.addr < ca.addr ∧ (∀ x ∈ t, ca.addr < x.addr) := by
  have hs := hw.geo.sorted
  rw [hc, List.map_append, List.map_cons, List.map_cons, List.pairwise_append, List.pairwise_cons,
    List.pairwise_cons] at hs
  refine ⟨fun x hx => hs.2.2 _ (List.mem_map_of_mem hx) _ List.mem_cons_self, hs.2.1.1 _ List.mem_cons_self, ?_⟩
  intro x hx; exact hs.2.1.2.1 _ (List.mem_map_of_mem hx)

theorem star_cells : ((starM H ca cb.addr).cells.erase { ca with allocated := true }).map
    (upd cb.addr (cellA cb { ca with allocated := true })) = s ++ bM cb ca :: t := by
  obtain ⟨hS, hba, hT⟩ := mergedM_pos hw hc
  have e1 : (starM H ca cb.addr).cells = s ++ cb :: { ca with allocated := true } :: t := by
    show H.cells.map _ = _
    rw [hc, List.map_append, List.map_cons, List.map_cons, map_upd_out (fun x hx => by have := hS x hx; omega),
      map_upd_out (fun x hx => by have := hT x hx; omega)]
    simp [upd, show cb.addr ≠ ca.addr by omega]
  rw [e1, List.erase_append_right _ (fun h => by have := hS _ h; simp at this; omega),
    List.erase_cons_tail (by simp; intro h; have := congrArg CellM.addr h; simp at this; omega),
    List.erase_cons_head, List.map_append, List.map_cons,
    map_upd_out (fun x hx => by have := hS x hx; omega), map_upd_out (fun x hx => by have := hT x hx; omega)]
  simp [upd, bM, cellA]

/-- The merged model, `a` the last cell of its chunk. -/
theorem wf_merged1 (hcaf : ca.allocated = false) (hcbf : cb.allocated = false) (hnf : cb.nextFree = 0)
    (hpa : ca.prev = cb.addr) (hp0 : ca.prev ≠ 0) (hlast : ca.last = true) :
    (mergedM H s t cb ca).wf live 1 := by
  obtain ⟨hS, hba, hT⟩ := mergedM_pos hw hc
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have hst := wf_star hw hca hcaf hcb hcbf hnf (by omega)
  have hstc : { ca with allocated := true } ∈ (starM H ca cb.addr).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨ca, hca, by simp [upd]⟩
  have hstb : cb ∈ (starM H ca cb.addr).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨cb, hcb, by simp [upd, show cb.addr ≠ ca.addr by omega]⟩
  have h := wf_caseA1 hst hstc rfl List.mem_cons_self hstb hpa.symm hp0 hcbf hlast
  rw [List.erase_cons_head] at h
  have hcl : (modelA1 (starM H ca cb.addr) { ca with allocated := true } cb).cells =
      (mergedM H s t cb ca).cells := by
    show ((starM H ca cb.addr).cells.erase _).map _ = _
    rw [star_cells hw hc]
    show s ++ bM cb ca :: t = s ++ bM cb ca :: _
    cases t with
    | nil => rfl
    | cons m t' => simp [hlast]
  have e : modelA1 (starM H ca cb.addr) { ca with allocated := true } cb = mergedM H s t cb ca := by
    cases hm : modelA1 (starM H ca cb.addr) { ca with allocated := true } cb
    rw [hm] at hcl
    simp only [mergedM] at hcl ⊢
    rw [← hcl]
    have := congrArg HeapModel.freeList hm
    have h0 := congrArg HeapModel.mem0 hm
    have h1 := congrArg HeapModel.len hm
    simp [modelA1, starM] at this h0 h1
    simp [this, h0, h1]
  rw [e] at h
  exact wf_relen h (by simp [mergedM])

/-- The merged model, `a` followed by `m` in its chunk. -/
theorem wf_merged2 (hcaf : ca.allocated = false) (hcbf : cb.allocated = false) (hnf : cb.nextFree = 0)
    (hpa : ca.prev = cb.addr) (hp0 : ca.prev ≠ 0) (hlast : ca.last = false) {m : CellM} {t' : List CellM}
    (ht : t = m :: t') (hmaddr : m.addr = ca.next) (hmprev : m.prev = ca.addr) :
    (mergedM H s t cb ca).wf live 1 := by
  obtain ⟨hS, hba, hT⟩ := mergedM_pos hw hc
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have hcm : m ∈ H.cells := by rw [hc, ht]; simp
  have hma : m.addr ≠ ca.addr := by have := hT m (by rw [ht]; simp); omega
  have hst := wf_star hw hca hcaf hcb hcbf hnf (by omega)
  have hstc : { ca with allocated := true } ∈ (starM H ca cb.addr).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨ca, hca, by simp [upd]⟩
  have hstb : cb ∈ (starM H ca cb.addr).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨cb, hcb, by simp [upd, show cb.addr ≠ ca.addr by omega]⟩
  have hstm : m ∈ (starM H ca cb.addr).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨m, hcm, by simp [upd, hma]⟩
  have h := wf_caseA2 hst hstc rfl List.mem_cons_self hstb hpa.symm hp0 hcbf hstm hmaddr hlast hmprev
  rw [List.erase_cons_head] at h
  have hcl : (modelA2 (starM H ca cb.addr) { ca with allocated := true } cb m).cells =
      (mergedM H s t cb ca).cells := by
    show (((starM H ca cb.addr).cells.erase _).map _).map _ = _
    rw [star_cells hw hc, ht]
    have hT' : ∀ x ∈ t', x.addr ≠ m.addr := by
      intro x hx
      have hs := hw.geo.sorted
      rw [hc, ht, List.map_append, List.map_cons, List.map_cons, List.map_cons, List.pairwise_append,
        List.pairwise_cons, List.pairwise_cons, List.pairwise_cons] at hs
      have := hs.2.1.2.2.1 _ (List.mem_map_of_mem hx); omega
    have hbm : (bM cb ca).addr ≠ m.addr := by
      have := hT m (by rw [ht]; simp); simp only [bM]; omega
    simp only [mergedM, hlast, List.map_append, List.map_cons, Bool.false_eq_true, ↓reduceIte]
    rw [map_upd_out (fun x hx => by have := hS x hx; have := hT m (by rw [ht]; simp); omega),
      map_upd_out hT']
    simp [upd, hbm, nbrA]
  have e : modelA2 (starM H ca cb.addr) { ca with allocated := true } cb m = mergedM H s t cb ca := by
    cases hm : modelA2 (starM H ca cb.addr) { ca with allocated := true } cb m
    rw [hm] at hcl
    simp only [mergedM] at hcl ⊢
    rw [← hcl]
    have := congrArg HeapModel.freeList hm
    have h0 := congrArg HeapModel.mem0 hm
    have h1 := congrArg HeapModel.len hm
    simp [modelA2, starM] at this h0 h1
    simp [this, h0, h1]
  rw [e] at h
  exact wf_relen h (by simp [mergedM])

end Merged

end WNear.Binary.AllocTwo
