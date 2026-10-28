import Bridge.Functions.AllocTwoModel

/-!
# The heap models of 580's walk over any free list (M4)

`AllocTwoModel` gives the models after a walk over a free list of two cells. This file gives the
models of one step of the walk over any list `a :: rest` (the cells `s ++ c :: t`, `c` at `a`):

* `head_facts`: `c` is free; without `CAN_MERGE` its `next_free` is the next listed cell (or 0),
  with `CAN_MERGE` it is `b + 1` where `b :: rest' = rest` and `b` is `c`'s free previous
  neighbour (`prev_split`: the cells are `s ++ cb :: c :: t`);
* *unlinked* (`c` too small, or not splittable and misaligned): the same cells, the list `rest`
  (`wf_tail`, `c` leaked);
* *merged* (`CAN_MERGE`): `AllocTwo.mergedM`'s cells, the list `rest` (`b` first) (`wf_mergedG`),
  through `AllocDealloc`'s case A on the model where `c` is lent whole and nothing is listed
  (`starE`, `wf_mergedE1/2`);
* *whole*: `c` allocated, the list `rest` (`wf_wholeG`);
* *split*: `modelS`, the list kept (`wf_splitG`): `AllocTwo.wf_split2` on the model with an empty
  list, the list put back by `lists_same` (`merge_prev_ne_head`: a listed cell with `CAN_MERGE`
  never has the list's head as previous neighbour, so the next neighbour's new `prev` is harmless).

Every step keeps the bound `F` on the list; unlink and merge shorten the list by one.
-/

namespace WNear.Binary.AllocWalk

open WNear.Binary.AllocInv WNear.Binary.AllocSeqModel WNear.Binary.AllocTwo
open WNear.Binary.AllocDealloc (upd mem_map_upd addrs_map_upd nodup_of_sorted cellAt_iff cellAt_iff' mem_unique
  geo_map lists_same lists_of_q Keeps nodup_get_inj cellA nbrA modelA1 modelA2 wf_caseA1 wf_caseA2)
open WNear.Binary.AllocFresh (lists_nil)

/-! ## The list's tail -/

theorem lists_tail {H : HeapModel} {F : Nat} (hw : Lists H F) {a : Nat} {rest : List Nat}
    (hfl : H.freeList = a :: rest) : Lists { H with freeList := rest } F := by
  have e : ∀ j, rest[j]? = H.freeList[j + 1]? := fun j => by rw [hfl]; rfl
  apply lists_of_q (H := { H with freeList := rest })
  · have := hw.fl_nodup; rw [hfl] at this; exact (List.nodup_cons.mp this).2
  · have := hw.fl_len; rw [hfl] at this; simp only [List.length_cons] at this; simp only; omega
  · intro b hb; exact hw.fl_free b (by rw [hfl]; exact List.mem_cons_of_mem _ hb)
  · intro j b hj
    simp only at hj ⊢
    rw [e] at hj; rw [e]
    exact hw.link_q (j + 1) b hj
  · intro j b hj c hc hm
    simp only at hj ⊢
    rw [e] at hj
    obtain ⟨d, h1, h2, h3, h4⟩ := hw.merge_q (j + 1) b hj c hc hm
    exact ⟨d, by rw [e]; exact h1, h2, h3, h4⟩

/-- The list's head unlinked (and leaked): the same cells, the list `rest`. -/
theorem wf_tail {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) {a : Nat}
    {rest : List Nat} (hfl : H.freeList = a :: rest) : ({ H with freeList := rest } : HeapModel).wf live F :=
  ⟨hw.mem0_al, hw.mem0_pos, hw.len_al, hw.mem0_le, hw.len_lt,
    ⟨hw.geo.bounds, hw.geo.next_al, hw.geo.sorted, hw.geo.next_nb, hw.geo.prev_nb, hw.geo.first, hw.geo.disj⟩,
    lists_tail hw.lists hfl, ⟨hw.lives.live_cell, hw.lives.cell_live, hw.lives.live_nodup⟩, hw.nf_lo⟩

/-- The same cells, nothing listed. -/
theorem wf_nil {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) (F' : Nat) :
    ({ H with freeList := [] } : HeapModel).wf live F' :=
  ⟨hw.mem0_al, hw.mem0_pos, hw.len_al, hw.mem0_le, hw.len_lt,
    ⟨hw.geo.bounds, hw.geo.next_al, hw.geo.sorted, hw.geo.next_nb, hw.geo.prev_nb, hw.geo.first, hw.geo.disj⟩,
    lists_nil rfl, ⟨hw.lives.live_cell, hw.lives.cell_live, hw.lives.live_nodup⟩, hw.nf_lo⟩

/-! ## The listed head -/

/-- What the list `a :: rest` says about its head's cell. -/
theorem head_facts {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) {a : Nat}
    {rest : List Nat} (hfl : H.freeList = a :: rest) :
    ∃ ca, H.cellAt a = some ca ∧ ca.allocated = false ∧
      (ca.nextFree % 2 = 0 → ca.nextFree = rest.headD 0) ∧
      (ca.nextFree % 2 = 1 → ∃ cb rest', rest = cb.addr :: rest' ∧ H.cellAt cb.addr = some cb ∧
        cb.allocated = false ∧ ca.prev = cb.addr ∧ ca.nextFree = cb.addr + 1) := by
  have hl := hw.lists
  have hnd := nodup_of_sorted hw.geo.sorted
  obtain ⟨ca, hca, hcaf⟩ := hl.fl_free a (by simp [hfl])
  have h0 : (0 : Nat) < H.freeList.length := by simp [hfl]
  obtain ⟨ca', hca', hla⟩ := hl.fl_link 0 h0
  have e0 : H.freeList[0] = a := by simp [hfl]
  rw [e0, hca] at hca'; cases hca'
  have g0 : H.freeList.getD (0 + 1) 0 = rest.headD 0 := by rw [hfl]; cases rest <;> rfl
  rw [g0] at hla
  have lo := hw.nf_lo ca ((cellAt_iff' hnd).mp hca).1
  refine ⟨ca, hca, hcaf, fun h => by omega, fun h => ?_⟩
  obtain ⟨d, hd, hd2, hd3, hd4⟩ := hl.fl_merge 0 h0 ca (by rw [e0]; exact hca) h
  have hr : rest[0]? = some d.addr := by rw [hfl] at hd; exact hd
  cases rest with
  | nil => simp at hr
  | cons b rest' =>
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hr
    subst hr
    refine ⟨d, rest', rfl, hd2, hd3, hd4, ?_⟩
    simp only [List.headD_cons] at hla
    omega

/-- The free previous neighbour `cb` of `ca` (its `next` is `ca`) comes right before it. -/
theorem prev_split {H : HeapModel} (hg : Geo H) {s0 t : List CellM} {ca cb : CellM}
    (hc : H.cells = s0 ++ ca :: t) (hcb : cb ∈ H.cells) (hbn : cb.next = ca.addr) :
    ∃ s, H.cells = s ++ cb :: ca :: t := by
  have hbb := hg.bounds cb hcb
  have hcbs : cb ∈ s0 := by
    rcases (mem_cells hc cb).mp hcb with h | rfl | h
    · exact h
    · omega
    · have := (pos_t hg hc cb h).1; omega
  obtain ⟨p1, -, p3, -⟩ := sorted_parts hg hc
  rcases List.eq_nil_or_concat s0 with rfl | ⟨s, x, rfl⟩
  · simp at hcbs
  · simp only [List.concat_eq_append] at hc hcbs p1 p3
    refine ⟨s, ?_⟩
    rw [hc]
    by_cases hx : x = cb
    · subst hx; simp
    · exfalso
      have hcbs' : cb ∈ s := by
        rcases List.mem_append.mp hcbs with h | h
        · exact h
        · simp at h; exact absurd h.symm hx
      rw [List.map_append, List.pairwise_append] at p1
      have hlt : cb.addr < x.addr := p1.2.2 _ (List.mem_map_of_mem hcbs') _ (by simp)
      have hxm : x ∈ H.cells := (mem_cells hc x).mpr (Or.inl (by simp))
      have := hg.disj cb hcb x hxm hlt
      have := p3 x (by simp)
      omega

/-- The next neighbour of a cell that is not last is the first cell after it. -/
theorem next_head {H : HeapModel} (hg : Geo H) {s t : List CellM} {c : CellM}
    (hc : H.cells = s ++ c :: t) (hl : c.last = false) :
    ∃ m t', t = m :: t' ∧ m.addr = c.next ∧ m.prev = c.addr := by
  obtain ⟨d, hdt, hda, hdp⟩ := nbr_t hg hc hl
  obtain ⟨-, p2, -, -⟩ := sorted_parts hg hc
  cases t with
  | nil => simp at hdt
  | cons m t' =>
    refine ⟨m, t', rfl, ?_⟩
    rcases List.mem_cons.mp hdt with rfl | hdt'
    · exact ⟨hda, hdp⟩
    · exfalso
      have := (pos_t hg hc m (by simp)).2
      rw [List.map_cons, List.pairwise_cons] at p2
      have := p2.1 _ (List.mem_map_of_mem hdt')
      omega

/-- A listed cell with `CAN_MERGE` never has the list's head as previous neighbour. -/
theorem merge_prev_ne_head {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
    {a : Nat} {rest : List Nat} (hfl : H.freeList = a :: rest) {x : CellM} (hx : x ∈ H.cells)
    (hxl : x.addr ∈ H.freeList) (hodd : x.nextFree % 2 = 1) : x.prev ≠ a := by
  intro hpa
  have hnd := nodup_of_sorted hw.geo.sorted
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hxl
  obtain ⟨d, hd1, -, -, hd4⟩ := hw.lists.merge_q i _ hi x ((cellAt_iff' hnd).mpr ⟨hx, rfl⟩) hodd
  have h0 : H.freeList[0]? = some d.addr := by rw [hfl, ← hd4, hpa]; rfl
  have := nodup_get_inj hw.lists.fl_nodup hd1 h0
  omega

/-! ## Whole: the head allocated, the list's tail -/

/-- The head `c` allocated in place, the list `rest`. -/
def modelWG (H : HeapModel) (s t : List CellM) (c : CellM) (rest : List Nat) : HeapModel :=
  { H with cells := s ++ cW c :: t, freeList := rest }

theorem wf_wholeG {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
    {s t : List CellM} {c : CellM} (hc : H.cells = s ++ c :: t) (hcf : c.allocated = false)
    {rest : List Nat} (hfl : H.freeList = c.addr :: rest)
    {size : Nat} (hs0 : 0 < size) (hsz : c.addr + 8 + size ≤ c.next) :
    (modelWG H s t c rest).wf ((c.addr + 8, size) :: live) F := by
  have h := wf_whole hw hc hcf hs0 hsz F
  have hnd := nodup_of_sorted hw.geo.sorted
  have hcc : c ∈ H.cells := (mem_cells hc c).mpr (Or.inr (Or.inl rfl))
  have hcn : c.addr ∉ rest := by
    have := hw.lists.fl_nodup; rw [hfl] at this; exact (List.nodup_cons.mp this).1
  refine ⟨h.mem0_al, h.mem0_pos, h.len_al, h.mem0_le, h.len_lt,
    ⟨h.geo.bounds, h.geo.next_al, h.geo.sorted, h.geo.next_nb, h.geo.prev_nb, h.geo.first, h.geo.disj⟩,
    ?_, ⟨h.lives.live_cell, h.lives.cell_live, h.lives.live_nodup⟩, h.nf_lo⟩
  have hnd' : ((s ++ cW c :: t).map CellM.addr).Nodup := nodup_of_sorted h.geo.sorted
  apply lists_same (H := { H with freeList := rest }) (lists_tail hw.lists hfl) _ hnd hnd' (le_refl F)
  intro x hx hxl
  rcases (mem_cells hc x).mp hx with h1 | rfl | h1
  · exact ⟨x, List.mem_append_left _ h1, rfl, rfl, rfl, fun _ => rfl⟩
  · exact absurd hxl hcn
  · exact ⟨x, List.mem_append_right _ (List.mem_cons_of_mem _ h1), rfl, rfl, rfl, fun _ => rfl⟩

/-! ## Split: the list kept -/

theorem wf_splitG {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
    {s t : List CellM} {c d : CellM} (hc : H.cells = s ++ c :: t)
    (hd : c.last = false → d ∈ t ∧ d.addr = c.next ∧ d.prev = c.addr) (hcf : c.allocated = false)
    {rest : List Nat} (hfl : H.freeList = c.addr :: rest)
    (ha0 : 0 < c.addr) {m : Nat} (hm1 : c.addr + 12 ≤ m) (hm2 : m % 4 = 0) (hm3 : m + 12 ≤ c.next)
    {size : Nat} (hs0 : 0 < size) (hsz : m + 8 + size ≤ c.next) :
    (modelS H s t c m d).wf ((m + 8, size) :: live) F := by
  have hw0 := wf_nil hw F
  have h := wf_split2 (H := { H with freeList := [] }) hw0 hc hd hcf (by intro x _ hx; simp at hx) ha0 hm1 hm2 hm3
    hs0 hsz
  have hnd := nodup_of_sorted hw.geo.sorted
  have hT := pos_t hw.geo hc
  refine ⟨h.mem0_al, h.mem0_pos, h.len_al, h.mem0_le, h.len_lt,
    ⟨h.geo.bounds, h.geo.next_al, h.geo.sorted, h.geo.next_nb, h.geo.prev_nb, h.geo.first, h.geo.disj⟩,
    ?_, ⟨h.lives.live_cell, h.lives.cell_live, h.lives.live_nodup⟩, h.nf_lo⟩
  have hnd' : ((s ++ cS c m :: nS c m :: tS c m d t).map CellM.addr).Nodup := nodup_of_sorted h.geo.sorted
  apply lists_same (H := H) hw.lists _ hnd hnd' (le_refl F)
  have src := tS_src2 hw hc hd m
  have tgt := tS_tgt2 hw hc hd m
  intro x hx hxl
  rcases (mem_cells hc x).mp hx with h1 | rfl | h1
  · exact ⟨x, List.mem_append_left _ h1, rfl, rfl, rfl, fun _ => rfl⟩
  · exact ⟨cS x m, List.mem_append_right _ (List.mem_cons_self), rfl, rfl, rfl, fun _ => rfl⟩
  · obtain ⟨z, hz, f1, -, -, f4, -⟩ := tgt x h1
    obtain ⟨x2, hx2, g1, -, -, -, g5, gp⟩ := src z hz
    have hx2H : x2 ∈ H.cells := (mem_cells hc x2).mpr (Or.inr (Or.inr hx2))
    have e : x2 = x := mem_unique hnd hx2H hx (by rw [← g1, f1])
    subst e
    refine ⟨z, List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hz)), f1, f4, g5,
      fun hodd => ?_⟩
    rcases gp with ⟨hp, -⟩ | ⟨hl, hxa, -⟩
    · exact hp
    · exfalso
      obtain ⟨-, hda, hdp⟩ := hd hl
      have hxd : x2 = d := by
        obtain ⟨hdt, -, -⟩ := hd hl
        exact mem_unique hnd hx2H ((mem_cells hc d).mpr (Or.inr (Or.inr hdt))) (by rw [hxa, hda])
      subst hxd
      exact merge_prev_ne_head hw hfl hx2H hxl hodd hdp

/-! ## Merge: `c` (with `CAN_MERGE`) into its previous neighbour, the list's tail -/

/-- `ca` lent whole, nothing listed: the model `AllocDealloc`'s case A starts from. -/
def starE (H : HeapModel) (ca : CellM) : HeapModel :=
  { H with cells := H.cells.map (upd ca.addr { ca with allocated := true }), freeList := [] }

theorem wf_starE {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F) {ca : CellM}
    (hca : ca ∈ H.cells) (hcaf : ca.allocated = false) :
    (starE H ca).wf ((ca.addr + 8, ca.size) :: live) F := by
  have hg := hw.geo
  have hnd := nodup_of_sorted hg.sorted
  have hb := hg.bounds ca hca
  have hmem := fun z => mem_map_upd (L := H.cells) (z := z) (a := ca.addr) (y := { ca with allocated := true })
    rfl ⟨ca, hca, rfl⟩
  have hcells : (starE H ca).cells = H.cells.map (upd ca.addr { ca with allocated := true }) := rfl
  have hstar : { ca with allocated := true } ∈ (starE H ca).cells := by
    rw [hcells]; exact (hmem _).mpr (Or.inl rfl)
  have hold : ∀ x ∈ H.cells, x.addr ≠ ca.addr → x ∈ (starE H ca).cells := by
    intro x hx hxa; rw [hcells]; exact (hmem x).mpr (Or.inr ⟨hx, hxa⟩)
  have hg' : Geo (starE H ca) := by
    refine geo_map hg (upd ca.addr { ca with allocated := true }) rfl rfl hcells ?_
    intro x hx; unfold upd; split
    · rename_i e; obtain rfl := mem_unique hnd hx hca e; exact ⟨rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  refine ⟨hw.mem0_al, hw.mem0_pos, hw.len_al, hw.mem0_le, hw.len_lt, hg', lists_nil rfl, ?_, ?_⟩
  · have hs0 : 0 < ca.size := by unfold CellM.size; omega
    apply lives_gen (a := ca.addr) (s := ca.size) hw.lives hstar rfl rfl hs0 (le_refl _)
    · intro x hx hxa
      have hxc : x.addr ≠ ca.addr := fun e => by
        obtain rfl := mem_unique hnd hx hca e; rw [hcaf] at hxa; cases hxa
      exact ⟨x, hold x hx hxc, hxa, rfl, le_refl _⟩
    · intro z hz hza
      rw [hcells] at hz
      rcases (hmem z).mp hz with rfl | ⟨hz', -⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨z, hz', hza, rfl⟩
    · intro x hx hxa e
      obtain rfl := mem_unique hnd hx hca e; rw [hcaf] at hxa; cases hxa
  · intro z hz
    rw [hcells] at hz
    rcases (hmem z).mp hz with rfl | ⟨hz', -⟩
    · exact hw.nf_lo ca hca
    · exact hw.nf_lo z hz'

/-- `mergedM` with nothing listed. -/
def mergedE (H : HeapModel) (s t : List CellM) (cb ca : CellM) : HeapModel :=
  { mergedM H s t cb ca with freeList := [] }

section MergedE

variable {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
  {s t : List CellM} {cb ca : CellM} (hc : H.cells = s ++ cb :: ca :: t)
include hw hc

theorem starE_cells : ((starE H ca).cells.erase { ca with allocated := true }).map
    (upd cb.addr (cellA cb { ca with allocated := true })) = s ++ bM cb ca :: t :=
  star_cells (H := H) (live := live) (F := F) (cb := cb) hw hc

/-- The merged cells, nothing listed, `a` the last cell of its chunk. -/
theorem wf_mergedE1 (hcaf : ca.allocated = false) (hcbf : cb.allocated = false)
    (hpa : ca.prev = cb.addr) (hp0 : ca.prev ≠ 0) (hlast : ca.last = true) :
    (mergedE H s t cb ca).wf live (F + 1) := by
  obtain ⟨hS, hba, hT⟩ := mergedM_pos hw hc
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have hst := wf_starE hw hca hcaf
  have hstc : { ca with allocated := true } ∈ (starE H ca).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨ca, hca, by simp [upd]⟩
  have hstb : cb ∈ (starE H ca).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨cb, hcb, by simp [upd, show cb.addr ≠ ca.addr by omega]⟩
  have h := wf_caseA1 hst hstc rfl List.mem_cons_self hstb hpa.symm hp0 hcbf hlast
  rw [List.erase_cons_head] at h
  have hcl : (modelA1 (starE H ca) { ca with allocated := true } cb).cells = (mergedE H s t cb ca).cells := by
    show ((starE H ca).cells.erase _).map _ = _
    rw [starE_cells hw hc]
    show s ++ bM cb ca :: t = s ++ bM cb ca :: _
    cases t with
    | nil => rfl
    | cons m t' => simp [hlast]
  have e : modelA1 (starE H ca) { ca with allocated := true } cb = mergedE H s t cb ca := by
    cases hm : modelA1 (starE H ca) { ca with allocated := true } cb
    rw [hm] at hcl
    simp only [mergedE, mergedM] at hcl ⊢
    rw [← hcl]
    have := congrArg HeapModel.freeList hm
    have h0 := congrArg HeapModel.mem0 hm
    have h1 := congrArg HeapModel.len hm
    simp [modelA1, starE] at this h0 h1
    simp [this, h0, h1]
  rw [e] at h
  exact h

/-- The merged cells, nothing listed, `a` followed by `m` in its chunk. -/
theorem wf_mergedE2 (hcaf : ca.allocated = false) (hcbf : cb.allocated = false)
    (hpa : ca.prev = cb.addr) (hp0 : ca.prev ≠ 0) (hlast : ca.last = false) {m : CellM} {t' : List CellM}
    (ht : t = m :: t') (hmaddr : m.addr = ca.next) (hmprev : m.prev = ca.addr) :
    (mergedE H s t cb ca).wf live (F + 1) := by
  obtain ⟨hS, hba, hT⟩ := mergedM_pos hw hc
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have hcm : m ∈ H.cells := by rw [hc, ht]; simp
  have hma : m.addr ≠ ca.addr := by have := hT m (by rw [ht]; simp); omega
  have hst := wf_starE hw hca hcaf
  have hstc : { ca with allocated := true } ∈ (starE H ca).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨ca, hca, by simp [upd]⟩
  have hstb : cb ∈ (starE H ca).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨cb, hcb, by simp [upd, show cb.addr ≠ ca.addr by omega]⟩
  have hstm : m ∈ (starE H ca).cells := by
    show _ ∈ H.cells.map _
    exact List.mem_map.mpr ⟨m, hcm, by simp [upd, hma]⟩
  have h := wf_caseA2 hst hstc rfl List.mem_cons_self hstb hpa.symm hp0 hcbf hstm hmaddr hlast hmprev
  rw [List.erase_cons_head] at h
  have hcl : (modelA2 (starE H ca) { ca with allocated := true } cb m).cells = (mergedE H s t cb ca).cells := by
    show (((starE H ca).cells.erase _).map _).map _ = _
    rw [starE_cells hw hc, ht]
    have hT' : ∀ x ∈ t', x.addr ≠ m.addr := by
      intro x hx
      have hs := hw.geo.sorted
      rw [hc, ht, List.map_append, List.map_cons, List.map_cons, List.map_cons, List.pairwise_append,
        List.pairwise_cons, List.pairwise_cons, List.pairwise_cons] at hs
      have := hs.2.1.2.2.1 _ (List.mem_map_of_mem hx); omega
    have hbm : (bM cb ca).addr ≠ m.addr := by
      have := hT m (by rw [ht]; simp); simp only [bM]; omega
    simp only [mergedE, mergedM, hlast, List.map_append, List.map_cons, Bool.false_eq_true, ↓reduceIte]
    rw [map_upd_out (fun x hx => by have := hS x hx; have := hT m (by rw [ht]; simp); omega),
      map_upd_out hT']
    simp [upd, hbm, nbrA]
  have e : modelA2 (starE H ca) { ca with allocated := true } cb m = mergedE H s t cb ca := by
    cases hm : modelA2 (starE H ca) { ca with allocated := true } cb m
    rw [hm] at hcl
    simp only [mergedE, mergedM] at hcl ⊢
    rw [← hcl]
    have := congrArg HeapModel.freeList hm
    have h0 := congrArg HeapModel.mem0 hm
    have h1 := congrArg HeapModel.len hm
    simp [modelA2, starE] at this h0 h1
    simp [this, h0, h1]
  rw [e] at h
  exact h

end MergedE

/-- `a` merged into `b`, the list `b :: rest`. -/
def mergedG (H : HeapModel) (s t : List CellM) (cb ca : CellM) (rest : List Nat) : HeapModel :=
  { mergedM H s t cb ca with freeList := cb.addr :: rest }

theorem mergedM_cells (H : HeapModel) (s t : List CellM) (cb ca : CellM) :
    (mergedM H s t cb ca).cells = s ++ bM cb ca :: (match t with
      | [] => []
      | m :: t' => if ca.last then m :: t' else { m with prev := cb.addr } :: t') := rfl

/-- The merge of the listed head `ca` (with `CAN_MERGE`) into its previous neighbour `cb`, the
next listed cell: the list `cb :: rest`. -/
theorem wf_mergedG {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : H.wf live F)
    {s t : List CellM} {cb ca : CellM} (hc : H.cells = s ++ cb :: ca :: t) {rest : List Nat}
    (hfl : H.freeList = ca.addr :: cb.addr :: rest)
    (hcaf : ca.allocated = false) (hcbf : cb.allocated = false) (hpa : ca.prev = cb.addr) :
    (mergedG H s t cb ca rest).wf live F := by
  have hnd := nodup_of_sorted hw.geo.sorted
  have hca : ca ∈ H.cells := by rw [hc]; simp
  have hcb : cb ∈ H.cells := by rw [hc]; simp
  have hp0 : ca.prev ≠ 0 := by have := (hw.geo.bounds cb hcb).1; have := hw.mem0_pos; omega
  have hc' : H.cells = (s ++ [cb]) ++ ca :: t := by rw [hc]; simp
  have h : (mergedE H s t cb ca).wf live (F + 1) := by
    cases hl : ca.last
    · obtain ⟨m, t', ht, hma, hmp⟩ := next_head hw.geo hc' hl
      exact wf_mergedE2 hw hc hcaf hcbf hpa hp0 hl ht hma hmp
    · exact wf_mergedE1 hw hc hcaf hcbf hpa hp0 hl
  refine ⟨h.mem0_al, h.mem0_pos, h.len_al, h.mem0_le, h.len_lt,
    ⟨h.geo.bounds, h.geo.next_al, h.geo.sorted, h.geo.next_nb, h.geo.prev_nb, h.geo.first, h.geo.disj⟩,
    ?_, ⟨h.lives.live_cell, h.lives.cell_live, h.lives.live_nodup⟩, h.nf_lo⟩
  have hnd' : ((mergedM H s t cb ca).cells.map CellM.addr).Nodup := nodup_of_sorted h.geo.sorted
  have hcan : ca.addr ∉ cb.addr :: rest := by
    have := hw.lists.fl_nodup; rw [hfl] at this; exact (List.nodup_cons.mp this).1
  apply lists_same (H := { H with freeList := cb.addr :: rest }) (lists_tail hw.lists hfl) _ hnd hnd' (le_refl F)
  obtain ⟨hS, hba, hT⟩ := mergedM_pos hw hc
  intro x hx hxl
  have hxl' : x.addr ∈ H.freeList := by rw [hfl]; exact List.mem_cons_of_mem _ hxl
  rw [mergedM_cells]
  rcases (mem_cells hc' x).mp hx with h1 | rfl | h1
  · rcases List.mem_append.mp h1 with h2 | h2
    · exact ⟨x, List.mem_append_left _ h2, rfl, rfl, rfl, fun _ => rfl⟩
    · simp only [List.mem_singleton] at h2; subst h2
      exact ⟨bM x ca, List.mem_append_right _ List.mem_cons_self, rfl, rfl, rfl, fun _ => rfl⟩
  · exact absurd hxl hcan
  · cases t with
    | nil => simp at h1
    | cons m t' =>
      rcases List.mem_cons.mp h1 with rfl | h2
      · cases hl : ca.last
        · obtain ⟨m', t'', ht, -, hmp⟩ := next_head hw.geo hc' hl
          obtain ⟨rfl, rfl⟩ := List.cons.inj ht
          refine ⟨{ x with prev := cb.addr }, by simp [hl], rfl, rfl, rfl,
            fun hodd => absurd hmp (merge_prev_ne_head hw hfl hx hxl' hodd)⟩
        · exact ⟨x, by simp [hl], rfl, rfl, rfl, fun _ => rfl⟩
      · refine ⟨x, ?_, rfl, rfl, rfl, fun _ => rfl⟩
        cases ca.last <;> simp [h2]

end WNear.Binary.AllocWalk
