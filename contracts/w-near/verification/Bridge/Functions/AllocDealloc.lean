import Bridge.Functions.AllocInv
import Bridge.Functions.AllocRemove
import Bridge.Functions.AllocWrap
import Binary.Code.Part11

/-!
# `WeeAlloc::dealloc` (582) and `__rust_dealloc` (311), in the metered logic

```
dealloc(&ALLOC, ptr, size, align)        (582; `align` unused)
  ptr == 0 || size == 0 → return
  bytes_to_words(size) (570, result dropped);  head := ALLOC
  c := ptr - 8;  c.word0 &= !ALLOCATED;  c.size() (576, dropped);  c.next_free := 0
  A  c.prev ≠ 0 and the previous neighbour p is free:
       remove(c) (575);  if c was last, p.word0 |= NEXT_CELL_IS_INVALID;  p.size() (576)
  B  else, c not last and its next neighbour m free:
       c.next_free := m.next_free & !3;  m.next_free := c | CAN_MERGE
  C  else  c.next_free := head;  head := c
  ALLOC := head (A, B) or c (C)
```

## The invariant: `AllocInv.heapInv` does not support `dealloc`; `heapInvFix` does

`heapInvFix` is `AllocInv.heapInv` over `WfFix`, which is `HeapModel.wf` regrouped
(`Geo` = clauses (1)–(2), `Lists` = (3)–(4) verbatim, `Lives` = (5)) with three changes:

* **clause (5) is wrong in `HeapModel.wf`**: `(p, s) ∈ live ↔ ∃ c, allocated ∧ p = c.addr + 8 ∧
  s ≤ c.size` puts *every* `(c.addr + 8, s)` with `s ≤ c.size` in `live` (at least 17
  entries per allocated cell). After `dealloc` erases the one `(ptr, size)` the other
  entries of the freed cell stay in `live` with no allocated cell, so
  `heapInv n (live.erase (p, size)) _` is unprovable (and `alloc`'s `(p, size) :: live`
  likewise). `Lives` replaces it by: every `(p, s) ∈ live` has `0 < s` and an allocated
  cell with `p = c.addr + 8`, `s ≤ c.size`; every allocated cell has some `(c.addr + 8, s)`
  in `live`; and `(live.map Prod.fst).Nodup` (instead of `live.Nodup`), so `cellRes`'s
  `∃ s` is the client's `size`;
* `0 < s` (part of the above): `dealloc` returns early on `size = 0` without freeing, so a
  zero-size live entry could not be erased (`alloc` only lends `0 < size`);
* **`next_al : c.next % 4 = 0` is added to clause (1)**: `wf` only aligns `c.addr`, so the
  last cell of a chunk (whose `next` is the chunk end) could have an unaligned `next`, and
  then `word0 & !3 ≠ next` (575's `prev.next := c.word0 & !3`, 576's size) and the
  `NEXT_CELL_IS_INVALID` bit could not be read off the header.

Nothing else was missing: clause (4) is exactly what rules out a listed next neighbour
with `CAN_MERGE` pointing at the cell being freed (case B) and makes case A's `m.prev`
change harmless; the three cases are proved from `WfFix` in `wf_caseC`, `wf_caseB`,
`wf_caseA1` (`c` last) and `wf_caseA2`. Case B links `c` into the list only when `m` is
listed (`listB`); if `m` is a leaked free cell, `c` is leaked too.

## The specs

* `f582_spec`: `{⌜(ptr, size) ∈ live⌝ ∗ heapInvFix n maxP live F ∗ block n ptr size}`
  `dealloc(&ALLOC, ptr, size, align)` `{heapInvFix n maxP (live.erase (ptr, size)) (F + 1)}`,
  cost `D₀ = 224 regular_op_cost`s (an upper bound, with 575 counted at its bound 61: the
  paths cost C 123–134, B 139–145, A 218 (`c` not last) / 224 (`c` last)), calls to 570
  (→ 568), 576, 575 and their activations included.
* `f311_spec`: the same for `__rust_dealloc(ptr, size, align)`, cost `15 + 17 + 224 = 256`.

## Two pitfalls (for 580/581)

* A symbolic `ptr + 4294967288` (i.e. `ptr - 8`) left in a local makes the *kernel* (and
  `simp_all` in `mstep`'s side conditions) unfold `Nat.add` four billion times: rewrite it
  to `UInt32.ofNat a` (`sub8_eq`, `sub4_eq`) right after the `i32.add`.
* `i32.load8_u` of a header word owned as `bytes32 w` needs a one-byte points-to:
  `mwpi_load8u_w` splits and rejoins it, giving `w.toNat % 256`.
-/

namespace WNear.Binary.AllocDealloc

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary.AllocInv WNear.Binary.AllocLeaves WNear.Binary.AllocRemove WNear.Binary.AllocNewCell
open WNear.Binary.U128From (memBytes_split memBytes_join)

/-! ## The corrected invariant -/

/-- Clauses (1)–(2): the cells' geometry. -/
structure Geo (H : HeapModel) : Prop where
  bounds : ∀ c ∈ H.cells, H.mem0 ≤ c.addr ∧ c.addr + 24 ≤ c.next ∧ c.next ≤ H.len ∧ c.addr % 4 = 0
  /-- New: `next` is word-aligned also for the last cell of a chunk. -/
  next_al : ∀ c ∈ H.cells, c.next % 4 = 0
  sorted : (H.cells.map (·.addr)).Pairwise (· < ·)
  next_nb : ∀ c ∈ H.cells, c.last = false → ∃ d ∈ H.cells, d.addr = c.next ∧ d.prev = c.addr
  prev_nb : ∀ c ∈ H.cells, c.prev ≠ 0 → ∃ d ∈ H.cells, d.addr = c.prev ∧ d.next = c.addr ∧ d.last = false
  first : ∀ c ∈ H.cells, c.prev = 0 → c.addr % 65536 = 0

/-- Clauses (3)–(4): the free list, as in `HeapModel.wf`. -/
structure Lists (H : HeapModel) (F : Nat) : Prop where
  fl_nodup : H.freeList.Nodup
  fl_len : H.freeList.length ≤ F
  fl_free : ∀ a ∈ H.freeList, ∃ c, H.cellAt a = some c ∧ c.allocated = false
  fl_link : ∀ i (h : i < H.freeList.length), ∃ c, H.cellAt H.freeList[i] = some c ∧
    c.nextFree / 4 * 4 = H.freeList.getD (i + 1) 0
  fl_merge : ∀ i (h : i < H.freeList.length), ∀ c, H.cellAt H.freeList[i] = some c → c.nextFree % 2 = 1 →
    ∃ d, H.freeList[i + 1]? = some d.addr ∧ H.cellAt d.addr = some d ∧ d.allocated = false ∧
      c.prev = d.addr

/-- Clause (5), corrected. -/
structure Lives (H : HeapModel) (live : List (Nat × Nat)) : Prop where
  /-- Every live allocation is an allocated cell's data, of a positive size no larger
  than the cell's, ... -/
  live_cell : ∀ p s, (p, s) ∈ live → 0 < s ∧ ∃ c ∈ H.cells, c.allocated = true ∧ p = c.addr + 8 ∧ s ≤ c.size
  /-- ... every allocated cell is lent, ... -/
  cell_live : ∀ c ∈ H.cells, c.allocated = true → ∃ s, (c.addr + 8, s) ∈ live
  /-- ... and once. -/
  live_nodup : (live.map Prod.fst).Nodup

/-- `HeapModel.wf`, corrected (see the module doc). -/
structure WfFix (H : HeapModel) (live : List (Nat × Nat)) (F : Nat) : Prop where
  mem0_al : H.mem0 % 65536 = 0
  len_al : H.len % 65536 = 0
  mem0_le : H.mem0 ≤ H.len
  len_lt : H.len < 2 ^ 32
  geo : Geo H
  lists : Lists H F
  lives : Lives H live

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- `heapInv` over the corrected `WfFix`. -/
def heapInvFix (n maxP : Nat) (live : List (Nat × Nat)) (F : Nat) : IProp GF :=
  iprop(∃ H : HeapModel, ⌜WfFix H live F ∧ H.len ≤ maxP * 65536⌝ ∗
    n ↦[wms][ headAddr ] bytes32 (UInt32.ofNat H.head) ∗ n ↦[wmlength] H.len ∗
    n ↪[wmlimit] some maxP ∗ [∗list] c ∈ H.cells, cellRes n live c)

end Res

/-! ## Lists of cells -/

/-- Replace the cell at address `a` by `y`. -/
def upd (a : Nat) (y x : CellM) : CellM := if x.addr = a then y else x

theorem mem_map_upd {L : List CellM} {a : Nat} {y z : CellM} (hy : y.addr = a)
    (hex : ∃ x ∈ L, x.addr = a) : z ∈ L.map (upd a y) ↔ z = y ∨ (z ∈ L ∧ z.addr ≠ a) := by
  constructor
  · intro hz
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
    unfold upd; split
    · exact Or.inl rfl
    · exact Or.inr ⟨hx, by assumption⟩
  · rintro (rfl | ⟨hz, hza⟩)
    · obtain ⟨x, hx, hxa⟩ := hex
      exact List.mem_map.mpr ⟨x, hx, by simp [upd, hxa]⟩
    · exact List.mem_map.mpr ⟨z, hz, by simp [upd, hza]⟩

theorem addrs_map_upd {L : List CellM} {a : Nat} {y : CellM} (hy : y.addr = a) :
    (L.map (upd a y)).map CellM.addr = L.map CellM.addr := by
  induction L with
  | nil => rfl
  | cons h t ih =>
    simp only [List.map_cons, ih]
    unfold upd; split <;> simp_all

theorem nodup_of_sorted {L : List CellM} (h : (L.map CellM.addr).Pairwise (· < ·)) :
    (L.map CellM.addr).Nodup :=
  h.imp (fun h => Nat.ne_of_lt h)

theorem perm_map_upd {L : List CellM} {a : Nat} {x y : CellM} (hnd : (L.map CellM.addr).Nodup)
    (hx : x ∈ L) (hxa : x.addr = a) (hy : y.addr = a) :
    (L.map (upd a y)).Perm (y :: L.erase x) := by
  induction L with
  | nil => simp at hx
  | cons h t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    by_cases hhx : h = x
    · subst hhx
      subst hxa
      have ht : t.map (upd h.addr y) = t := by
        refine (List.map_congr_left (g := id) ?_).trans (List.map_id t)
        intro z hz
        have : z.addr ≠ h.addr := fun e => hnd.1 (List.mem_map.mpr ⟨z, hz, e⟩)
        simp [upd, this]
      simp only [List.map_cons, upd, List.erase_cons_head, ht]
      exact List.Perm.refl _
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with e | e
        · exact absurd e.symm hhx
        · exact e
      have hha : h.addr ≠ a := by
        intro e; apply hnd.1; exact List.mem_map.mpr ⟨x, hxt, by rw [hxa, e]⟩
      rw [List.map_cons, List.erase_cons_tail (by simpa using hhx)]
      simp only [upd, hha, ↓reduceIte]
      exact ((ih hnd.2 hxt).cons h).trans (List.Perm.swap y h _)

theorem cellAt_iff {L : List CellM} (hnd : (L.map CellM.addr).Nodup) {a : Nat} {x : CellM} :
    L.find? (·.addr == a) = some x ↔ x ∈ L ∧ x.addr = a := by
  induction L with
  | nil => simp
  | cons h t ih =>
    rw [List.map_cons, List.nodup_cons] at hnd
    rw [List.find?_cons]
    by_cases hh : h.addr = a
    · simp only [hh, beq_self_eq_true, Option.some.injEq, List.mem_cons]
      constructor
      · rintro rfl; exact ⟨Or.inl rfl, hh⟩
      · rintro ⟨rfl | hx, hxa⟩
        · rfl
        · exact absurd (List.mem_map.mpr ⟨x, hx, hxa.trans hh.symm⟩) hnd.1
    · have : (h.addr == a) = false := by simpa using hh
      rw [this, ih hnd.2, List.mem_cons]
      constructor
      · rintro ⟨hx, hxa⟩; exact ⟨Or.inr hx, hxa⟩
      · rintro ⟨rfl | hx, hxa⟩
        · exact absurd hxa hh
        · exact ⟨hx, hxa⟩

theorem cellAt_iff' {H : HeapModel} (hnd : (H.cells.map CellM.addr).Nodup) {a : Nat} {x : CellM} :
    H.cellAt a = some x ↔ x ∈ H.cells ∧ x.addr = a := cellAt_iff hnd

theorem map_inj_of_nodup {α β : Type} {f : α → β} : ∀ {L : List α}, (L.map f).Nodup →
    ∀ {x y}, x ∈ L → y ∈ L → f x = f y → x = y
  | [], _, _, _, hx, _, _ => by simp at hx
  | h :: t, hnd, x, y, hx, hy, e => by
    rw [List.map_cons, List.nodup_cons] at hnd
    rcases List.mem_cons.mp hx with hx1 | hx1 <;> rcases List.mem_cons.mp hy with hy1 | hy1
    · rw [hx1, hy1]
    · subst hx1; exact absurd (List.mem_map.mpr ⟨y, hy1, e.symm⟩) hnd.1
    · subst hy1; exact absurd (List.mem_map.mpr ⟨x, hx1, e⟩) hnd.1
    · exact map_inj_of_nodup hnd.2 hx1 hy1 e

theorem mem_unique {L : List CellM} (hnd : (L.map CellM.addr).Nodup) {x y : CellM}
    (hx : x ∈ L) (hy : y ∈ L) (h : x.addr = y.addr) : x = y := map_inj_of_nodup hnd hx hy h

theorem nodup_of_map {α β : Type} {f : α → β} {L : List α} (hnd : (L.map f).Nodup) : L.Nodup :=
  List.Pairwise.of_map f (fun _ _ h e => h (e ▸ rfl)) hnd

/-! ## Geometry kept by an update that keeps every cell's neighbours -/

theorem geo_map {H H' : HeapModel} (hg : Geo H) (f : CellM → CellM) (h0 : H'.mem0 = H.mem0)
    (hl : H'.len = H.len) (hc : H'.cells = H.cells.map f)
    (hf : ∀ x ∈ H.cells, (f x).addr = x.addr ∧ (f x).next = x.next ∧ (f x).prev = x.prev ∧
      (f x).last = x.last) : Geo H' := by
  have hmem : ∀ z ∈ H'.cells, ∃ x ∈ H.cells, z = f x := by
    intro z hz; rw [hc] at hz; obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz; exact ⟨x, hx, rfl⟩
  have hin : ∀ x ∈ H.cells, f x ∈ H'.cells := fun x hx => by rw [hc]; exact List.mem_map_of_mem hx
  constructor
  · intro z hz; obtain ⟨x, hx, rfl⟩ := hmem z hz
    have := hg.bounds x hx; have := hf x hx; rw [h0, hl]; omega
  · intro z hz; obtain ⟨x, hx, rfl⟩ := hmem z hz
    have := hg.next_al x hx; have := hf x hx; omega
  · rw [hc, List.map_map]
    have : H.cells.map ((fun x => x.addr) ∘ f) = H.cells.map (fun x => x.addr) :=
      List.map_congr_left (fun x hx => by simp [(hf x hx).1])
    rw [this]; exact hg.sorted
  · intro z hz hlast; obtain ⟨x, hx, rfl⟩ := hmem z hz
    obtain ⟨e1, e2, e3, e4⟩ := hf x hx
    obtain ⟨d, hd, hd1, hd2⟩ := hg.next_nb x hx (e4 ▸ hlast)
    obtain ⟨g1, g2, g3, g4⟩ := hf d hd
    exact ⟨f d, hin d hd, by rw [g1, hd1, e2], by rw [g3, hd2, e1]⟩
  · intro z hz hp; obtain ⟨x, hx, rfl⟩ := hmem z hz
    obtain ⟨e1, e2, e3, e4⟩ := hf x hx
    obtain ⟨d, hd, hd1, hd2, hd3⟩ := hg.prev_nb x hx (e3 ▸ hp)
    obtain ⟨g1, g2, g3, g4⟩ := hf d hd
    exact ⟨f d, hin d hd, by rw [g1, hd1, e3], by rw [g2, hd2, e1], by rw [g4, hd3]⟩
  · intro z hz hp; obtain ⟨x, hx, rfl⟩ := hmem z hz
    obtain ⟨e1, e2, e3, e4⟩ := hf x hx
    rw [e1]; exact hg.first x hx (e3 ▸ hp)

/-! ## The live allocations after freeing one -/

theorem lives_erase {H H' : HeapModel} {live : List (Nat × Nat)} (hv : Lives H live) {c : CellM}
    (hc : c ∈ H.cells) {s : Nat} (hs : (c.addr + 8, s) ∈ live)
    (h1 : ∀ z ∈ H'.cells, z.allocated = true → ∃ x ∈ H.cells, x.allocated = true ∧ x.addr = z.addr ∧
      x.addr ≠ c.addr)
    (h2 : ∀ x ∈ H.cells, x.allocated = true → x.addr ≠ c.addr →
      ∃ z ∈ H'.cells, z.allocated = true ∧ z.addr = x.addr ∧ z.size = x.size) :
    Lives H' (live.erase (c.addr + 8, s)) := by
  have hnd : live.Nodup := nodup_of_map hv.live_nodup
  have fst_uniq : ∀ p s₁ s₂, (p, s₁) ∈ live → (p, s₂) ∈ live → s₁ = s₂ := by
    intro p s₁ s₂ h₁ h₂
    have := map_inj_of_nodup hv.live_nodup h₁ h₂ rfl
    simp at this; exact this
  constructor
  · intro p s' hm
    rw [List.Nodup.mem_erase_iff hnd] at hm
    obtain ⟨hne, hm⟩ := hm
    obtain ⟨hpos, x, hx, hxa, rfl, hle⟩ := hv.live_cell _ _ hm
    refine ⟨hpos, ?_⟩
    have hxc : x.addr ≠ c.addr := by
      intro e; apply hne; rw [e] at hm ⊢; rw [fst_uniq _ _ _ hm hs]
    obtain ⟨z, hz, hza, hzaddr, hzs⟩ := h2 x hx hxa hxc
    exact ⟨z, hz, hza, by rw [hzaddr], by rw [hzs]; exact hle⟩
  · intro z hz hza
    obtain ⟨x, hx, hxa, hxz, hxc⟩ := h1 z hz hza
    obtain ⟨s', hs'⟩ := hv.cell_live x hx hxa
    refine ⟨s', ?_⟩
    rw [List.Nodup.mem_erase_iff hnd]
    refine ⟨?_, by rw [← hxz]; exact hs'⟩
    intro e; simp at e; omega
  · exact hv.live_nodup.sublist ((List.erase_sublist).map _)

/-! ## The free list, by `?`-indexing -/

theorem lists_of_q {H : HeapModel} {F : Nat} (h1 : H.freeList.Nodup) (h2 : H.freeList.length ≤ F)
    (h3 : ∀ a ∈ H.freeList, ∃ c, H.cellAt a = some c ∧ c.allocated = false)
    (h4 : ∀ j a, H.freeList[j]? = some a → ∃ c, H.cellAt a = some c ∧
      c.nextFree / 4 * 4 = (H.freeList[j + 1]?).getD 0)
    (h5 : ∀ j a, H.freeList[j]? = some a → ∀ c, H.cellAt a = some c → c.nextFree % 2 = 1 →
      ∃ d, H.freeList[j + 1]? = some d.addr ∧ H.cellAt d.addr = some d ∧ d.allocated = false ∧
        c.prev = d.addr) : Lists H F := by
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · intro i hi
    obtain ⟨c, hc, he⟩ := h4 i _ (List.getElem?_eq_getElem hi)
    exact ⟨c, hc, by rw [he, List.getD_eq_getElem?_getD]⟩
  · intro i hi c hc hm
    exact h5 i _ (List.getElem?_eq_getElem hi) c hc hm

theorem Lists.link_q {H : HeapModel} {F : Nat} (hw : Lists H F) :
    ∀ j a, H.freeList[j]? = some a → ∃ c, H.cellAt a = some c ∧
      c.nextFree / 4 * 4 = (H.freeList[j + 1]?).getD 0 := by
  intro j a hj
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  obtain ⟨c, hc, he⟩ := hw.fl_link j hlt
  exact ⟨c, hc, by rw [he, List.getD_eq_getElem?_getD]⟩

theorem Lists.merge_q {H : HeapModel} {F : Nat} (hw : Lists H F) :
    ∀ j a, H.freeList[j]? = some a → ∀ c, H.cellAt a = some c → c.nextFree % 2 = 1 →
      ∃ d, H.freeList[j + 1]? = some d.addr ∧ H.cellAt d.addr = some d ∧ d.allocated = false ∧
        c.prev = d.addr := by
  intro j a hj
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hj
  exact hw.fl_merge j hlt

/-- What a list cell keeps across an update that does not touch the list. -/
def Keeps (x x' : CellM) : Prop :=
  x'.addr = x.addr ∧ x'.allocated = x.allocated ∧ x'.nextFree = x.nextFree ∧
    (x.nextFree % 2 = 1 → x'.prev = x.prev)

theorem lists_same {H : HeapModel} {F F' : Nat} (hw : Lists H F) (L' : List CellM)
    (hnd : (H.cells.map CellM.addr).Nodup) (hnd' : (L'.map CellM.addr).Nodup) (hF : F ≤ F')
    (hs : ∀ x ∈ H.cells, x.addr ∈ H.freeList → ∃ x' ∈ L', Keeps x x') :
    Lists { H with cells := L' } F' := by
  have get : ∀ a ∈ H.freeList, ∃ x ∈ H.cells, x.addr = a ∧ ∃ x' ∈ L', Keeps x x' := by
    intro a ha
    obtain ⟨x, hx, -⟩ := hw.fl_free a ha
    obtain ⟨hxm, hxa⟩ := (cellAt_iff' hnd).mp hx
    exact ⟨x, hxm, hxa, hs x hxm (hxa ▸ ha)⟩
  have ca' : ∀ {a x'}, x' ∈ L' → x'.addr = a → HeapModel.cellAt { H with cells := L' } a = some x' :=
    fun hm ha => (cellAt_iff (L := L') hnd').mpr ⟨hm, ha⟩
  apply lists_of_q (H := { H with cells := L' }) hw.fl_nodup (Nat.le_trans hw.fl_len hF)
  · intro a ha
    obtain ⟨x, hxm, hxa, x', hx', k1, k2, -⟩ := get a ha
    obtain ⟨c, hc, hcf⟩ := hw.fl_free a ha
    obtain rfl : c = x := mem_unique hnd ((cellAt_iff' hnd).mp hc).1 hxm
      (((cellAt_iff' hnd).mp hc).2.trans hxa.symm)
    exact ⟨x', ca' hx' (k1.trans hxa), k2.trans hcf⟩
  · intro j a hj
    obtain ⟨x, hxm, hxa, x', hx', k1, -, k3, -⟩ := get a (List.mem_of_getElem? hj)
    obtain ⟨c, hc, hcl⟩ := hw.link_q j a hj
    obtain rfl : c = x := mem_unique hnd ((cellAt_iff' hnd).mp hc).1 hxm
      (((cellAt_iff' hnd).mp hc).2.trans hxa.symm)
    exact ⟨x', ca' hx' (k1.trans hxa), by rw [k3]; exact hcl⟩
  · intro j a hj c' hc' hm
    obtain ⟨x, hxm, hxa, x', hx', k1, k2, k3, k4⟩ := get a (List.mem_of_getElem? hj)
    obtain rfl : c' = x' := mem_unique hnd' ((cellAt_iff hnd').mp hc').1 hx'
      (((cellAt_iff hnd').mp hc').2.trans (k1.trans hxa).symm)
    have hcx : H.cellAt a = some x := (cellAt_iff' hnd).mpr ⟨hxm, hxa⟩
    obtain ⟨d, hd1, hd2, hd3, hd4⟩ := hw.merge_q j a hj x hcx (k3 ▸ hm)
    obtain ⟨y, hym, hya, y', hy', l1, l2, -, -⟩ := get d.addr (List.mem_of_getElem? hd1)
    have hdm := ((cellAt_iff' hnd).mp hd2)
    obtain rfl : y = d := mem_unique hnd hym hdm.1 (hya.trans hdm.2.symm)
    exact ⟨y', by rw [l1]; exact hd1, ca' hy' rfl, l2.trans hd3, by rw [k4 (k3 ▸ hm), hd4, l1]⟩


theorem ins_get {α : Type} (l : List α) (i : Nat) (hi : i < l.length) (x : α) (j : Nat) :
    (l.take (i + 1) ++ x :: l.drop (i + 1))[j]? =
      if j ≤ i then l[j]? else if j = i + 1 then some x else l[j - 1]? := by
  have hl : (l.take (i + 1)).length = i + 1 := by rw [List.length_take]; omega
  by_cases h1 : j ≤ i
  · simp only [h1, ↓reduceIte]
    rw [List.getElem?_append_left (by omega), List.getElem?_take]
    simp only [show j < i + 1 by omega, ↓reduceIte]
  · simp only [h1, ↓reduceIte]
    rw [List.getElem?_append_right (by omega), hl]
    by_cases h2 : j = i + 1
    · subst h2; simp
    · simp only [h2, ↓reduceIte]
      obtain ⟨k, hk⟩ : ∃ k, j - (i + 1) = k + 1 := ⟨j - (i + 1) - 1, by omega⟩
      rw [hk, List.getElem?_cons_succ, List.getElem?_drop]
      congr 1; omega

theorem nodup_get_inj {α : Type} : ∀ {l : List α}, l.Nodup → ∀ {j k : Nat} {a : α},
    l[j]? = some a → l[k]? = some a → j = k
  | [], _, _, _, _, hj, _ => by simp at hj
  | b :: t, h, j, k, a, hj, hk => by
    rw [List.nodup_cons] at h
    match j, k with
    | 0, 0 => rfl
    | 0, k + 1 => simp at hj hk; subst hj; exact absurd (List.mem_of_getElem? hk) h.1
    | j + 1, 0 => simp at hj hk; subst hk; exact absurd (List.mem_of_getElem? hj) h.1
    | j + 1, k + 1 => simp at hj hk; rw [nodup_get_inj h.2 hj hk]

theorem head_eq_get0 (l : List Nat) : (l.headD 0) = (l[0]?).getD 0 := by cases l <;> rfl

/-- Push `c` (now free, `next_free` = the old head) at the head of the list. -/
theorem lists_push {H : HeapModel} {F F' : Nat} (hw : Lists H F) (L' : List CellM)
    (hnd : (H.cells.map CellM.addr).Nodup) (hnd' : (L'.map CellM.addr).Nodup)
    (hlen : H.freeList.length + 1 ≤ F') {c' : CellM} (hc' : c' ∈ L') (hcf : c'.allocated = false)
    (hcn : c'.addr ∉ H.freeList) (hcnf : c'.nextFree = H.head) (hhead : H.head % 4 = 0)
    (hs : ∀ x ∈ H.cells, x.addr ∈ H.freeList → ∃ x' ∈ L', Keeps x x') :
    Lists { H with cells := L', freeList := c'.addr :: H.freeList } F' := by
  have get : ∀ a ∈ H.freeList, ∃ x ∈ H.cells, x.addr = a ∧ x.allocated = false ∧ ∃ x' ∈ L', Keeps x x' := by
    intro a ha
    obtain ⟨x, hx, hxf⟩ := hw.fl_free a ha
    obtain ⟨hxm, hxa⟩ := (cellAt_iff' hnd).mp hx
    exact ⟨x, hxm, hxa, hxf, hs x hxm (hxa ▸ ha)⟩
  have ca' : ∀ {a x'}, x' ∈ L' → x'.addr = a →
      HeapModel.cellAt { H with cells := L', freeList := c'.addr :: H.freeList } a = some x' :=
    fun hm ha => (cellAt_iff (L := L') hnd').mpr ⟨hm, ha⟩
  have ca'' : ∀ {a x'}, HeapModel.cellAt { H with cells := L', freeList := c'.addr :: H.freeList } a = some x' →
      x' ∈ L' ∧ x'.addr = a := fun h => (cellAt_iff (L := L') hnd').mp h
  have hca : ∀ {a x}, H.cellAt a = some x → x ∈ H.cells ∧ x.addr = a := fun h => (cellAt_iff' hnd).mp h
  apply lists_of_q (H := { H with cells := L', freeList := c'.addr :: H.freeList })
    (List.nodup_cons.mpr ⟨hcn, hw.fl_nodup⟩) (by simpa using hlen)
  · intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨c', ca' hc' rfl, hcf⟩
    obtain ⟨x, hxm, hxa, hxf, x', hx', k1, k2, -⟩ := get a ha
    exact ⟨x', ca' hx' (k1.trans hxa), k2.trans hxf⟩
  · intro j a hj
    match j with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      refine ⟨c', ca' hc' rfl, ?_⟩
      simp only [List.getElem?_cons_succ, hcnf]
      rw [← head_eq_get0]; unfold HeapModel.head at hhead ⊢; omega
    | j + 1 =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      obtain ⟨x, hxm, hxa, -, x', hx', k1, -, k3, -⟩ := get a (List.mem_of_getElem? hj)
      obtain ⟨c, hc, hcl⟩ := hw.link_q j a hj
      obtain rfl : c = x := mem_unique hnd (hca hc).1 hxm ((hca hc).2.trans hxa.symm)
      exact ⟨x', ca' hx' (k1.trans hxa), by rw [k3]; exact hcl⟩
  · intro j a hj y hy hm
    match j with
    | 0 =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj; subst hj
      obtain rfl : y = c' := mem_unique hnd' (ca'' hy).1 hc' (ca'' hy).2
      exfalso; unfold HeapModel.head at hcnf hhead; omega
    | j + 1 =>
      simp only [List.getElem?_cons_succ] at hj ⊢
      obtain ⟨x, hxm, hxa, -, x', hx', k1, k2, k3, k4⟩ := get a (List.mem_of_getElem? hj)
      obtain rfl : y = x' := mem_unique hnd' (ca'' hy).1 hx' ((ca'' hy).2.trans (k1.trans hxa).symm)
      obtain ⟨d, hd1, hd2, hd3, hd4⟩ := hw.merge_q j a hj x ((cellAt_iff' hnd).mpr ⟨hxm, hxa⟩) (k3 ▸ hm)
      obtain ⟨z, hzm, hza, -, z', hz', l1, l2, -, -⟩ := get d.addr (List.mem_of_getElem? hd1)
      obtain rfl : z = d := mem_unique hnd hzm (hca hd2).1 (hza.trans (hca hd2).2.symm)
      exact ⟨z', by rw [l1]; exact hd1, ca' hz' rfl, l2.trans hd3, by rw [k4 (k3 ▸ hm), hd4, l1]⟩


/-- Link `c` (now free) right after the list cell `m`, whose `next_free` becomes
`c | CAN_MERGE`; `c` takes `m`'s old successor. -/
theorem lists_insert {H : HeapModel} {F F' : Nat} (hw : Lists H F) (L' : List CellM)
    (hnd : (H.cells.map CellM.addr).Nodup) (hnd' : (L'.map CellM.addr).Nodup)
    (hlen : H.freeList.length + 1 ≤ F') {i : Nat} {m m' c' : CellM}
    (hi : H.freeList[i]? = some m.addr) (hm : m ∈ H.cells)
    (hc' : c' ∈ L') (hcf : c'.allocated = false) (hcn : c'.addr ∉ H.freeList)
    (hcnf : c'.nextFree / 4 * 4 = m.nextFree / 4 * 4) (hcm : c'.nextFree % 2 = 0) (hca4 : c'.addr % 4 = 0)
    (hm' : m' ∈ L') (hm'a : m'.addr = m.addr) (hm'f : m'.allocated = false)
    (hm'n : m'.nextFree = c'.addr + 1) (hm'p : m'.prev = c'.addr)
    (hs : ∀ x ∈ H.cells, x.addr ∈ H.freeList → x.addr ≠ m.addr → ∃ x' ∈ L', Keeps x x') :
    Lists { H with cells := L', freeList := H.freeList.take (i + 1) ++ c'.addr :: H.freeList.drop (i + 1) } F' := by
  have hil : i < H.freeList.length := (List.getElem?_eq_some_iff.mp hi).1
  have hca : ∀ {a x}, H.cellAt a = some x → x ∈ H.cells ∧ x.addr = a := fun h => (cellAt_iff' hnd).mp h
  have get : ∀ a ∈ H.freeList, ∃ x ∈ H.cells, x.addr = a ∧ x.allocated = false ∧
      ∃ x' ∈ L', x'.addr = a ∧ x'.allocated = false ∧ (a ≠ m.addr → Keeps x x') := by
    intro a ha
    obtain ⟨x, hx, hxf⟩ := hw.fl_free a ha
    obtain ⟨hxm, hxa⟩ := hca hx
    refine ⟨x, hxm, hxa, hxf, ?_⟩
    by_cases ham : a = m.addr
    · exact ⟨m', hm', hm'a.trans ham.symm, hm'f, fun h => absurd ham h⟩
    · obtain ⟨x', hx', k1, k2, k3, k4⟩ := hs x hxm (hxa ▸ ha) (hxa ▸ ham)
      exact ⟨x', hx', k1.trans hxa, k2.trans hxf, fun _ => ⟨k1, k2, k3, k4⟩⟩
  have ca' : ∀ {a x'}, x' ∈ L' → x'.addr = a → (L'.find? (·.addr == a)) = some x' :=
    fun hm ha => (cellAt_iff (L := L') hnd').mpr ⟨hm, ha⟩
  have ca'' : ∀ {a x'}, (L'.find? (·.addr == a)) = some x' → x' ∈ L' ∧ x'.addr = a :=
    fun h => (cellAt_iff (L := L') hnd').mp h
  have hmc : H.cellAt m.addr = some m := (cellAt_iff' hnd).mpr ⟨hm, rfl⟩
  have hperm : (H.freeList.take (i + 1) ++ c'.addr :: H.freeList.drop (i + 1)).Perm
      (c'.addr :: H.freeList) := by
    have := (List.perm_middle (a := c'.addr) (l₁ := H.freeList.take (i + 1))
      (l₂ := H.freeList.drop (i + 1)))
    rwa [List.take_append_drop] at this
  have mem' : ∀ a, a ∈ H.freeList.take (i + 1) ++ c'.addr :: H.freeList.drop (i + 1) →
      a = c'.addr ∨ a ∈ H.freeList := fun a ha => List.mem_cons.mp (hperm.mem_iff.mp ha)
  have hne : ∀ {j a}, H.freeList[j]? = some a → j ≠ i → a ≠ m.addr := by
    intro j a hj hji e; subst e; exact hji (nodup_get_inj hw.fl_nodup hj hi)
  apply lists_of_q (H := { H with cells := L', freeList := H.freeList.take (i + 1) ++ c'.addr :: H.freeList.drop (i + 1) })
    (hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨hcn, hw.fl_nodup⟩))
    (by simp only [hperm.length_eq, List.length_cons]; omega)
  · intro a ha
    rcases mem' a ha with rfl | ha
    · exact ⟨c', ca' hc' rfl, hcf⟩
    obtain ⟨x, -, -, -, x', hx', k1, k2, -⟩ := get a ha
    exact ⟨x', ca' hx' k1, k2⟩
  · intro j a hj
    simp only [ins_get _ _ hil] at hj ⊢
    show ∃ c, L'.find? (·.addr == a) = some c ∧ _
    by_cases h1 : j < i
    · simp only [show j ≤ i by omega, show j + 1 ≤ i by omega, ↓reduceIte] at hj ⊢
      obtain ⟨x, hxm, hxa, -, x', hx', k1, -, hk⟩ := get a (List.mem_of_getElem? hj)
      obtain ⟨-, -, k3, -⟩ := hk (hne hj (by omega))
      obtain ⟨c, hc, hcl⟩ := hw.link_q j a hj
      obtain rfl : c = x := mem_unique hnd (hca hc).1 hxm ((hca hc).2.trans hxa.symm)
      exact ⟨x', ca' hx' k1, by rw [k3]; exact hcl⟩
    by_cases h2 : j = i
    · subst h2
      simp only [Nat.le_refl, ↓reduceIte, show ¬ (j + 1 ≤ j) by omega] at hj ⊢
      rw [hi] at hj; cases hj
      refine ⟨m', ca' hm' hm'a, ?_⟩
      simp only [Option.getD_some, hm'n]; omega
    by_cases h3 : j = i + 1
    · subst h3
      simp only [show ¬ (i + 1 ≤ i) by omega, show ¬ (i + 1 + 1 ≤ i) by omega,
        show ¬ (i + 1 + 1 = i + 1) by omega, ↓reduceIte, Option.some.injEq] at hj ⊢
      subst hj
      refine ⟨c', ca' hc' rfl, ?_⟩
      obtain ⟨c, hc, hcl⟩ := hw.link_q i m.addr hi
      rw [hmc] at hc; cases hc
      rw [hcnf, hcl]; rfl
    · simp only [show ¬ (j ≤ i) by omega, show ¬ (j + 1 ≤ i) by omega, h3,
        show ¬ (j + 1 = i + 1) by omega, ↓reduceIte] at hj ⊢
      obtain ⟨x, hxm, hxa, -, x', hx', k1, -, hk⟩ := get a (List.mem_of_getElem? hj)
      obtain ⟨-, -, k3, -⟩ := hk (hne hj (by omega))
      obtain ⟨c, hc, hcl⟩ := hw.link_q (j - 1) a hj
      obtain rfl : c = x := mem_unique hnd (hca hc).1 hxm ((hca hc).2.trans hxa.symm)
      refine ⟨x', ca' hx' k1, ?_⟩
      rw [k3, hcl, show j - 1 + 1 = j + 1 - 1 by omega]
  · intro j a hj y hy hodd
    have hy' := ca'' hy
    simp only [ins_get _ _ hil] at hj ⊢
    by_cases h1 : j < i
    · simp only [show j ≤ i by omega, show j + 1 ≤ i by omega, ↓reduceIte] at hj ⊢
      obtain ⟨x, hxm, hxa, -, x', hx', k1, -, hk⟩ := get a (List.mem_of_getElem? hj)
      obtain ⟨-, k2, k3, k4⟩ := hk (hne hj (by omega))
      obtain rfl : y = x' := mem_unique hnd' hy'.1 hx' (hy'.2.trans k1.symm)
      obtain ⟨d, hd1, hd2, hd3, hd4⟩ := hw.merge_q j a hj x ((cellAt_iff' hnd).mpr ⟨hxm, hxa⟩) (k3 ▸ hodd)
      obtain ⟨-, -, -, -, d', hd', l1, l2, -⟩ := get d.addr (List.mem_of_getElem? hd1)
      exact ⟨d', by rw [l1]; exact hd1, ca' hd' rfl, l2, by rw [k4 (k3 ▸ hodd), hd4, l1]⟩
    by_cases h2 : j = i
    · subst h2
      simp only [Nat.le_refl, ↓reduceIte, show ¬ (j + 1 ≤ j) by omega] at hj ⊢
      rw [hi] at hj; cases hj
      obtain rfl : y = m' := mem_unique hnd' hy'.1 hm' (hy'.2.trans hm'a.symm)
      exact ⟨c', rfl, ca' hc' rfl, hcf, hm'p⟩
    by_cases h3 : j = i + 1
    · subst h3
      simp only [show ¬ (i + 1 ≤ i) by omega, ↓reduceIte, Option.some.injEq] at hj
      subst hj
      obtain rfl : y = c' := mem_unique hnd' hy'.1 hc' hy'.2
      omega
    · simp only [show ¬ (j ≤ i) by omega, show ¬ (j + 1 ≤ i) by omega, h3,
        show ¬ (j + 1 = i + 1) by omega, ↓reduceIte] at hj ⊢
      obtain ⟨x, hxm, hxa, -, x', hx', k1, -, hk⟩ := get a (List.mem_of_getElem? hj)
      obtain ⟨-, k2, k3, k4⟩ := hk (hne hj (by omega))
      obtain rfl : y = x' := mem_unique hnd' hy'.1 hx' (hy'.2.trans k1.symm)
      obtain ⟨d, hd1, hd2, hd3, hd4⟩ := hw.merge_q (j - 1) a hj x ((cellAt_iff' hnd).mpr ⟨hxm, hxa⟩)
        (k3 ▸ hodd)
      rw [show j - 1 + 1 = j + 1 - 1 by omega] at hd1
      obtain ⟨-, -, -, -, d', hd', l1, l2, -⟩ := get d.addr (List.mem_of_getElem? hd1)
      exact ⟨d', by rw [l1]; exact hd1, ca' hd' rfl, l2, by rw [k4 (k3 ▸ hodd), hd4, l1]⟩


theorem mem_erase_iff' {L : List CellM} (hnd : (L.map CellM.addr).Nodup) {c z : CellM} (hc : c ∈ L) :
    z ∈ L.erase c ↔ z ∈ L ∧ z.addr ≠ c.addr := by
  rw [List.Nodup.mem_erase_iff (nodup_of_map hnd)]
  constructor
  · rintro ⟨hne, hz⟩; exact ⟨hz, fun e => hne (mem_unique hnd hz hc e)⟩
  · rintro ⟨hz, hne⟩; exact ⟨fun e => hne (e ▸ rfl), hz⟩

/-! ## The three cases of `dealloc`, on the model -/

section Cases

variable {H : HeapModel} {live : List (Nat × Nat)} {F : Nat} (hw : WfFix H live F)
  {c : CellM} (hc : c ∈ H.cells) (hca : c.allocated = true) {s : Nat} (hs : (c.addr + 8, s) ∈ live)
include hw hc hca

theorem WfFix.nodup : (H.cells.map CellM.addr).Nodup := nodup_of_sorted hw.geo.sorted

theorem not_listed : c.addr ∉ H.freeList := by
  intro h
  obtain ⟨x, hx, hxf⟩ := hw.lists.fl_free _ h
  obtain ⟨hxm, hxa⟩ := (cellAt_iff' (hw.nodup hc hca)).mp hx
  obtain rfl : x = c := mem_unique (hw.nodup hc hca) hxm hc hxa
  rw [hca] at hxf; cases hxf

theorem head_al : H.head % 4 = 0 := by
  unfold HeapModel.head
  cases hl : H.freeList with
  | nil => rfl
  | cons a t =>
    obtain ⟨x, hx, -⟩ := hw.lists.fl_free a (by rw [hl]; exact List.mem_cons_self)
    obtain ⟨hxm, hxa⟩ := (cellAt_iff' (hw.nodup hc hca)).mp hx
    have := (hw.geo.bounds x hxm).2.2.2
    simp only [List.headD_cons]; omega

/-- Case C, push at the head: `c` becomes free with `next_free` the old head. -/
def cellC (H : HeapModel) (c : CellM) : CellM := { c with allocated := false, nextFree := H.head }

def modelC (H : HeapModel) (c : CellM) : HeapModel :=
  { H with cells := H.cells.map (upd c.addr (cellC H c)), freeList := c.addr :: H.freeList }

include hs in
theorem wf_caseC : WfFix (modelC H c) (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  have hex : ∃ x ∈ H.cells, x.addr = c.addr := ⟨c, hc, rfl⟩
  have hmem := fun z => mem_map_upd (L := H.cells) (z := z) (a := c.addr) (y := cellC H c) rfl hex
  have hnd' : ((H.cells.map (upd c.addr (cellC H c))).map CellM.addr).Nodup := by
    rw [addrs_map_upd (a := c.addr) (y := cellC H c) rfl]; exact hnd
  have hcn := not_listed hw hc hca
  refine ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt, ?_, ?_, ?_⟩
  · apply geo_map (H' := modelC H c) hw.geo (upd c.addr (cellC H c)) rfl rfl rfl
    intro x hx
    unfold upd; split
    · rename_i h; obtain rfl : x = c := mem_unique hnd hx hc h; simp [cellC]
    · simp
  · have := lists_push (F' := F + 1) hw.lists _ hnd hnd' (Nat.succ_le_succ hw.lists.fl_len)
      (c' := cellC H c) ((hmem _).mpr (Or.inl rfl)) rfl hcn rfl (head_al hw hc hca)
      (fun x hx hxl => ⟨x, (hmem x).mpr (Or.inr ⟨hx, fun e => hcn (e ▸ hxl)⟩), rfl, rfl, rfl, fun _ => rfl⟩)
    exact this
  · apply lives_erase hw.lives hc hs
    · intro z hz hza
      rcases (hmem z).mp hz with rfl | ⟨hz, hzc⟩
      · simp [cellC] at hza
      · exact ⟨z, hz, hza, rfl, hzc⟩
    · intro x hx hxa hxc
      exact ⟨x, (hmem x).mpr (Or.inr ⟨hx, hxc⟩), hxa, rfl, rfl⟩

/-- Case B, link after the free next neighbour `m`: `c` becomes free and takes `m`'s
successor (`m.next_free & !3`), `m.next_free` becomes `c | CAN_MERGE`. -/
def cellB (c m : CellM) : CellM := { c with allocated := false, nextFree := m.nextFree % 2 ^ 32 / 4 * 4 }

def nbrB (c m : CellM) : CellM := { m with nextFree := c.addr + 1 }

/-- `c` enters the list after `m` if `m` is listed (else both stay out of it). -/
def listB (l : List Nat) (c m : CellM) : List Nat :=
  if m.addr ∈ l then l.take (l.idxOf m.addr + 1) ++ c.addr :: l.drop (l.idxOf m.addr + 1) else l

def modelB (H : HeapModel) (c m : CellM) : HeapModel :=
  { H with cells := (H.cells.map (upd c.addr (cellB c m))).map (upd m.addr (nbrB c m)),
           freeList := listB H.freeList c m }

theorem modelB_head (H : HeapModel) (c m : CellM) : (modelB H c m).head = H.head := by
  unfold modelB HeapModel.head listB
  split
  · cases hl : H.freeList with
    | nil => rename_i h; rw [hl] at h; simp at h
    | cons a t => simp
  · rfl

include hs in
theorem wf_caseB {m : CellM} (hm : m ∈ H.cells) (hmaddr : m.addr = c.next) (hlast : c.last = false)
    (hmprev : m.prev = c.addr) (hmf : m.allocated = false) :
    WfFix (modelB H c m) (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  have hcm : c.addr ≠ m.addr := by have := (hw.geo.bounds c hc).2.1; omega
  have hmem1 := fun z => mem_map_upd (L := H.cells) (z := z) (a := c.addr) (y := cellB c m) rfl ⟨c, hc, rfl⟩
  have hex2 : ∃ x ∈ H.cells.map (upd c.addr (cellB c m)), x.addr = m.addr :=
    ⟨m, (hmem1 m).mpr (Or.inr ⟨hm, fun e => hcm e.symm⟩), rfl⟩
  have hmem : ∀ z, z ∈ (modelB H c m).cells ↔
      z = nbrB c m ∨ ((z = cellB c m ∨ (z ∈ H.cells ∧ z.addr ≠ c.addr)) ∧ z.addr ≠ m.addr) := by
    intro z
    show z ∈ (H.cells.map (upd c.addr (cellB c m))).map (upd m.addr (nbrB c m)) ↔ _
    rw [mem_map_upd (a := m.addr) (y := nbrB c m) rfl hex2, hmem1]
  have hnd' : ((modelB H c m).cells.map CellM.addr).Nodup := by
    show (((H.cells.map (upd c.addr (cellB c m))).map (upd m.addr (nbrB c m))).map CellM.addr).Nodup
    rw [addrs_map_upd (a := m.addr) (y := nbrB c m) rfl, addrs_map_upd (a := c.addr) (y := cellB c m) rfl]
    exact hnd
  have hcn := not_listed hw hc hca
  have keep : ∀ x ∈ H.cells, x.addr ≠ c.addr → x.addr ≠ m.addr → x ∈ (modelB H c m).cells :=
    fun x hx h1 h2 => (hmem x).mpr (Or.inr ⟨Or.inr ⟨hx, h1⟩, h2⟩)
  have hc'm : cellB c m ∈ (modelB H c m).cells := (hmem _).mpr (Or.inr ⟨Or.inl rfl, hcm⟩)
  have hm'm : nbrB c m ∈ (modelB H c m).cells := (hmem _).mpr (Or.inl rfl)
  refine ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt, ?_, ?_, ?_⟩
  · apply geo_map (H' := modelB H c m) hw.geo (upd m.addr (nbrB c m) ∘ upd c.addr (cellB c m)) rfl rfl
      (List.map_map)
    intro x hx
    by_cases h1 : x.addr = c.addr
    · obtain rfl : x = c := mem_unique hnd hx hc h1
      simp [upd, cellB, hcm]
    · by_cases h2 : x.addr = m.addr
      · obtain rfl : x = m := mem_unique hnd hx hm h2
        simp [upd, nbrB, h1]
      · simp [upd, h1, h2]
  · by_cases hml : m.addr ∈ H.freeList
    · have hi : H.freeList[H.freeList.idxOf m.addr]? = some m.addr := List.getElem?_idxOf hml
      -- `m.next_free` is a list link, so it fits in 32 bits
      have hmn : m.nextFree < 2 ^ 32 := by
        obtain ⟨x, hx, hxl⟩ := hw.lists.link_q _ _ hi
        obtain ⟨hxm, hxa⟩ := (cellAt_iff' hnd).mp hx
        rw [mem_unique hnd hxm hm hxa] at hxl
        have : (H.freeList[H.freeList.idxOf m.addr + 1]?).getD 0 < 2 ^ 32 := by
          cases hn : H.freeList[H.freeList.idxOf m.addr + 1]? with
          | none => simp
          | some a =>
            obtain ⟨y, hy, -⟩ := hw.lists.fl_free a (List.mem_of_getElem? hn)
            obtain ⟨hym, hya⟩ := (cellAt_iff' hnd).mp hy
            have := hw.geo.bounds y hym; have := hw.len_lt
            simp only [Option.getD_some]; omega
        omega
      have := lists_insert (F' := F + 1) hw.lists (modelB H c m).cells hnd hnd'
        (Nat.succ_le_succ hw.lists.fl_len) hi hm hc'm rfl hcn
        (by simp only [cellB]; omega) (by simp only [cellB]; omega) (hw.geo.bounds c hc).2.2.2
        hm'm rfl hmf rfl hmprev
        (fun x hx hxl hxm => ⟨x, keep x hx (fun e => hcn (e ▸ hxl)) hxm, rfl, rfl, rfl, fun _ => rfl⟩)
      simp only [modelB, listB, hml, ↓reduceIte]; exact this
    · have := lists_same (F' := F + 1) hw.lists (modelB H c m).cells hnd hnd' (Nat.le_succ F)
        (fun x hx hxl => ⟨x, keep x hx (fun e => hcn (e ▸ hxl)) (fun e => hml (e ▸ hxl)),
          rfl, rfl, rfl, fun _ => rfl⟩)
      simp only [modelB, listB, hml, ↓reduceIte]; exact this
  · apply lives_erase hw.lives hc hs
    · intro z hz hza
      rcases (hmem z).mp hz with rfl | ⟨rfl | ⟨hz, hzc⟩, hzm⟩
      · simp [nbrB, hmf] at hza
      · simp [cellB] at hza
      · exact ⟨z, hz, hza, rfl, hzc⟩
    · intro x hx hxa hxc
      have hxm : x.addr ≠ m.addr := by
        intro e; obtain rfl : x = m := mem_unique hnd hx hm e; rw [hmf] at hxa; cases hxa
      exact ⟨x, keep x hx hxc hxm, hxa, rfl, rfl⟩

/-- Case A, merge into the free previous neighbour `p`: `p` grows to `c`'s end. -/
def cellA (p c : CellM) : CellM := { p with next := c.next, last := c.last }

/-- The next neighbour `m` of `c` (if any) gets `p` as previous neighbour. -/
def nbrA (p m : CellM) : CellM := { m with prev := p.addr }

def modelA1 (H : HeapModel) (c p : CellM) : HeapModel :=
  { H with cells := (H.cells.erase c).map (upd p.addr (cellA p c)) }

def modelA2 (H : HeapModel) (c p m : CellM) : HeapModel :=
  { H with cells := ((H.cells.erase c).map (upd p.addr (cellA p c))).map (upd m.addr (nbrA p m)) }

/-- The previous neighbour of `c` from clause (2). -/
theorem prev_facts {p : CellM} (hp : p ∈ H.cells) (hpa : p.addr = c.prev) (hp0 : c.prev ≠ 0) :
    p.next = c.addr ∧ p.last = false := by
  obtain ⟨d, hd, hda, hdn, hdl⟩ := hw.geo.prev_nb c hc hp0
  obtain rfl : d = p := mem_unique (hw.nodup hc hca) hd hp (hda.trans hpa.symm)
  exact ⟨hdn, hdl⟩

include hs in
theorem wf_caseA2 {p m : CellM} (hp : p ∈ H.cells) (hpa : p.addr = c.prev) (hp0 : c.prev ≠ 0)
    (hpf : p.allocated = false) (hm : m ∈ H.cells) (hmaddr : m.addr = c.next) (hlast : c.last = false)
    (hmprev : m.prev = c.addr) :
    WfFix (modelA2 H c p m) (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  obtain ⟨hpn, hpl⟩ := prev_facts hw hc hca hp hpa hp0
  have bc := hw.geo.bounds c hc
  have bp := hw.geo.bounds p hp
  have bm := hw.geo.bounds m hm
  have a1 : p.addr ≠ c.addr := by omega
  have a2 : m.addr ≠ c.addr := by omega
  have a3 : m.addr ≠ p.addr := by omega
  have hmemE := fun z => mem_erase_iff' (z := z) hnd hc
  have hmem1 := fun z => mem_map_upd (L := H.cells.erase c) (z := z) (a := p.addr) (y := cellA p c) rfl
    ⟨p, (hmemE p).mpr ⟨hp, a1⟩, rfl⟩
  have hex2 : ∃ x ∈ (H.cells.erase c).map (upd p.addr (cellA p c)), x.addr = m.addr :=
    ⟨m, (hmem1 m).mpr (Or.inr ⟨(hmemE m).mpr ⟨hm, a2⟩, a3⟩), rfl⟩
  have hmem : ∀ z, z ∈ (modelA2 H c p m).cells ↔ z = nbrA p m ∨ z = cellA p c ∨
      (z ∈ H.cells ∧ z.addr ≠ c.addr ∧ z.addr ≠ p.addr ∧ z.addr ≠ m.addr) := by
    intro z
    show z ∈ ((H.cells.erase c).map (upd p.addr (cellA p c))).map (upd m.addr (nbrA p m)) ↔ _
    rw [mem_map_upd (a := m.addr) (y := nbrA p m) rfl hex2, hmem1, hmemE]
    constructor
    · rintro (h | ⟨h | ⟨⟨h1, h2⟩, h3⟩, h4⟩)
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨h1, h2, h3, h4⟩)
    · rintro (h | h | ⟨h1, h2, h3, h4⟩)
      · exact Or.inl h
      · subst h; exact Or.inr ⟨Or.inl rfl, by simpa [cellA] using a3.symm⟩
      · exact Or.inr ⟨Or.inr ⟨⟨h1, h2⟩, h3⟩, h4⟩
  have hnd' : ((modelA2 H c p m).cells.map CellM.addr).Nodup := by
    show ((((H.cells.erase c).map (upd p.addr (cellA p c))).map (upd m.addr (nbrA p m))).map
      CellM.addr).Nodup
    rw [addrs_map_upd (a := m.addr) (y := nbrA p m) rfl, addrs_map_upd (a := p.addr) (y := cellA p c) rfl]
    exact hnd.sublist ((List.erase_sublist).map _)
  have old : ∀ x ∈ H.cells, x.addr ≠ c.addr → x.addr ≠ p.addr → x.addr ≠ m.addr →
      x ∈ (modelA2 H c p m).cells := fun x hx h1 h2 h3 => (hmem x).mpr (Or.inr (Or.inr ⟨hx, h1, h2, h3⟩))
  have hm' : nbrA p m ∈ (modelA2 H c p m).cells := (hmem _).mpr (Or.inl rfl)
  have hp' : cellA p c ∈ (modelA2 H c p m).cells := (hmem _).mpr (Or.inr (Or.inl rfl))
  have U := fun {x y : CellM} (hx : x ∈ H.cells) (hy : y ∈ H.cells) (e : x.addr = y.addr) =>
    mem_unique hnd hx hy e
  have hcn := not_listed hw hc hca
  refine ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z hz
    rcases (hmem z).mp hz with rfl | rfl | ⟨hz, -⟩
    · exact bm
    · simp only [cellA]; refine ⟨bp.1, by omega, bc.2.2.1, bp.2.2.2⟩
    · exact hw.geo.bounds z hz
  · intro z hz
    rcases (hmem z).mp hz with rfl | rfl | ⟨hz, -⟩
    · exact hw.geo.next_al m hm
    · exact hw.geo.next_al c hc
    · exact hw.geo.next_al z hz
  · show ((((H.cells.erase c).map (upd p.addr (cellA p c))).map (upd m.addr (nbrA p m))).map
      CellM.addr).Pairwise _
    rw [addrs_map_upd (a := m.addr) (y := nbrA p m) rfl, addrs_map_upd (a := p.addr) (y := cellA p c) rfl]
    exact hw.geo.sorted.sublist ((List.erase_sublist).map _)
  · intro z hz hzl
    rcases (hmem z).mp hz with rfl | rfl | ⟨hz, z1, z2, z3⟩
    · obtain ⟨d, hd, hda, hdp⟩ := hw.geo.next_nb m hm hzl
      have := hw.geo.bounds d hd; have := hw.geo.bounds m hm
      exact ⟨d, old d hd (by omega) (by omega) (by omega), hda, hdp⟩
    · exact ⟨nbrA p m, hm', hmaddr, rfl⟩
    · obtain ⟨d, hd, hda, hdp⟩ := hw.geo.next_nb z hz hzl
      by_cases e1 : d.addr = c.addr
      · obtain rfl := U hd hc e1; exact absurd (hdp.symm.trans hpa.symm) z2
      by_cases e2 : d.addr = p.addr
      · obtain rfl := U hd hp e2; exact ⟨cellA d c, hp', hda, hdp⟩
      by_cases e3 : d.addr = m.addr
      · obtain rfl := U hd hm e3; exact absurd (hdp.symm.trans hmprev) z1
      exact ⟨d, old d hd e1 e2 e3, hda, hdp⟩
  · intro z hz hzp
    rcases (hmem z).mp hz with rfl | rfl | ⟨hz, z1, z2, z3⟩
    · exact ⟨cellA p c, hp', rfl, hmaddr.symm, hlast⟩
    · obtain ⟨d, hd, hda, hdn, hdl⟩ := hw.geo.prev_nb p hp hzp
      have := hw.geo.bounds d hd
      have e1 : d.addr ≠ c.addr := by
        intro e; obtain rfl := U hd hc e; omega
      have e2 : d.addr ≠ p.addr := by omega
      have e3 : d.addr ≠ m.addr := by
        intro e; obtain rfl := U hd hm e; omega
      exact ⟨d, old d hd e1 e2 e3, hda, hdn, hdl⟩
    · obtain ⟨d, hd, hda, hdn, hdl⟩ := hw.geo.prev_nb z hz hzp
      by_cases e1 : d.addr = c.addr
      · obtain rfl := U hd hc e1; exact absurd (hdn.symm.trans hmaddr.symm) z3
      by_cases e2 : d.addr = p.addr
      · obtain rfl := U hd hp e2; exact absurd (hdn.symm.trans hpn) z1
      by_cases e3 : d.addr = m.addr
      · obtain rfl := U hd hm e3; exact ⟨nbrA p d, hm', hda, hdn, hdl⟩
      exact ⟨d, old d hd e1 e2 e3, hda, hdn, hdl⟩
  · intro z hz hz0
    rcases (hmem z).mp hz with rfl | rfl | ⟨hz, -⟩
    · exact absurd (hpa.symm.trans (hz0 : p.addr = 0)) hp0
    · exact hw.geo.first p hp hz0
    · exact hw.geo.first z hz hz0
  · apply lists_same (F' := F + 1) hw.lists _ hnd hnd' (Nat.le_succ F)
    intro x hx hxl
    have hxc : x.addr ≠ c.addr := fun e => hcn (e ▸ hxl)
    by_cases e2 : x.addr = p.addr
    · obtain rfl := U hx hp e2; exact ⟨cellA x c, hp', rfl, rfl, rfl, fun _ => rfl⟩
    by_cases e3 : x.addr = m.addr
    · obtain rfl := U hx hm e3
      refine ⟨nbrA p x, hm', rfl, rfl, rfl, fun hodd => ?_⟩
      exfalso
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hxl
      obtain ⟨d, -, hd2, hd3, hd4⟩ := hw.lists.merge_q i _ hi x ((cellAt_iff' hnd).mpr ⟨hx, rfl⟩) hodd
      obtain ⟨hdm, -⟩ := (cellAt_iff' hnd).mp hd2
      obtain rfl := U hdm hc (hd4.symm.trans hmprev)
      rw [hca] at hd3; cases hd3
    exact ⟨x, old x hx hxc e2 e3, rfl, rfl, rfl, fun _ => rfl⟩
  · apply lives_erase hw.lives hc hs
    · intro z hz hza
      rcases (hmem z).mp hz with rfl | rfl | ⟨hz, z1, -, -⟩
      · exact ⟨m, hm, hza, rfl, a2⟩
      · simp [cellA, hpf] at hza
      · exact ⟨z, hz, hza, rfl, z1⟩
    · intro x hx hxa hxc
      by_cases e2 : x.addr = p.addr
      · obtain rfl := U hx hp e2; rw [hpf] at hxa; cases hxa
      by_cases e3 : x.addr = m.addr
      · obtain rfl := U hx hm e3; exact ⟨nbrA p x, hm', hxa, rfl, rfl⟩
      exact ⟨x, old x hx hxc e2 e3, hxa, rfl, rfl⟩

include hs in
theorem wf_caseA1 {p : CellM} (hp : p ∈ H.cells) (hpa : p.addr = c.prev) (hp0 : c.prev ≠ 0)
    (hpf : p.allocated = false) (hlast : c.last = true) :
    WfFix (modelA1 H c p) (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  obtain ⟨hpn, hpl⟩ := prev_facts hw hc hca hp hpa hp0
  have bc := hw.geo.bounds c hc
  have bp := hw.geo.bounds p hp
  have a1 : p.addr ≠ c.addr := by omega
  have hmemE := fun z => mem_erase_iff' (z := z) hnd hc
  have hmem1 := fun z => mem_map_upd (L := H.cells.erase c) (z := z) (a := p.addr) (y := cellA p c) rfl
    ⟨p, (hmemE p).mpr ⟨hp, a1⟩, rfl⟩
  have hmem : ∀ z, z ∈ (modelA1 H c p).cells ↔ z = cellA p c ∨
      (z ∈ H.cells ∧ z.addr ≠ c.addr ∧ z.addr ≠ p.addr) := by
    intro z
    show z ∈ (H.cells.erase c).map (upd p.addr (cellA p c)) ↔ _
    rw [hmem1, hmemE]
    constructor
    · rintro (h | ⟨⟨h1, h2⟩, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1, h2, h3⟩
    · rintro (h | ⟨h1, h2, h3⟩)
      · exact Or.inl h
      · exact Or.inr ⟨⟨h1, h2⟩, h3⟩
  have hnd' : ((modelA1 H c p).cells.map CellM.addr).Nodup := by
    show (((H.cells.erase c).map (upd p.addr (cellA p c))).map CellM.addr).Nodup
    rw [addrs_map_upd (a := p.addr) (y := cellA p c) rfl]
    exact hnd.sublist ((List.erase_sublist).map _)
  have old : ∀ x ∈ H.cells, x.addr ≠ c.addr → x.addr ≠ p.addr → x ∈ (modelA1 H c p).cells :=
    fun x hx h1 h2 => (hmem x).mpr (Or.inr ⟨hx, h1, h2⟩)
  have hp' : cellA p c ∈ (modelA1 H c p).cells := (hmem _).mpr (Or.inl rfl)
  have U := fun {x y : CellM} (hx : x ∈ H.cells) (hy : y ∈ H.cells) (e : x.addr = y.addr) =>
    mem_unique hnd hx hy e
  have hcn := not_listed hw hc hca
  refine ⟨hw.mem0_al, hw.len_al, hw.mem0_le, hw.len_lt, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro z hz
    rcases (hmem z).mp hz with rfl | ⟨hz, -⟩
    · simp only [cellA]; refine ⟨bp.1, by omega, bc.2.2.1, bp.2.2.2⟩
    · exact hw.geo.bounds z hz
  · intro z hz
    rcases (hmem z).mp hz with rfl | ⟨hz, -⟩
    · exact hw.geo.next_al c hc
    · exact hw.geo.next_al z hz
  · show (((H.cells.erase c).map (upd p.addr (cellA p c))).map CellM.addr).Pairwise _
    rw [addrs_map_upd (a := p.addr) (y := cellA p c) rfl]
    exact hw.geo.sorted.sublist ((List.erase_sublist).map _)
  · intro z hz hzl
    rcases (hmem z).mp hz with rfl | ⟨hz, z1, z2⟩
    · simp [cellA, hlast] at hzl
    · obtain ⟨d, hd, hda, hdp⟩ := hw.geo.next_nb z hz hzl
      by_cases e1 : d.addr = c.addr
      · obtain rfl := U hd hc e1; exact absurd (hdp.symm.trans hpa.symm) z2
      by_cases e2 : d.addr = p.addr
      · obtain rfl := U hd hp e2; exact ⟨cellA d c, hp', hda, hdp⟩
      exact ⟨d, old d hd e1 e2, hda, hdp⟩
  · intro z hz hzp
    rcases (hmem z).mp hz with rfl | ⟨hz, z1, z2⟩
    · obtain ⟨d, hd, hda, hdn, hdl⟩ := hw.geo.prev_nb p hp hzp
      have := hw.geo.bounds d hd
      have e1 : d.addr ≠ c.addr := by
        intro e; obtain rfl := U hd hc e; omega
      have e2 : d.addr ≠ p.addr := by omega
      exact ⟨d, old d hd e1 e2, hda, hdn, hdl⟩
    · obtain ⟨d, hd, hda, hdn, hdl⟩ := hw.geo.prev_nb z hz hzp
      by_cases e1 : d.addr = c.addr
      · obtain rfl := U hd hc e1; rw [hlast] at hdl; cases hdl
      by_cases e2 : d.addr = p.addr
      · obtain rfl := U hd hp e2; exact absurd (hdn.symm.trans hpn) z1
      exact ⟨d, old d hd e1 e2, hda, hdn, hdl⟩
  · intro z hz hz0
    rcases (hmem z).mp hz with rfl | ⟨hz, -⟩
    · exact hw.geo.first p hp hz0
    · exact hw.geo.first z hz hz0
  · apply lists_same (F' := F + 1) hw.lists _ hnd hnd' (Nat.le_succ F)
    intro x hx hxl
    have hxc : x.addr ≠ c.addr := fun e => hcn (e ▸ hxl)
    by_cases e2 : x.addr = p.addr
    · obtain rfl := U hx hp e2; exact ⟨cellA x c, hp', rfl, rfl, rfl, fun _ => rfl⟩
    exact ⟨x, old x hx hxc e2, rfl, rfl, rfl, fun _ => rfl⟩
  · apply lives_erase hw.lives hc hs
    · intro z hz hza
      rcases (hmem z).mp hz with rfl | ⟨hz, z1, -⟩
      · simp [cellA, hpf] at hza
      · exact ⟨z, hz, hza, rfl, z1⟩
    · intro x hx hxa hxc
      by_cases e2 : x.addr = p.addr
      · obtain rfl := U hx hp e2; rw [hpf] at hxa; cases hxa
      exact ⟨x, old x hx hxc e2, hxa, rfl, rfl⟩

end Cases


theorem erase_map_upd {L : List CellM} {a : Nat} {x y : CellM} (hxa : x.addr ≠ a) (hyx : y ≠ x) :
    (L.map (upd a y)).erase x = (L.erase x).map (upd a y) := by
  induction L with
  | nil => rfl
  | cons h t ih =>
    by_cases hh : h = x
    · subst hh
      simp [upd, hxa]
    · have hu : upd a y h ≠ x := by unfold upd; split <;> assumption
      rw [List.map_cons, List.erase_cons_tail (by simpa using hu), List.erase_cons_tail (by simpa using hh),
        List.map_cons, ih]

/-! ## Resources -/

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

theorem nodup_sublist_erase {L : List CellM} {x : CellM} (hnd : (L.map CellM.addr).Nodup) :
    ((L.erase x).map CellM.addr).Nodup := hnd.sublist ((List.erase_sublist).map _)

omit [WasmGS NearState GF] in
theorem bigSep_extract {Φ : CellM → IProp GF} {L : List CellM} {x : CellM} (hx : x ∈ L) :
    ([∗list] y ∈ L, Φ y) ⊣⊢ Φ x ∗ [∗list] y ∈ L.erase x, Φ y :=
  (BigSepL.bigSepL_perm (List.perm_cons_erase hx)).trans BigSepL.bigSepL_cons

omit [WasmGS NearState GF] in
theorem bigSep_upd {Φ : CellM → IProp GF} {L : List CellM} {a : Nat} {x y : CellM}
    (hnd : (L.map CellM.addr).Nodup) (hx : x ∈ L) (hxa : x.addr = a) (hy : y.addr = a) :
    ([∗list] z ∈ L.map (upd a y), Φ z) ⊣⊢ Φ y ∗ [∗list] z ∈ L.erase x, Φ z :=
  (BigSepL.bigSepL_perm (perm_map_upd hnd hx hxa hy)).trans BigSepL.bigSepL_cons

theorem cellRes_erase (n : Nat) {live : List (Nat × Nat)} {a s : Nat} {x : CellM} (hx : x.addr ≠ a) :
    cellRes (GF := GF) n live x ⊢ cellRes n (live.erase (a + 8, s)) x := by
  unfold cellRes
  iintro ⟨H0, H1, H2⟩
  iframe H0 H1
  split
  · icases H2 with ⟨%s', %bs, %⟨h1, h2⟩, H⟩
    iexists s', bs
    iframe H
    ipureintro
    refine ⟨List.mem_erase_of_ne (by intro e; simp at e; omega) |>.mpr h1, h2⟩
  · iexact H2

theorem bigSep_erase (n : Nat) {live : List (Nat × Nat)} {a s : Nat} {R : List CellM}
    (hR : ∀ x ∈ R, x.addr ≠ a) :
    ([∗list] x ∈ R, cellRes (GF := GF) n live x) ⊢ [∗list] x ∈ R, cellRes n (live.erase (a + 8, s)) x :=
  BigSepL.bigSepL_mono (fun hk => cellRes_erase n (hR _ (List.mem_of_getElem? hk)))

theorem cellRes_alloc (n : Nat) {live : List (Nat × Nat)} {x : CellM} (h : x.allocated = true) :
    cellRes (GF := GF) n live x ⊣⊢ iprop(n ↦[wms][ x.addr ] bytes32 (UInt32.ofNat x.word0) ∗
      n ↦[wms][ x.addr + 4 ] bytes32 (UInt32.ofNat x.prev) ∗
      ∃ s bs, ⌜(x.addr + 8, s) ∈ live ∧ bs.length = x.size - s⌝ ∗ n ↦[wms][ x.addr + 8 + s ] bs) := by
  unfold cellRes; simp only [h, ↓reduceIte]; exact .rfl

theorem cellRes_free (n : Nat) {live : List (Nat × Nat)} {x : CellM} (h : x.allocated = false) :
    cellRes (GF := GF) n live x ⊣⊢ iprop(n ↦[wms][ x.addr ] bytes32 (UInt32.ofNat x.word0) ∗
      n ↦[wms][ x.addr + 4 ] bytes32 (UInt32.ofNat x.prev) ∗
      ∃ bs, ⌜bs.length + 4 = x.size⌝ ∗ n ↦[wms][ x.addr + 8 ] bytes32 (UInt32.ofNat x.nextFree) ∗
        n ↦[wms][ x.addr + 12 ] bs) := by
  unfold cellRes; simp only [h, Bool.false_eq_true, ↓reduceIte]; exact .rfl


/-! ## Closing the invariant after each case -/

theorem memBytes_at {n a b : Nat} {bs bs' : List UInt8} (h : a = b) (h' : bs = bs') :
    n ↦[wms][ a ] bs ⊢ (n ↦[wms][ b ] bs' : IProp GF) := by
  subst h h'; exact .rfl

theorem cellRes_free_intro {n : Nat} {live : List (Nat × Nat)} (x : CellM) (h : x.allocated = false)
    {a : Nat} {w0 w1 nf : UInt32} (ha : x.addr = a) (h0 : UInt32.ofNat x.word0 = w0)
    (h1 : UInt32.ofNat x.prev = w1) (h2 : UInt32.ofNat x.nextFree = nf) (bs : List UInt8)
    (hbs : bs.length + 4 = x.size) :
    n ↦[i32][ a ] w0 ∗ n ↦[i32][ a + 4 ] w1 ∗ n ↦[i32][ a + 8 ] nf ∗ n ↦[wms][ a + 12 ] bs
      ⊢ cellRes (GF := GF) n live x := by
  subst ha h0 h1 h2
  iintro ⟨H0, H1, H2, H3⟩
  iapply (cellRes_free n h).2
  iframe H0 H1
  iexists bs
  iframe H2 H3
  ipureintro; exact hbs

/-- Case C, push. -/
theorem finC {n maxP F s : Nat} {H : HeapModel} {live : List (Nat × Nat)} {c : CellM}
    (hw : WfFix H live F) (hc : c ∈ H.cells) (hca : c.allocated = true) (hs : (c.addr + 8, s) ∈ live)
    (hmax : H.len ≤ maxP * 65536) (w0 : UInt32)
    (hw0 : w0 = UInt32.ofNat (c.next + if c.last = true then 2 else 0)) (dr : List UInt8)
    (hdr : dr.length = c.size - 4) :
    n ↦[i32][ 1074896 ] UInt32.ofNat c.addr ∗ n ↦[wmlength] H.len ∗ n ↪[wmlimit] some maxP ∗
      ([∗list] y ∈ H.cells.erase c, cellRes n live y) ∗
      n ↦[i32][ c.addr ] w0 ∗ n ↦[i32][ c.addr + 4 ] UInt32.ofNat c.prev ∗
      n ↦[i32][ c.addr + 8 ] UInt32.ofNat H.head ∗ n ↦[wms][ c.addr + 8 + 4 ] dr
      ⊢ heapInvFix (GF := GF) n maxP (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  have bc := hw.geo.bounds c hc
  iintro ⟨Hh, Hl, Hm, Hrest, Hw0, Hw1, Hnf, Hdr⟩
  iunfold heapInvFix
  iexists modelC H c
  isplitr
  · ipureintro; exact ⟨wf_caseC hw hc hca hs, hmax⟩
  have hhd : (modelC H c).head = c.addr := rfl
  rw [hhd, show headAddr = 1074896 from rfl, show (modelC H c).len = H.len from rfl,
    show (modelC H c).cells = H.cells.map (upd c.addr (cellC H c)) from rfl]
  iframe Hh Hl Hm
  iapply (bigSep_upd (Φ := cellRes n (live.erase (c.addr + 8, s))) (a := c.addr) (y := cellC H c)
    hnd hc rfl rfl).2
  isplitr [Hrest]
  · ihave Hdr := memBytes_at (n := n) (a := c.addr + 8 + 4) (b := c.addr + 12) (by omega) rfl $$ Hdr
    iapply cellRes_free_intro (a := c.addr) (w0 := w0) (w1 := UInt32.ofNat c.prev)
      (nf := UInt32.ofNat H.head) (cellC H c) rfl rfl
      (by rw [hw0]; unfold cellC CellM.word0; cases c.last <;> rfl) rfl rfl dr
      (by simp only [cellC, CellM.size]; unfold CellM.size at hdr; omega)
    iframe Hw0 Hw1 Hnf Hdr
  · iapply bigSep_erase n (fun x hx => ?_) $$ Hrest
    intro e
    exact (List.Nodup.mem_erase_iff (nodup_of_map hnd)).mp hx |>.1 (mem_unique hnd
      ((List.Nodup.mem_erase_iff (nodup_of_map hnd)).mp hx).2 hc e)


/-- The cells other than `c` keep their resources when `c`'s allocation is freed. -/
theorem rest_erase {n : Nat} {H : HeapModel} {live : List (Nat × Nat)} {c : CellM} {s : Nat}
    (hnd : (H.cells.map CellM.addr).Nodup) (hc : c ∈ H.cells) {R : List CellM}
    (hR : ∀ x ∈ R, x ∈ H.cells.erase c) :
    ([∗list] y ∈ R, cellRes n live y) ⊢
      [∗list] y ∈ R, cellRes (GF := GF) n (live.erase (c.addr + 8, s)) y :=
  bigSep_erase n fun x hx e =>
    ((List.Nodup.mem_erase_iff (nodup_of_map hnd)).mp (hR x hx)).1
      (mem_unique hnd ((List.Nodup.mem_erase_iff (nodup_of_map hnd)).mp (hR x hx)).2 hc e)

/-- Case B, link after the free next neighbour `m`. -/
theorem finB {n maxP F s : Nat} {H : HeapModel} {live : List (Nat × Nat)} {c m : CellM}
    (hw : WfFix H live F) (hc : c ∈ H.cells) (hca : c.allocated = true) (hs : (c.addr + 8, s) ∈ live)
    (hmax : H.len ≤ maxP * 65536) (hm : m ∈ H.cells) (hmaddr : m.addr = c.next)
    (hlast : c.last = false) (hmprev : m.prev = c.addr) (hmf : m.allocated = false)
    (w0 nf mnf : UInt32) (hw0 : w0 = UInt32.ofNat (c.next + if c.last = true then 2 else 0))
    (hnf : nf = UInt32.ofNat (m.nextFree % 2 ^ 32 / 4 * 4)) (hmnf : mnf = UInt32.ofNat (c.addr + 1))
    (dr : List UInt8) (hdr : dr.length = c.size - 4) (mbs : List UInt8) (hmbs : mbs.length + 4 = m.size) :
    n ↦[i32][ 1074896 ] UInt32.ofNat H.head ∗ n ↦[wmlength] H.len ∗ n ↪[wmlimit] some maxP ∗
      ([∗list] y ∈ (H.cells.erase c).erase m, cellRes n live y) ∗
      n ↦[i32][ c.addr ] w0 ∗ n ↦[i32][ c.addr + 4 ] UInt32.ofNat c.prev ∗
      n ↦[i32][ c.addr + 8 ] nf ∗ n ↦[wms][ c.addr + 8 + 4 ] dr ∗
      n ↦[i32][ m.addr ] UInt32.ofNat m.word0 ∗ n ↦[i32][ m.addr + 4 ] UInt32.ofNat m.prev ∗
      n ↦[i32][ m.addr + 8 ] mnf ∗ n ↦[wms][ m.addr + 12 ] mbs
      ⊢ heapInvFix (GF := GF) n maxP (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  have bc := hw.geo.bounds c hc
  have hcm : m.addr ≠ c.addr := by omega
  iintro ⟨Hh, Hl, Hm, Hrest, Hw0, Hw1, Hnf, Hdr, Hm0, Hm1, Hmnf, Hmbs⟩
  iunfold heapInvFix
  iexists modelB H c m
  isplitr
  · ipureintro; exact ⟨wf_caseB hw hc hca hs hm hmaddr hlast hmprev hmf, hmax⟩
  rw [modelB_head hw hc hca, show headAddr = 1074896 from rfl, show (modelB H c m).len = H.len from rfl,
    show (modelB H c m).cells = (H.cells.map (upd c.addr (cellB c m))).map (upd m.addr (nbrB c m)) from rfl]
  iframe Hh Hl Hm
  have hnd1 : ((H.cells.map (upd c.addr (cellB c m))).map CellM.addr).Nodup := by
    rw [addrs_map_upd (a := c.addr) (y := cellB c m) rfl]; exact hnd
  have hm1 : m ∈ H.cells.map (upd c.addr (cellB c m)) :=
    (mem_map_upd (a := c.addr) (y := cellB c m) rfl ⟨c, hc, rfl⟩).mpr (Or.inr ⟨hm, hcm⟩)
  iapply (bigSep_upd (Φ := cellRes n (live.erase (c.addr + 8, s))) (a := m.addr) (y := nbrB c m)
    hnd1 hm1 rfl rfl).2
  have hne : cellB c m ≠ m := fun e => hcm (by rw [← e]; rfl)
  rw [erase_map_upd hcm hne]
  have hmE : c ∈ H.cells.erase m :=
    (mem_erase_iff' hnd hm).mpr ⟨hc, fun e => hcm e.symm⟩
  isplitl [Hm0 Hm1 Hmnf Hmbs]
  · iapply cellRes_free_intro (a := m.addr) (w0 := UInt32.ofNat m.word0) (w1 := UInt32.ofNat m.prev)
      (nf := mnf) (nbrB c m) hmf rfl rfl rfl (by rw [hmnf]; rfl) mbs hmbs
    iframe Hm0 Hm1 Hmnf Hmbs
  iapply (bigSep_upd (Φ := cellRes n (live.erase (c.addr + 8, s))) (a := c.addr) (y := cellB c m)
    (nodup_sublist_erase hnd) hmE rfl rfl).2
  rw [List.erase_comm m c]
  isplitr [Hrest]
  · ihave Hdr := memBytes_at (n := n) (a := c.addr + 8 + 4) (b := c.addr + 12) (by omega) rfl $$ Hdr
    iapply cellRes_free_intro (a := c.addr) (w0 := w0) (w1 := UInt32.ofNat c.prev)
      (nf := nf) (cellB c m) rfl rfl
      (by rw [hw0]; unfold cellB CellM.word0; cases c.last <;> rfl) rfl (by rw [hnf]; rfl) dr
      (by simp only [cellB, CellM.size]; unfold CellM.size at hdr; omega)
    iframe Hw0 Hw1 Hnf Hdr
  · iapply rest_erase hnd hc (fun x hx => List.mem_of_mem_erase hx) $$ Hrest


/-- The data part of `cellRes` (after the two header words). -/
def cellData (n : Nat) (live : List (Nat × Nat)) (x : CellM) : IProp GF :=
  if x.allocated then
    iprop(∃ s bs, ⌜(x.addr + 8, s) ∈ live ∧ bs.length = x.size - s⌝ ∗ n ↦[wms][ x.addr + 8 + s ] bs)
  else
    iprop(∃ bs, ⌜bs.length + 4 = x.size⌝ ∗ n ↦[wms][ x.addr + 8 ] bytes32 (UInt32.ofNat x.nextFree) ∗
      n ↦[wms][ x.addr + 12 ] bs)

theorem cellRes_split (n : Nat) (live : List (Nat × Nat)) (x : CellM) :
    cellRes (GF := GF) n live x ⊣⊢ iprop(n ↦[i32][ x.addr ] UInt32.ofNat x.word0 ∗
      n ↦[i32][ x.addr + 4 ] UInt32.ofNat x.prev ∗ cellData n live x) := by
  unfold cellRes cellData; exact .rfl

theorem cellData_nbr (n : Nat) (live : List (Nat × Nat)) {a s : Nat} (x y : CellM) (hxa : x.addr ≠ a)
    (h1 : y.addr = x.addr) (h2 : y.allocated = x.allocated) (h3 : y.next = x.next)
    (h4 : y.nextFree = x.nextFree) :
    cellData (GF := GF) n live x ⊢ cellData n (live.erase (a + 8, s)) y := by
  have hs : y.size = x.size := by unfold CellM.size; rw [h1, h3]
  unfold cellData
  rw [h1, h2, hs, h4]
  split
  · iintro ⟨%s', %bs, %⟨h1, h2⟩, H⟩
    iexists s', bs
    iframe H
    ipureintro
    exact ⟨List.mem_erase_of_ne (by intro e; simp at e; omega) |>.mpr h1, h2⟩
  · iintro H; iexact H

/-- Case A, merge into the free previous neighbour `p`: the bytes from `p`'s data to `c`'s
end become `p`'s data. -/
theorem finA_cell {n : Nat} {live : List (Nat × Nat)} {c p : CellM}
    (bc : c.addr + 24 ≤ c.next) (hpn : p.next = c.addr) (bp : p.addr + 24 ≤ p.next)
    (hpf : p.allocated = false) (wp : UInt32) (hwp : wp = UInt32.ofNat (c.next + if c.last = true then 2 else 0))
    (pbs : List UInt8) (hpbs : pbs.length + 4 = p.size) (wc0 wc1 wd : UInt32) (dr : List UInt8)
    (hdr : dr.length = c.size - 4) :
    n ↦[i32][ p.addr ] wp ∗ n ↦[i32][ p.addr + 4 ] UInt32.ofNat p.prev ∗
      n ↦[i32][ p.addr + 8 ] UInt32.ofNat p.nextFree ∗ n ↦[wms][ p.addr + 12 ] pbs ∗
      n ↦[i32][ c.addr ] wc0 ∗ n ↦[i32][ c.addr + 4 ] wc1 ∗ n ↦[i32][ c.addr + 8 ] wd ∗
      n ↦[wms][ c.addr + 8 + 4 ] dr
      ⊢ cellRes (GF := GF) n live (cellA p c) := by
  iintro ⟨Hp0, Hp1, Hpnf, Hpbs, Hc0, Hc1, Hd, Hdr⟩
  have hl : (pbs ++ bytes32 wc0 ++ bytes32 wc1 ++ bytes32 wd ++ dr).length + 4 = (cellA p c).size := by
    simp only [List.length_append, bytes32_length, cellA, CellM.size]
    unfold CellM.size at hpbs hdr; omega
  have e1 : p.addr + 12 + pbs.length = c.addr := by unfold CellM.size at hpbs; omega
  ihave H1 := memBytes_join n (p.addr + 12) pbs.length pbs (bytes32 wc0) rfl $$ [Hpbs Hc0]
  · iframe Hpbs; iapply memBytes_at e1.symm rfl $$ Hc0
  ihave H2 := memBytes_join n (p.addr + 12) (pbs ++ bytes32 wc0).length _ (bytes32 wc1) rfl $$ [H1 Hc1]
  · iframe H1; iapply memBytes_at (by simp; omega) rfl $$ Hc1
  ihave H3 := memBytes_join n (p.addr + 12) (pbs ++ bytes32 wc0 ++ bytes32 wc1).length _ (bytes32 wd) rfl
    $$ [H2 Hd]
  · iframe H2; iapply memBytes_at (by simp; omega) rfl $$ Hd
  ihave H4 := memBytes_join n (p.addr + 12) (pbs ++ bytes32 wc0 ++ bytes32 wc1 ++ bytes32 wd).length _ dr rfl
    $$ [H3 Hdr]
  · iframe H3; iapply memBytes_at (by simp; omega) rfl $$ Hdr
  iapply cellRes_free_intro (a := p.addr) (w0 := wp) (w1 := UInt32.ofNat p.prev)
    (nf := UInt32.ofNat p.nextFree) (cellA p c) hpf rfl
    (by rw [hwp]; unfold cellA CellM.word0; rw [hpf]; cases c.last <;> rfl) rfl rfl _ hl
  iframe Hp0 Hp1 Hpnf H4

/-- Case A with a next neighbour `m` (now `p`'s). -/
theorem finA2 {n maxP F s : Nat} {H : HeapModel} {live : List (Nat × Nat)} {c p m : CellM}
    (hw : WfFix H live F) (hc : c ∈ H.cells) (hca : c.allocated = true) (hs : (c.addr + 8, s) ∈ live)
    (hmax : H.len ≤ maxP * 65536) (hp : p ∈ H.cells) (hpa : p.addr = c.prev) (hp0 : c.prev ≠ 0)
    (hpf : p.allocated = false) (hm : m ∈ H.cells) (hmaddr : m.addr = c.next)
    (hlast : c.last = false) (hmprev : m.prev = c.addr)
    (wp : UInt32) (hwp : wp = UInt32.ofNat (c.next + if c.last = true then 2 else 0))
    (pbs : List UInt8) (hpbs : pbs.length + 4 = p.size) (wc0 wc1 wd : UInt32) (dr : List UInt8)
    (hdr : dr.length = c.size - 4) (wm1 : UInt32) (hwm1 : wm1 = UInt32.ofNat p.addr) :
    n ↦[i32][ 1074896 ] UInt32.ofNat H.head ∗ n ↦[wmlength] H.len ∗ n ↪[wmlimit] some maxP ∗
      ([∗list] y ∈ ((H.cells.erase c).erase p).erase m, cellRes n live y) ∗
      n ↦[i32][ p.addr ] wp ∗ n ↦[i32][ p.addr + 4 ] UInt32.ofNat p.prev ∗
      n ↦[i32][ p.addr + 8 ] UInt32.ofNat p.nextFree ∗ n ↦[wms][ p.addr + 12 ] pbs ∗
      n ↦[i32][ c.addr ] wc0 ∗ n ↦[i32][ c.addr + 4 ] wc1 ∗ n ↦[i32][ c.addr + 8 ] wd ∗
      n ↦[wms][ c.addr + 8 + 4 ] dr ∗
      n ↦[i32][ m.addr ] UInt32.ofNat m.word0 ∗ n ↦[i32][ m.addr + 4 ] wm1 ∗ cellData n live m
      ⊢ heapInvFix (GF := GF) n maxP (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  obtain ⟨hpn, hpl⟩ := prev_facts hw hc hca hp hpa hp0
  have bc := hw.geo.bounds c hc
  have bp := hw.geo.bounds p hp
  have a1 : p.addr ≠ c.addr := by omega
  have a2 : m.addr ≠ c.addr := by omega
  have a3 : m.addr ≠ p.addr := by omega
  iintro ⟨Hh, Hl, Hm, Hrest, Hp0, Hp1, Hpnf, Hpbs, Hc0, Hc1, Hd, Hdr, Hm0, Hm1, Hmd⟩
  iunfold heapInvFix
  iexists modelA2 H c p m
  isplitr
  · ipureintro; exact ⟨wf_caseA2 hw hc hca hs hp hpa hp0 hpf hm hmaddr hlast hmprev, hmax⟩
  rw [show (modelA2 H c p m).head = H.head from rfl, show headAddr = 1074896 from rfl,
    show (modelA2 H c p m).len = H.len from rfl,
    show (modelA2 H c p m).cells =
      ((H.cells.erase c).map (upd p.addr (cellA p c))).map (upd m.addr (nbrA p m)) from rfl]
  iframe Hh Hl Hm
  have hpE : p ∈ H.cells.erase c := (mem_erase_iff' hnd hc).mpr ⟨hp, a1⟩
  have hmE : m ∈ H.cells.erase c := (mem_erase_iff' hnd hc).mpr ⟨hm, a2⟩
  have hnd0 := nodup_sublist_erase (x := c) hnd
  have hnd1 : (((H.cells.erase c).map (upd p.addr (cellA p c))).map CellM.addr).Nodup := by
    rw [addrs_map_upd (a := p.addr) (y := cellA p c) rfl]; exact hnd0
  have hm1 : m ∈ (H.cells.erase c).map (upd p.addr (cellA p c)) :=
    (mem_map_upd (a := p.addr) (y := cellA p c) rfl ⟨p, hpE, rfl⟩).mpr (Or.inr ⟨hmE, a3⟩)
  iapply (bigSep_upd (Φ := cellRes n (live.erase (c.addr + 8, s))) (a := m.addr) (y := nbrA p m)
    hnd1 hm1 rfl rfl).2
  have hne : cellA p c ≠ m := fun e => a3 (by rw [← e]; rfl)
  rw [erase_map_upd a3 hne]
  have hpE2 : p ∈ (H.cells.erase c).erase m := (mem_erase_iff' hnd0 hmE).mpr ⟨hpE, fun e => a3 e.symm⟩
  isplitl [Hm0 Hm1 Hmd]
  · iapply (cellRes_split n _ (nbrA p m)).2
    isplitl [Hm0]
    · iapply (memBytes_at (n := n) (a := m.addr) (b := (nbrA p m).addr) (bs := bytes32 (UInt32.ofNat m.word0))
        (bs' := bytes32 (UInt32.ofNat (nbrA p m).word0)) rfl rfl); iexact Hm0
    isplitl [Hm1]
    · iapply (memBytes_at (n := n) (a := m.addr + 4) (b := (nbrA p m).addr + 4) (bs := bytes32 wm1)
        (bs' := bytes32 (UInt32.ofNat (nbrA p m).prev)) rfl (by rw [hwm1]; rfl)); iexact Hm1
    iapply cellData_nbr n live m (nbrA p m) a2 rfl rfl rfl rfl $$ Hmd
  iapply (bigSep_upd (Φ := cellRes n (live.erase (c.addr + 8, s))) (a := p.addr) (y := cellA p c)
    (nodup_sublist_erase hnd0) hpE2 rfl rfl).2
  rw [List.erase_comm m p]
  isplitr [Hrest]
  · iapply finA_cell bc.2.1 hpn bp.2.1 hpf wp hwp pbs hpbs wc0 wc1 wd dr hdr
    iframe Hp0 Hp1 Hpnf Hpbs Hc0 Hc1 Hd Hdr
  · iapply rest_erase hnd hc (fun x hx => List.mem_of_mem_erase (List.mem_of_mem_erase hx)) $$ Hrest

/-- Case A, `c` the last cell of its chunk. -/
theorem finA1 {n maxP F s : Nat} {H : HeapModel} {live : List (Nat × Nat)} {c p : CellM}
    (hw : WfFix H live F) (hc : c ∈ H.cells) (hca : c.allocated = true) (hs : (c.addr + 8, s) ∈ live)
    (hmax : H.len ≤ maxP * 65536) (hp : p ∈ H.cells) (hpa : p.addr = c.prev) (hp0 : c.prev ≠ 0)
    (hpf : p.allocated = false) (hlast : c.last = true)
    (wp : UInt32) (hwp : wp = UInt32.ofNat (c.next + if c.last = true then 2 else 0))
    (pbs : List UInt8) (hpbs : pbs.length + 4 = p.size) (wc0 wc1 wd : UInt32) (dr : List UInt8)
    (hdr : dr.length = c.size - 4) :
    n ↦[i32][ 1074896 ] UInt32.ofNat H.head ∗ n ↦[wmlength] H.len ∗ n ↪[wmlimit] some maxP ∗
      ([∗list] y ∈ (H.cells.erase c).erase p, cellRes n live y) ∗
      n ↦[i32][ p.addr ] wp ∗ n ↦[i32][ p.addr + 4 ] UInt32.ofNat p.prev ∗
      n ↦[i32][ p.addr + 8 ] UInt32.ofNat p.nextFree ∗ n ↦[wms][ p.addr + 12 ] pbs ∗
      n ↦[i32][ c.addr ] wc0 ∗ n ↦[i32][ c.addr + 4 ] wc1 ∗ n ↦[i32][ c.addr + 8 ] wd ∗
      n ↦[wms][ c.addr + 8 + 4 ] dr
      ⊢ heapInvFix (GF := GF) n maxP (live.erase (c.addr + 8, s)) (F + 1) := by
  have hnd := hw.nodup hc hca
  obtain ⟨hpn, hpl⟩ := prev_facts hw hc hca hp hpa hp0
  have bc := hw.geo.bounds c hc
  have bp := hw.geo.bounds p hp
  have a1 : p.addr ≠ c.addr := by omega
  iintro ⟨Hh, Hl, Hm, Hrest, Hp0, Hp1, Hpnf, Hpbs, Hc0, Hc1, Hd, Hdr⟩
  iunfold heapInvFix
  iexists modelA1 H c p
  isplitr
  · ipureintro; exact ⟨wf_caseA1 hw hc hca hs hp hpa hp0 hpf hlast, hmax⟩
  rw [show (modelA1 H c p).head = H.head from rfl, show headAddr = 1074896 from rfl,
    show (modelA1 H c p).len = H.len from rfl,
    show (modelA1 H c p).cells = (H.cells.erase c).map (upd p.addr (cellA p c)) from rfl]
  iframe Hh Hl Hm
  have hpE : p ∈ H.cells.erase c := (mem_erase_iff' hnd hc).mpr ⟨hp, a1⟩
  iapply (bigSep_upd (Φ := cellRes n (live.erase (c.addr + 8, s))) (a := p.addr) (y := cellA p c)
    (nodup_sublist_erase hnd) hpE rfl rfl).2
  isplitr [Hrest]
  · iapply finA_cell bc.2.1 hpn bp.2.1 hpf wp hwp pbs hpbs wc0 wc1 wd dr hdr
    iframe Hp0 Hp1 Hpnf Hpbs Hc0 Hc1 Hd Hdr
  · iapply rest_erase hnd hc (fun x hx => List.mem_of_mem_erase hx) $$ Hrest

end Res


/-! ## `i32.load8_u` of a header's low byte -/

theorem decode_take1 (w : UInt32) :
    Memory.decodeLE ((bytes32 w).take 1) = w.toNat % 256 := by
  simp [bytes32, Memory.decodeLE, List.range, List.range.loop]

section Load8

variable {GF : BundledGFunctors} [WasmGS NearState GF]
variable {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {f : Frame} {vs : List Value}
  {Φ : Post NearState GF} {Cg K : Nat}

open WNear.Binary.U128From (memBytes_split memBytes_join) in
/-- `i32.load8_u` of the low byte of a word owned whole. -/
theorem mwpi_load8u_w {arg : MemArg} {rest : List Value} {a : UInt32} {n addr : Nat} {w : UInt32} :
    credits Cg K ∗ ⌜vs.reverse = .i32 a :: rest ∧ a.toNat + arg.offset = addr ∧
        cfg.regularOpCost ≤ K ∧ f.mi.memAddrs[0]? = some n⌝ ∗ n ↦[wms][ addr ] bytes32 w ∗
      ▷ (credits Cg (K - cfg.regularOpCost) -∗ n ↦[wms][ addr ] bytes32 w -∗
          Φ.normal (rest.reverse ++ [.i32 (UInt32.ofNat (w.toNat % 256))]) f)
      ⊢ mwpi cfg lim d f vs [.load .i32 (some ⟨8, false⟩) arg] Φ := by
  iintro ⟨Hc, %⟨hs, ha, hK, hn⟩, Hw, H⟩
  icases memBytes_split n addr 1 (bytes32 w) (by simp) $$ Hw with ⟨H1, H3⟩
  iapply mwpi_load_at'
  iframe Hc
  isplitr
  · ipureintro; exact hs
  iframe H1
  isplitr
  · ipureintro; exact ha
  isplitr
  · ipureintro; exact ⟨hK, hn, by simp [loadWidth, bytes32], by simp [bytes32]⟩
  inext
  iintro Hc H1
  ihave Hw := memBytes_join n addr 1 ((bytes32 w).take 1) ((bytes32 w).drop 1) (by simp [bytes32]) $$ [H1 H3]
  · iframe H1 H3
  rw [List.take_append_drop]
  simp only [loadValue, decode_take1, Bool.false_eq_true, ↓reduceIte]
  iapply H $$ Hc Hw

end Load8


/-! ## `u32` facts for the stepping -/

theorem bool_eqz_zero {x : UInt32} (h : x.toNat ≠ 0) : Numeric.bool (x == 0) = 0 := by
  have : x ≠ 0 := fun e => h (by subst e; rfl)
  simp [Numeric.bool, this]

theorem bool_eqz_ne {x : UInt32} (h : x.toNat = 0) : Numeric.bool (x == 0) ≠ 0 := by
  have : x = 0 := UInt32.toNat_inj.mp h
  simp [Numeric.bool, this]

theorem clr_alloc (x L : Nat) (hx : x % 4 = 0) (hL : L = 0 ∨ L = 2) (h : x + 3 < 2 ^ 32) :
    UInt32.ofNat (x + L + 1) &&& 4294967294 = UInt32.ofNat (x + L) := by
  apply UInt32.toNat_inj.mp; rw [u32_and_mask2]; simp only [UInt32.toNat_ofNat']; omega

theorem mask4_ofNat (x L : Nat) (hx : x % 4 = 0) (hL : L < 4) (h : x + 3 < 2 ^ 32) :
    UInt32.ofNat (x + L) &&& 4294967292 = UInt32.ofNat x := by
  apply UInt32.toNat_inj.mp; rw [u32_and_mask4]; simp only [UInt32.toNat_ofNat']; omega

theorem sub8_eq (ptr : UInt32) (a : Nat) (h : ptr.toNat = a + 8) : ptr + 4294967288 = UInt32.ofNat a := by
  apply UInt32.toNat_inj.mp; have := ptr.toNat_lt; rw [UInt32.toNat_add]; simp; omega

theorem sub4_eq (ptr : UInt32) (a : Nat) (h : ptr.toNat = a + 8) : ptr + 4294967292 = UInt32.ofNat (a + 4) := by
  apply UInt32.toNat_inj.mp; have := ptr.toNat_lt; rw [UInt32.toNat_add]; simp; omega

theorem ofNat_toNat_lt (a : Nat) (h : a < 2 ^ 32) : (UInt32.ofNat a).toNat = a := by
  simp only [UInt32.toNat_ofNat']; omega

theorem mask4_self (x : Nat) (hx : x % 4 = 0) (h : x < 2 ^ 32) :
    UInt32.ofNat x &&& 4294967292 = UInt32.ofNat x := by
  apply UInt32.toNat_inj.mp; rw [u32_and_mask4]; simp only [UInt32.toNat_ofNat']; omega
theorem and2_ofNat (x L : Nat) (hx : x % 4 = 0) (hL : L = 0 ∨ L = 2) (h : x + 3 < 2 ^ 32) :
    UInt32.ofNat (x + L) &&& 2 = UInt32.ofNat L := by
  apply UInt32.toNat_inj.mp; rw [u32_and_2]; simp only [UInt32.toNat_ofNat']; omega
theorem byte_and1 (w : Nat) (h : w < 2 ^ 32) :
    UInt32.ofNat ((UInt32.ofNat w).toNat % 256) &&& 1 = UInt32.ofNat (w % 2) := by
  apply UInt32.toNat_inj.mp; rw [u32_and_1]; simp only [UInt32.toNat_ofNat']; omega
theorem byte_and2 (w : Nat) (h : w < 2 ^ 32) :
    UInt32.ofNat ((UInt32.ofNat w).toNat % 256) &&& 2 = UInt32.ofNat (w % 4 / 2 * 2) := by
  apply UInt32.toNat_inj.mp; rw [u32_and_2]; simp only [UInt32.toNat_ofNat']; omega

theorem or1_ofNat (x : Nat) (hx : x % 4 = 0) (h : x + 3 < 2 ^ 32) :
    UInt32.ofNat x ||| 1 = UInt32.ofNat (x + 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, show (1 : UInt32).toNat = 1 from rfl, nat_or_low _ _ (by decide)]
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show x < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show x + 1 < 2 ^ 32 by omega), hx, Nat.reduceOr]; omega

theorem mask4_nf (x : Nat) :
    UInt32.ofNat x &&& 4294967292 = UInt32.ofNat (x % 2 ^ 32 / 4 * 4) := by
  apply UInt32.toNat_inj.mp; rw [u32_and_mask4]; simp only [UInt32.toNat_ofNat']; omega

theorem nextOf_last (x : Nat) (hx : x % 4 = 0) (h : x + 3 < 2 ^ 32) : nextOf (UInt32.ofNat (x + 2)) = 0 := by
  unfold nextOf
  have : UInt32.ofNat (x + 2) &&& 2 ≠ 0 := by
    intro e; have := congrArg UInt32.toNat e; rw [u32_and_2] at this; simp only [UInt32.toNat_ofNat'] at this
    simp at this; omega
  simp only [this, ↓reduceIte]
theorem nextOf_nolast (x : Nat) (hx : x % 4 = 0) (h : x + 3 < 2 ^ 32) :
    nextOf (UInt32.ofNat x) = UInt32.ofNat x := by
  unfold nextOf
  have e1 : UInt32.ofNat x &&& 2 = 0 := by
    apply UInt32.toNat_inj.mp; rw [u32_and_2]; simp only [UInt32.toNat_ofNat']; simp; omega
  have e2 : UInt32.ofNat x &&& 4294967292 = UInt32.ofNat x := by
    apply UInt32.toNat_inj.mp; rw [u32_and_mask4]; simp only [UInt32.toNat_ofNat']; omega
  simp only [e1, e2, ↓reduceIte]
theorem and3_ofNat (x L : Nat) (hx : x % 4 = 0) (hL : L < 4) (h : x + 3 < 2 ^ 32) :
    UInt32.ofNat (x + L) &&& 3 = UInt32.ofNat L := by
  apply UInt32.toNat_inj.mp; rw [u32_and_3]; simp only [UInt32.toNat_ofNat']; omega
theorem or_mask3 (a b : Nat) (ha : a % 4 = 0) (ha' : a < 2 ^ 32) (hb : b % 4 = 0) (hb' : b < 2 ^ 32) :
    (UInt32.ofNat a &&& 3) ||| UInt32.ofNat b = UInt32.ofNat b := by
  apply UInt32.toNat_inj.mp
  rw [u32_or_disj _ _ (by rw [u32_and_3]; omega) (by simp only [UInt32.toNat_ofNat']; omega), u32_and_3]
  simp only [UInt32.toNat_ofNat']; omega
theorem and3_self (x : Nat) (hx : x % 4 = 0) (h : x < 2 ^ 32) : UInt32.ofNat x &&& 3 = 0 := by
  apply UInt32.toNat_inj.mp; rw [u32_and_3]; simp only [UInt32.toNat_ofNat']; simp; omega

theorem or2_ofNat (x : Nat) (hx : x % 4 = 0) (h : x + 3 < 2 ^ 32) :
    UInt32.ofNat x ||| 2 = UInt32.ofNat (x + 2) := by
  apply UInt32.toNat_inj.mp; rw [u32_or_2]; simp only [UInt32.toNat_ofNat']; omega

section Spec
variable {GF : BundledGFunctors} [WasmGS NearState GF]

set_option maxRecDepth 20000 in
set_option maxHeartbeats 8000000 in
theorem f582_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a570 a568 a576 a575 : Nat)
    (h570 : mi.funcAddrs[570]? = some a570) (h568 : mi.funcAddrs[568]? = some a568)
    (h576 : mi.funcAddrs[576]? = some a576) (h575 : mi.funcAddrs[575]? = some a575)
    (ty570 ty568 ty576 ty575 : FuncType)
    (hp570 : ty570.params.length = 1) (hr570 : ty570.results.length = 1)
    (hp568 : ty568.params.length = 2) (hr568 : ty568.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp575 : ty575.params.length = 1) (hr575 : ty575.results.length = 0)
    (hd : d + 2 < lim.maxCallDepth) (Cg maxP : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ptr size align : UInt32) :
    a570 ↪[wf] FuncInst.wasm ty570 inst f570 ∗ a568 ↪[wf] FuncInst.wasm ty568 inst f568 ∗
      a576 ↪[wf] FuncInst.wasm ty576 inst f576 ∗ a575 ↪[wf] FuncInst.wasm ty575 inst f575 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f582 Cg
        (fun args => iprop(⌜args = [.i32 1074896, .i32 ptr, .i32 size, .i32 align]⌝ ∗
          ⌜(ptr.toNat, size.toNat) ∈ live⌝ ∗ heapInvFix n maxP live F ∗ block n ptr.toNat size.toNat))
        (fun _ => 224 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ heapInvFix n maxP (live.erase (ptr.toNat, size.toNat)) (F + 1))) := by
  iintro ⟨#H570, #H568, #H576, #H575, #Hi⟩
  iapply MFunSpec_intro
  imodintro
  iintro %args %R ⟨%hargs, %hlive, Hinv, Hblk⟩ Hc
  subst hargs
  iunfold heapInvFix at Hinv
  icases Hinv with ⟨%H, %⟨hw, hmax⟩, Hh, Hl, Hm, Hcells⟩
  obtain ⟨hpos, c, hc, hca, hpc, hsz⟩ := hw.lives.live_cell _ _ hlive
  have hnd := hw.nodup hc hca
  have bc := hw.geo.bounds c hc
  have hlen := hw.len_lt
  icases (bigSep_extract hc).1 $$ Hcells with ⟨Hcr, Hrest⟩
  icases (cellRes_alloc n hca).1 $$ Hcr with ⟨Hw0, Hw1, %s', %bs, %⟨hs1, hs2⟩, Hslack⟩
  obtain rfl : s' = size.toNat := by
    have := map_inj_of_nodup hw.lives.live_nodup hs1 hlive (by simp [hpc])
    simp at this; exact this.symm.1
  iunfold block at Hblk
  icases Hblk with ⟨%bb, %hbb, Hb⟩
  ihave Hb := memBytes_addr (b := c.addr + 8) hpc $$ Hb
  ihave Hdata := memBytes_join n (c.addr + 8) size.toNat bb bs hbb $$ [Hb Hslack]
  · iframe Hb Hslack
  have hdl : (bb ++ bs).length = c.size := by simp [hbb, hs2]; omega
  have hcs : 16 ≤ c.size := by unfold CellM.size; omega
  icases memBytes_split n (c.addr + 8) 4 (bb ++ bs) (by omega) $$ Hdata with ⟨Hd4, Hdr⟩
  have hd4l : ((bb ++ bs).take 4).length = 4 := by rw [List.length_take]; omega
  have hdrl : ((bb ++ bs).drop 4).length = c.size - 4 := by rw [List.length_drop]; omega
  generalize (bb ++ bs).take 4 = d4 at hd4l ⊢
  generalize (bb ++ bs).drop 4 = dr at hdrl ⊢
  clear hs2 hbb hdl
  have hw0 : c.word0 = c.next + (if c.last then 2 else 0) + 1 := by simp [CellM.word0, hca]
  have hna := hw.geo.next_al c hc
  have hsize : size.toNat + 4 < 2 ^ 32 := by unfold CellM.size at hsz; omega
  unfold headAddr
  simp only [f582]
  mstep; mstep; mstep
  mstep_not_taken with (apply bool_eqz_zero; omega)
  mstep; mstep
  mstep_not_taken with (apply bool_eqz_zero; omega)
  mstep
  mcall (f570_spec cfg lim (d + 1) ty570 hr570 inst mi a568 h568 ty568 hp568 hr568 (by omega) Cg size hsize)
    with (simp [activationGas, entryLocals, f570, hp570]; omega)
  · ipureintro; trivial
  icases HQ with %hrs
  subst hrs
  mstep; mstep; mstep [Hh]
  mstep; mstep; mstep; mstep
  rw [sub8_eq ptr c.addr hpc]
  mstep; mstep; mstep [Hw0]; mstep; mstep; mstep [Hw0]
  have hL : (if c.last = true then 2 else 0) = 0 ∨ (if c.last = true then 2 else 0) = 2 := by
    split <;> simp
  rw [hw0, clr_alloc _ _ hna hL (by omega)]
  mstep
  have s576 := f576_spec (GF := GF) cfg lim (d + 1) ty576 hr576 inst mi n hn Cg (UInt32.ofNat c.addr)
    (UInt32.ofNat (c.next + if c.last = true then 2 else 0))
    (by rw [ofNat_toNat_lt _ (by omega)]; omega)
    (by rw [mask4_ofNat _ _ hna (by omega) (by omega), ofNat_toNat_lt _ (by omega),
      ofNat_toNat_lt _ (by omega)]; omega)
  rw [ofNat_toNat_lt _ (by omega)] at s576
  mcall s576 using [Hw0] with (simp [activationGas, entryLocals, f576, hp576]; omega)
  · iframe Hw0
  icases HQ with ⟨%hrs, Hw0⟩
  subst hrs
  clear s576
  mstep; mstep; mstep; mstep [Hd4]
  mstep; mstep; mstep; mstep; mstep; mstep; mstep
  rw [sub4_eq ptr c.addr hpc]
  mstep [Hw1]
  have hprev4 : c.prev % 4 = 0 ∧ c.prev < 2 ^ 32 := by
    by_cases h0 : c.prev = 0
    · rw [h0]; decide
    · obtain ⟨d, hd, hda, -, -⟩ := hw.geo.prev_nb c hc h0
      have := hw.geo.bounds d hd; omega
  mstep; mstep
  rw [mask4_self _ hprev4.1 hprev4.2]
  mstep; mstep
  by_cases hp0 : c.prev = 0
  · mstep_taken with (apply bool_eqz_ne; rw [hp0]; rfl)
    mstep; mstep [Hw0]; mstep; mstep; mstep
    rw [mask4_ofNat _ _ hna (by split <;> decide) (by omega)]
    mstep; mstep
    mstep_not_taken with (apply bool_eqz_zero; rw [ofNat_toNat_lt _ (by omega)]; omega)
    mstep; mstep; mstep; mstep; mstep
    rw [and2_ofNat _ _ hna hL (by omega)]
    by_cases hl : c.last = true
    · simp only [hl, ↓reduceIte]
      iapply mwpi_cons; iapply mwpi_select_ite; isplitl [Hc]; iexact Hc
      isplitr; ipureintro; exact ⟨rfl, by omega⟩
      inext; iintro Hc
      simp only [show UInt32.ofNat 2 ≠ 0 by decide, ↓reduceIte]
      mctrl_norm
      mstep; mstep
      mstep_taken with (apply bool_eqz_ne; rfl)
      mstep; mstep; mstep [Hd4]; mstep; mstep; mstep [Hh]
      rw [hpc]
      mcredits R
      iframe Hc
      isplitr; · ipureintro; trivial
      iapply finC hw hc hca hs1 hmax (UInt32.ofNat (c.next + 2)) (by simp only [hl, ↓reduceIte]) dr hdrl
      iframe Hh Hl Hm Hrest Hw0 Hw1 Hd4 Hdr
    · have hl' : c.last = false := by simpa using hl
      simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      iapply mwpi_cons; iapply mwpi_select_ite; isplitl [Hc]; iexact Hc
      isplitr; ipureintro; exact ⟨rfl, by omega⟩
      inext; iintro Hc
      simp only [show UInt32.ofNat 0 = 0 from rfl, ↓reduceIte]
      mctrl_norm
      mstep; mstep
      mstep_not_taken with (apply bool_eqz_zero; rw [ofNat_toNat_lt _ (by omega)]; omega)
      obtain ⟨m, hm, hmaddr, hmprev⟩ := hw.geo.next_nb c hc hl'
      have bm := hw.geo.bounds m hm
      have hmE : m ∈ H.cells.erase c := (mem_erase_iff' hnd hc).mpr ⟨hm, by omega⟩
      icases (bigSep_extract hmE).1 $$ Hrest with ⟨Hmr, Hrest⟩
      have hmna := hw.geo.next_al m hm
      have hmw : m.word0 < 2 ^ 32 := by unfold CellM.word0; split <;> split <;> omega
      by_cases hmf : m.allocated = false
      · icases (cellRes_free n hmf).1 $$ Hmr with ⟨Hm0, Hm1, %mbs, %hmbs, Hmnf, Hmbs⟩
        mstep
        iapply mwpi_cons; iapply mwpi_load8u_w (addr := m.addr) (w := UInt32.ofNat m.word0)
        iframe Hc; isplitr
        · ipureintro; exact ⟨rfl, by rw [ofNat_toNat_lt _ (by omega)]; exact (Nat.add_zero _).trans hmaddr.symm, by omega, hn⟩
        iframe Hm0; inext; iintro Hc Hm0; mctrl_norm
        mstep; mstep
        rw [byte_and1 _ hmw, show m.word0 % 2 = 0 by unfold CellM.word0; rw [hmf]; simp only [Bool.false_eq_true, ↓reduceIte]; split <;> omega]
        mstep_not_taken with rfl
        mstep; mstep; mstep [Hmnf]; mstep; mstep; mstep [Hd4]
        mstep; mstep; mstep; mstep; mstep [Hmnf]; mstep; mstep; mstep
        mstep; mstep; mstep [Hh]
        rw [hpc]
        mcredits R
        iframe Hc
        isplitr; · ipureintro; trivial
        iapply finB hw hc hca hs1 hmax hm hmaddr hl' hmprev hmf (UInt32.ofNat c.next)
          (UInt32.ofNat m.nextFree &&& 4294967292) (UInt32.ofNat c.addr ||| 1)
          (by simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]) (mask4_nf _)
          (or1_ofNat _ bc.2.2.2 (by omega)) dr hdrl mbs hmbs
        iframe Hh Hl Hm Hrest Hw0 Hw1 Hd4 Hdr Hm0 Hm1 Hmnf Hmbs
      · have hma : m.allocated = true := by simpa using hmf
        icases (cellRes_alloc n hma).1 $$ Hmr with ⟨Hm0, Hm1, Hmd⟩
        mstep
        iapply mwpi_cons; iapply mwpi_load8u_w (addr := m.addr) (w := UInt32.ofNat m.word0)
        iframe Hc; isplitr
        · ipureintro; exact ⟨rfl, by rw [ofNat_toNat_lt _ (by omega)]; exact (Nat.add_zero _).trans hmaddr.symm, by omega, hn⟩
        iframe Hm0; inext; iintro Hc Hm0; mctrl_norm
        mstep; mstep
        rw [byte_and1 _ hmw, show m.word0 % 2 = 1 by unfold CellM.word0; rw [hma]; simp only [↓reduceIte]; split <;> omega]
        mstep_taken with (decide)
        ihave Hmr := (cellRes_alloc n hma).2 $$ [Hm0 Hm1 Hmd]
        · iframe Hm0 Hm1 Hmd
        ihave Hrest := (bigSep_extract hmE).2 $$ [Hmr Hrest]
        · iframe Hmr Hrest
        mstep; mstep; mstep [Hd4]; mstep; mstep; mstep [Hh]
        rw [hpc]
        mcredits R
        iframe Hc
        isplitr; · ipureintro; trivial
        iapply finC hw hc hca hs1 hmax (UInt32.ofNat c.next)
          (by simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]) dr hdrl
        iframe Hh Hl Hm Hrest Hw0 Hw1 Hd4 Hdr
  · mstep_not_taken with (apply bool_eqz_zero; rw [ofNat_toNat_lt _ hprev4.2]; exact hp0)
    obtain ⟨p, hp, hpa, hpn, hpl⟩ := hw.geo.prev_nb c hc hp0
    have bp := hw.geo.bounds p hp
    have hpna := hw.geo.next_al p hp
    have hpE : p ∈ H.cells.erase c := (mem_erase_iff' hnd hc).mpr ⟨hp, by omega⟩
    icases (bigSep_extract hpE).1 $$ Hrest with ⟨Hpr, Hrest⟩
    have hpw : p.word0 < 2 ^ 32 := by unfold CellM.word0; split <;> split <;> omega
    have hcp : (UInt32.ofNat c.prev).toNat = p.addr := by rw [ofNat_toNat_lt _ hprev4.2]; exact hpa.symm
    by_cases hpf : p.allocated = false
    · icases (cellRes_free n hpf).1 $$ Hpr with ⟨Hp0, Hp1, %pbs, %hpbs, Hpnf, Hpbs⟩
      have hpw0 : p.word0 = p.next := by unfold CellM.word0; rw [hpf, hpl]; rfl
      mstep
      iapply mwpi_cons; iapply mwpi_load8u_w (addr := p.addr) (w := UInt32.ofNat p.word0)
      iframe Hc; isplitr
      · ipureintro; exact ⟨rfl, by rw [hcp]; rfl, by omega, hn⟩
      iframe Hp0; inext; iintro Hc Hp0; mctrl_norm
      mstep; mstep
      rw [byte_and1 _ hpw, show p.word0 % 2 = 0 by omega]
      mstep
      mstep_taken with (apply bool_eqz_ne; rfl)
      have hpne : UInt32.ofNat c.prev ≠ 0 := fun e => hp0 (by
        have := congrArg UInt32.toNat e; rw [ofNat_toNat_lt _ hprev4.2] at this; exact this)
      by_cases hl : c.last = true
      · simp only [hl, ↓reduceIte]
        have s575 := f575_spec (GF := GF) cfg lim (d + 1) ty575 hr575 inst mi n hn Cg (UInt32.ofNat c.addr)
          (UInt32.ofNat (c.next + 2)) (UInt32.ofNat c.prev) (UInt32.ofNat p.word0) 0
        rw [nextOf_last _ hna (by omega), mask4_self _ hprev4.1 hprev4.2, hcp,
          ofNat_toNat_lt c.addr (by omega)] at s575
        simp only [ptsIf, ne_eq, not_true_eq_false, ↓reduceIte, hpne, not_false_eq_true] at s575
        mstep
        mcall s575 using [Hw0 Hw1 Hp0] with (simp [activationGas, entryLocals, f575, hp575]; omega)
        · iframe Hw0 Hw1 Hp0
        icases HQ with ⟨%hrs, Hw0, Hw1, -, Hp0⟩
        subst hrs
        clear s575
        rw [and3_ofNat _ 2 hna (by omega) (by omega), mask4_ofNat _ _ hna (by omega) (by omega),
          or_mask3 _ _ (by omega) hpw hna (by omega)]
        mstep; mstep
        iapply mwpi_cons; iapply mwpi_load8u_w (addr := c.addr) (w := UInt32.ofNat 2)
        iframe Hc; isplitr
        · ipureintro; exact ⟨rfl, by rw [ofNat_toNat_lt _ (by omega)]; rfl, by omega, hn⟩
        iframe Hw0; inext; iintro Hc Hw0; mctrl_norm
        mstep; mstep; mstep
        mstep_not_taken with decide
        mstep; mstep; mstep [Hp0]; mstep; mstep; mstep [Hp0]
        rw [or2_ofNat _ hna (by omega)]
        mstep
        have s576p := f576_spec (GF := GF) cfg lim (d + 1) ty576 hr576 inst mi n hn Cg (UInt32.ofNat c.prev)
          (UInt32.ofNat (c.next + 2)) (by rw [hcp]; omega)
          (by rw [mask4_ofNat _ _ hna (by omega) (by omega), hcp, ofNat_toNat_lt _ (by omega)]; omega)
        rw [hcp] at s576p
        mcall s576p using [Hp0] with (simp [activationGas, entryLocals, f576, hp576]; omega)
        · iframe Hp0
        icases HQ with ⟨%hrs, Hp0⟩
        subst hrs
        clear s576p
        mstep; mstep; mstep; mstep
        mstep; mstep; mstep [Hh]
        rw [hpc]
        mcredits R
        iframe Hc
        isplitr; · ipureintro; trivial
        iapply finA1 hw hc hca hs1 hmax hp hpa hp0 hpf hl (UInt32.ofNat (c.next + 2))
          (by simp only [hl, ↓reduceIte]) pbs hpbs (UInt32.ofNat 2) (UInt32.ofNat c.prev &&& 3) 0 dr hdrl
        iframe Hh Hl Hm Hrest Hp0 Hp1 Hpnf Hpbs Hw0 Hw1 Hd4 Hdr
      · have hl' : c.last = false := by simpa using hl
        simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        obtain ⟨m, hm, hmaddr, hmprev⟩ := hw.geo.next_nb c hc hl'
        have bm := hw.geo.bounds m hm
        have hmE2 : m ∈ (H.cells.erase c).erase p :=
          (mem_erase_iff' (z := m) (nodup_sublist_erase hnd) hpE).mpr
            ⟨(mem_erase_iff' (z := m) hnd hc).mpr ⟨hm, by omega⟩, by omega⟩
        icases (bigSep_extract hmE2).1 $$ Hrest with ⟨Hmr, Hrest⟩
        icases (cellRes_split n live m).1 $$ Hmr with ⟨Hm0, Hm1, Hmd⟩
        have hcne : UInt32.ofNat c.next ≠ 0 := fun e => by
          have := congrArg UInt32.toNat e; rw [ofNat_toNat_lt c.next (by omega)] at this; simp at this; omega
        have s575 := f575_spec (GF := GF) cfg lim (d + 1) ty575 hr575 inst mi n hn Cg (UInt32.ofNat c.addr)
          (UInt32.ofNat c.next) (UInt32.ofNat c.prev) (UInt32.ofNat p.word0) (UInt32.ofNat m.prev)
        rw [nextOf_nolast _ hna (by omega), mask4_self _ hprev4.1 hprev4.2, hcp,
          ofNat_toNat_lt c.addr (by omega), ofNat_toNat_lt c.next (by omega)] at s575
        simp only [ptsIf, ne_eq, hcne, hpne, not_false_eq_true, ↓reduceIte] at s575
        ihave Hm1 := memBytes_at (n := n) (a := m.addr + 4) (b := c.next + 4) (by omega) rfl $$ Hm1
        mstep
        mcall s575 using [Hw0 Hw1 Hm1 Hp0] with (simp [activationGas, entryLocals, f575, hp575]; omega)
        · iframe Hw0 Hw1 Hm1 Hp0
        icases HQ with ⟨%hrs, Hw0, Hw1, Hm1, Hp0⟩
        subst hrs
        clear s575
        have hmp4 : m.prev % 4 = 0 := by rw [hmprev]; exact bc.2.2.2
        rw [and3_self _ hna (by omega), mask4_self _ hna (by omega),
          or_mask3 _ _ hmp4 (by omega) hprev4.1 hprev4.2, or_mask3 _ _ (by omega) hpw hna (by omega)]
        mstep; mstep
        iapply mwpi_cons; iapply mwpi_load8u_w (addr := c.addr) (w := 0)
        iframe Hc; isplitr
        · ipureintro; exact ⟨rfl, by rw [ofNat_toNat_lt _ (by omega)]; rfl, by omega, hn⟩
        iframe Hw0; inext; iintro Hc Hw0; mctrl_norm
        mstep; mstep; mstep
        mstep_taken with decide
        mstep
        have s576p := f576_spec (GF := GF) cfg lim (d + 1) ty576 hr576 inst mi n hn Cg (UInt32.ofNat c.prev)
          (UInt32.ofNat c.next) (by rw [hcp]; omega)
          (by rw [mask4_self _ hna (by omega), hcp, ofNat_toNat_lt _ (by omega)]; omega)
        rw [hcp] at s576p
        mcall s576p using [Hp0] with (simp [activationGas, entryLocals, f576, hp576]; omega)
        · iframe Hp0
        icases HQ with ⟨%hrs, Hp0⟩
        subst hrs
        clear s576p
        mstep; mstep; mstep; mstep
        mstep; mstep; mstep [Hh]
        rw [hpc]
        mcredits R
        iframe Hc
        isplitr; · ipureintro; trivial
        ihave Hm1 := memBytes_at (n := n) (a := c.next + 4) (b := m.addr + 4) (by omega) rfl $$ Hm1
        iapply finA2 hw hc hca hs1 hmax hp hpa hp0 hpf hm hmaddr hl' hmprev (UInt32.ofNat c.next)
          (by simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]) pbs hpbs 0
          (UInt32.ofNat c.prev &&& 3) 0 dr hdrl (UInt32.ofNat c.prev) (by rw [hpa])
        iframe Hh Hl Hm Hrest Hp0 Hp1 Hpnf Hpbs Hw0 Hw1 Hd4 Hdr Hm0 Hm1 Hmd
    · have hpa' : p.allocated = true := by simpa using hpf
      icases (cellRes_alloc n hpa').1 $$ Hpr with ⟨Hp0, Hp1, Hpd⟩
      mstep
      iapply mwpi_cons; iapply mwpi_load8u_w (addr := p.addr) (w := UInt32.ofNat p.word0)
      iframe Hc; isplitr
      · ipureintro; exact ⟨rfl, by rw [hcp]; rfl, by omega, hn⟩
      iframe Hp0; inext; iintro Hc Hp0; mctrl_norm
      mstep; mstep
      rw [byte_and1 _ hpw, show p.word0 % 2 = 1 by unfold CellM.word0; rw [hpa']; simp only [↓reduceIte]; split <;> omega]
      mstep
      mstep_not_taken with (apply bool_eqz_zero; decide)
      ihave Hpr := (cellRes_alloc n hpa').2 $$ [Hp0 Hp1 Hpd]
      · iframe Hp0 Hp1 Hpd
      ihave Hrest := (bigSep_extract hpE).2 $$ [Hpr Hrest]
      · iframe Hpr Hrest
      mstep; mstep [Hw0]; mstep; mstep; mstep
      rw [mask4_ofNat _ _ hna (by split <;> decide) (by omega)]
      mstep; mstep
      mstep_not_taken with (apply bool_eqz_zero; rw [ofNat_toNat_lt _ (by omega)]; omega)
      mstep; mstep; mstep; mstep; mstep
      rw [and2_ofNat _ _ hna hL (by omega)]
      by_cases hl : c.last = true
      · simp only [hl, ↓reduceIte]
        iapply mwpi_cons; iapply mwpi_select_ite; isplitl [Hc]; iexact Hc
        isplitr; ipureintro; exact ⟨rfl, by omega⟩
        inext; iintro Hc
        simp only [show UInt32.ofNat 2 ≠ 0 by decide, ↓reduceIte]
        mctrl_norm
        mstep; mstep
        mstep_taken with (apply bool_eqz_ne; rfl)
        mstep; mstep; mstep [Hd4]; mstep; mstep; mstep [Hh]
        rw [hpc]
        mcredits R
        iframe Hc
        isplitr; · ipureintro; trivial
        iapply finC hw hc hca hs1 hmax (UInt32.ofNat (c.next + 2)) (by simp only [hl, ↓reduceIte]) dr hdrl
        iframe Hh Hl Hm Hrest Hw0 Hw1 Hd4 Hdr
      · have hl' : c.last = false := by simpa using hl
        simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        iapply mwpi_cons; iapply mwpi_select_ite; isplitl [Hc]; iexact Hc
        isplitr; ipureintro; exact ⟨rfl, by omega⟩
        inext; iintro Hc
        simp only [show UInt32.ofNat 0 = 0 from rfl, ↓reduceIte]
        mctrl_norm
        mstep; mstep
        mstep_not_taken with (apply bool_eqz_zero; rw [ofNat_toNat_lt _ (by omega)]; omega)
        obtain ⟨m, hm, hmaddr, hmprev⟩ := hw.geo.next_nb c hc hl'
        have bm := hw.geo.bounds m hm
        have hmE : m ∈ H.cells.erase c := (mem_erase_iff' hnd hc).mpr ⟨hm, by omega⟩
        icases (bigSep_extract hmE).1 $$ Hrest with ⟨Hmr, Hrest⟩
        have hmna := hw.geo.next_al m hm
        have hmw : m.word0 < 2 ^ 32 := by unfold CellM.word0; split <;> split <;> omega
        by_cases hmf : m.allocated = false
        · icases (cellRes_free n hmf).1 $$ Hmr with ⟨Hm0, Hm1, %mbs, %hmbs, Hmnf, Hmbs⟩
          mstep
          iapply mwpi_cons; iapply mwpi_load8u_w (addr := m.addr) (w := UInt32.ofNat m.word0)
          iframe Hc; isplitr
          · ipureintro; exact ⟨rfl, by rw [ofNat_toNat_lt _ (by omega)]; exact (Nat.add_zero _).trans hmaddr.symm, by omega, hn⟩
          iframe Hm0; inext; iintro Hc Hm0; mctrl_norm
          mstep; mstep
          rw [byte_and1 _ hmw, show m.word0 % 2 = 0 by unfold CellM.word0; rw [hmf]; simp only [Bool.false_eq_true, ↓reduceIte]; split <;> omega]
          mstep_not_taken with rfl
          mstep; mstep; mstep [Hmnf]; mstep; mstep; mstep [Hd4]
          mstep; mstep; mstep; mstep; mstep [Hmnf]; mstep; mstep; mstep
          mstep; mstep; mstep [Hh]
          rw [hpc]
          mcredits R
          iframe Hc
          isplitr; · ipureintro; trivial
          iapply finB hw hc hca hs1 hmax hm hmaddr hl' hmprev hmf (UInt32.ofNat c.next)
            (UInt32.ofNat m.nextFree &&& 4294967292) (UInt32.ofNat c.addr ||| 1)
            (by simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]) (mask4_nf _)
            (or1_ofNat _ bc.2.2.2 (by omega)) dr hdrl mbs hmbs
          iframe Hh Hl Hm Hrest Hw0 Hw1 Hd4 Hdr Hm0 Hm1 Hmnf Hmbs
        · have hma : m.allocated = true := by simpa using hmf
          icases (cellRes_alloc n hma).1 $$ Hmr with ⟨Hm0, Hm1, Hmd⟩
          mstep
          iapply mwpi_cons; iapply mwpi_load8u_w (addr := m.addr) (w := UInt32.ofNat m.word0)
          iframe Hc; isplitr
          · ipureintro; exact ⟨rfl, by rw [ofNat_toNat_lt _ (by omega)]; exact (Nat.add_zero _).trans hmaddr.symm, by omega, hn⟩
          iframe Hm0; inext; iintro Hc Hm0; mctrl_norm
          mstep; mstep
          rw [byte_and1 _ hmw, show m.word0 % 2 = 1 by unfold CellM.word0; rw [hma]; simp only [↓reduceIte]; split <;> omega]
          mstep_taken with (decide)
          ihave Hmr := (cellRes_alloc n hma).2 $$ [Hm0 Hm1 Hmd]
          · iframe Hm0 Hm1 Hmd
          ihave Hrest := (bigSep_extract hmE).2 $$ [Hmr Hrest]
          · iframe Hmr Hrest
          mstep; mstep; mstep [Hd4]; mstep; mstep; mstep [Hh]
          rw [hpc]
          mcredits R
          iframe Hc
          isplitr; · ipureintro; trivial
          iapply finC hw hc hca hs1 hmax (UInt32.ofNat c.next)
            (by simp only [hl', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]) dr hdrl
          iframe Hh Hl Hm Hrest Hw0 Hw1 Hd4 Hdr
end Spec

/-! ## `__rust_dealloc` (311) -/

section Wrap

variable {GF : BundledGFunctors} [WasmGS NearState GF]

instance MFunSpec_persistent {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P : List Value → IProp GF} {K : List Value → Nat}
    {Q : List Value → List Value → IProp GF} :
    Persistent (MFunSpec cfg lim d type inst mi code Cg P K Q) := by
  unfold MFunSpec; infer_instance

/-- A specification with a stronger precondition and the same cost, written differently. -/
theorem MFunSpec_conv {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P P' : List Value → IProp GF} {K K' : List Value → Nat}
    {Q : List Value → List Value → IProp GF} (hP : ∀ args, P' args ⊢ P args)
    (hK : ∀ args, K' args = K args) :
    MFunSpec cfg lim d type inst mi code Cg P K Q ⊢ MFunSpec cfg lim d type inst mi code Cg P' K' Q := by
  unfold MFunSpec
  iintro #H
  imodintro
  iintro %args %R HP Hc
  rw [hK]
  iapply H $$ %args %R [HP] Hc
  iapply hP $$ HP

/-- `__rust_dealloc(ptr, size, align)` (311 → 237 → 582): frees the live block `(ptr, size)`.
Cost `256 regular_op_cost`s at most (`15 + 17` for the shims, `224` for `dealloc`), the
activation of 311 excluded. -/
theorem f311_spec (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 0) (inst : Nat) (mi : ModuleInst) (n : Nat)
    (hn : mi.memAddrs[0]? = some n) (a237 a582 a570 a568 a576 a575 : Nat)
    (h237 : mi.funcAddrs[237]? = some a237) (h582 : mi.funcAddrs[582]? = some a582)
    (h570 : mi.funcAddrs[570]? = some a570) (h568 : mi.funcAddrs[568]? = some a568)
    (h576 : mi.funcAddrs[576]? = some a576) (h575 : mi.funcAddrs[575]? = some a575)
    (ty237 ty582 ty570 ty568 ty576 ty575 : FuncType)
    (hp237 : ty237.params.length = 3) (hr237 : ty237.results.length = 0)
    (hp582 : ty582.params.length = 4) (hr582 : ty582.results.length = 0)
    (hp570 : ty570.params.length = 1) (hr570 : ty570.results.length = 1)
    (hp568 : ty568.params.length = 2) (hr568 : ty568.results.length = 1)
    (hp576 : ty576.params.length = 1) (hr576 : ty576.results.length = 1)
    (hp575 : ty575.params.length = 1) (hr575 : ty575.results.length = 0)
    (hd : d + 4 < lim.maxCallDepth) (Cg maxP : Nat) (live : List (Nat × Nat)) (F : Nat)
    (ptr size align : UInt32) :
    a237 ↪[wf] FuncInst.wasm ty237 inst f237 ∗ a582 ↪[wf] FuncInst.wasm ty582 inst f582 ∗
      a570 ↪[wf] FuncInst.wasm ty570 inst f570 ∗ a568 ↪[wf] FuncInst.wasm ty568 inst f568 ∗
      a576 ↪[wf] FuncInst.wasm ty576 inst f576 ∗ a575 ↪[wf] FuncInst.wasm ty575 inst f575 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f311 Cg
        (fun args => iprop(⌜args = [.i32 ptr, .i32 size, .i32 align]⌝ ∗
          ⌜(ptr.toNat, size.toNat) ∈ live⌝ ∗ heapInvFix n maxP live F ∗ block n ptr.toNat size.toNat))
        (fun _ => 256 * cfg.regularOpCost)
        (fun _ rs => iprop(⌜rs = []⌝ ∗ heapInvFix n maxP (live.erase (ptr.toNat, size.toNat)) (F + 1))) := by
  iintro ⟨#H237, #H582, #H570, #H568, #H576, #H575, #Hi⟩
  ihave #S582 := f582_spec (GF := GF) cfg lim (d + 2) ty582 hr582 inst mi n hn a570 a568 a576 a575
    h570 h568 h576 h575 ty570 ty568 ty576 ty575 hp570 hr570 hp568 hr568 hp576 hr576 hp575 hr575
    (by omega) Cg maxP live F ptr size align $$ [H570 H568 H576 H575 Hi]
  · iframe H570 H568 H576 H575 Hi
  ihave #S237 := AllocWrap.f237_spec (GF := GF) cfg lim (d + 1) ty237 hr237 inst mi a582 h582 ty582
    hp582 hr582 (by omega) Cg _ _ _ ptr size align $$ [H582 Hi S582]
  · iframe H582 Hi; iexact S582
  iapply MFunSpec_conv
    (K := fun _ => 15 * cfg.regularOpCost + (17 * cfg.regularOpCost + 224 * cfg.regularOpCost))
    (fun _ => .rfl) (fun _ => by omega)
  iapply AllocWrap.f311_of_f237 (GF := GF) cfg lim d type htype inst mi a237 h237 ty237 hp237 hr237
    (by omega) Cg _ _ _ ptr size align
  iframe H237 Hi
  iapply MFunSpec_conv (fun _ => ?_) (fun _ => rfl) $$ S237
  iintro ⟨%h1, H⟩
  iframe H
  ipureintro; exact ⟨h1, rfl⟩

end Wrap

end WNear.Binary.AllocDealloc
