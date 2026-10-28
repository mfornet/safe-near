import Bridge.Functions.AllocAlloc
import Bridge.Functions.AllocDealloc

/-!
# `__rust_alloc` on a heap with an empty free list, against `AllocInv.heapInv` (M4)

`AllocAlloc.f310_fresh` proves `__rust_alloc` (310 → 236 → 581) on `ALLOC = 0` with raw
resources (`pre581` / `res581`). This file packs it into the heap invariant.

## The model: appending the fresh chunk `[len, E)`, `E = len + P · 65536`

* `geo_append`: the geometry of the old cells (all below `len`) and of the chunk's cells
  gives that of both; `geo_one` (the chunk is one cell) and `geo_two` (free remainder `len`,
  allocated tail `m`);
* `wf_freshU`: 580 unlinked the fresh cell: it stays a free, leaked cell (`F` unchanged);
* `wf_freshW`: taken whole: one allocated cell, `(len + 8, s)` live;
* `wf_freshS`: split: the free remainder `[len, m)` (listed, `next_free = 0`, the free list
  `[len]`, `F = 1`) and the allocated cell `[m, E)`, `(m + 8, s)` live.

## Resources

* `heapInv_open0`: `heapInv n maxP len live 0 ⊢ ALLOC ↦ 0 ∗ len ↦[wmlength] ∗ frameH …`
  (`F = 0` forces the free list empty, so the head word is 0): 581's `pre581` plus a frame;
* `pack_fail` (memory.grow failed), `pack_U`, `pack_W`, `pack_S` (580's three outcomes on the
  fresh cell), dispatched by `pack_grown` on `post1`;
* `MFunSpec_frame`: a specification's precondition strengthened by a frame its postcondition
  gives back.

## The spec

`f310_spec_fresh`: for `1 ≤ size < 2^28`, `align = 2^k` (`k < 20`), `0 < len` page-aligned and
`len + P · 65536 + 65536 ≤ 2^32` (`P = cellPages (wordsOf size) align`),

```
{ ⌜args = [size, align]⌝ ∗ g_sp ↦ sp ∗ 581's 3 stack words ∗ vt (min_cell_size's slot)
  ∗ heapInv n maxP len live 0 }
__rust_alloc(size, align)                      cost 15 + 15 + 630 + grow(P)
{ ∃ p, rs = [p] ∗ g_sp ↦ sp ∗ 3 stack words (any) ∗ vt ∗ allocOut n maxP len E live size al p }

allocOut … p =  (p ≠ 0 ∗ p % al = 0 ∗ heapInv n maxP E ((p, size) :: live) 1 ∗ block n p size)
              ∨ (p = 0 ∗ ∃ len', (len' = len ∨ len' = E) ∗ heapInv n maxP len' live 0)
```

`F' = 1` covers both the split (remainder listed) and the whole case (`F = 0`, weakened by
`heapInv_mono`). `p = 0` happens when memory.grow fails (`len' = len`) or when 580 does not
use the fresh cell (`len' = E`, AllocFirstFit's finding 5).

A block is aligned: `p % align = 0` (from `post1`: `aligned` for the whole cell, `aN` for a
split).

## Elsewhere

Alloc on a one-cell free list (`F = 1`), with the memory's limit seen by `memory.grow`, is
`AllocSeq.f310_spec_seq` (it also covers `F = 0`, at a higher cost bound: 910 against 630).
-/

namespace WNear.Binary.AllocFresh

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic
open WNear.Binary WNear.Binary.AllocInv
open WNear.Binary.AllocDealloc (cellAt_iff nodup_of_sorted)

/-! ## The model: appending a fresh chunk -/

/-- A cell of a fresh chunk (`next_free = 0`). -/
def newCell (a e pv : Nat) (lst al : Bool) : CellM :=
  { addr := a, next := e, prev := pv, last := lst, allocated := al, nextFree := 0 }

/-- The geometry of `H` and of a chunk `N` above it give the geometry of both. -/
theorem geo_append {H N H' : HeapModel} (hg : Geo H) (hn : Geo N) (h1 : H.len ≤ N.mem0)
    (h2 : H.mem0 ≤ N.mem0) (h3 : N.mem0 ≤ N.len) (h0 : H'.mem0 = H.mem0) (hl : H'.len = N.len)
    (hc : H'.cells = H.cells ++ N.cells) : Geo H' := by
  have hmem : ∀ z, z ∈ H'.cells ↔ z ∈ H.cells ∨ z ∈ N.cells := by
    intro z; rw [hc, List.mem_append]
  constructor
  · intro z hz
    rcases (hmem z).mp hz with hz | hz
    · have := hg.bounds z hz; rw [h0, hl]; omega
    · have := hn.bounds z hz; rw [h0, hl]; omega
  · intro z hz
    rcases (hmem z).mp hz with hz | hz
    · exact hg.next_al z hz
    · exact hn.next_al z hz
  · rw [hc, List.map_append, List.pairwise_append]
    refine ⟨hg.sorted, hn.sorted, ?_⟩
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hb
    have := hg.bounds x hx; have := hn.bounds y hy; omega
  · intro z hz hzl
    rcases (hmem z).mp hz with hz | hz
    · obtain ⟨d, hd, e⟩ := hg.next_nb z hz hzl; exact ⟨d, (hmem d).mpr (Or.inl hd), e⟩
    · obtain ⟨d, hd, e⟩ := hn.next_nb z hz hzl; exact ⟨d, (hmem d).mpr (Or.inr hd), e⟩
  · intro z hz hzp
    rcases (hmem z).mp hz with hz | hz
    · obtain ⟨d, hd, e⟩ := hg.prev_nb z hz hzp; exact ⟨d, (hmem d).mpr (Or.inl hd), e⟩
    · obtain ⟨d, hd, e⟩ := hn.prev_nb z hz hzp; exact ⟨d, (hmem d).mpr (Or.inr hd), e⟩
  · intro z hz hzp
    rcases (hmem z).mp hz with hz | hz
    · exact hg.first z hz hzp
    · exact hn.first z hz hzp
  · intro x hx y hy hxy
    rcases (hmem x).mp hx with hx | hx <;> rcases (hmem y).mp hy with hy | hy
    · exact hg.disj x hx y hy hxy
    · have := hg.bounds x hx; have := hn.bounds y hy; omega
    · have := hg.bounds y hy; have := hn.bounds x hx; omega
    · exact hn.disj x hx y hy hxy

/-- A chunk of one cell (free or allocated). -/
theorem geo_one (a e : Nat) (al : Bool) (ha : a % 65536 = 0) (hae : a + 12 ≤ e) (he : e % 4 = 0) :
    Geo { mem0 := a, len := e, cells := [newCell a e 0 true al], freeList := [] } := by
  constructor
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; simp only [newCell]; omega
  · intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact he
  · simp
  · intro c hc hl; simp only [List.mem_singleton] at hc; subst hc; simp [newCell] at hl
  · intro c hc hp; simp only [List.mem_singleton] at hc; subst hc; simp [newCell] at hp
  · intro c hc _; simp only [List.mem_singleton] at hc; subst hc; exact ha
  · intro x hx y hy hxy
    simp only [List.mem_singleton] at hx hy; subst hx hy; omega

/-- A chunk split in two: the free remainder `a` and the allocated tail `m`. -/
theorem geo_two (a m e : Nat) (ha : a % 65536 = 0) (ha0 : 0 < a) (ham : a + 12 ≤ m) (hme : m + 12 ≤ e)
    (hm : m % 4 = 0) (he : e % 4 = 0) :
    Geo { mem0 := a, len := e, cells := [newCell a m 0 false false, newCell m e a true true], freeList := [] } := by
  have hmem : ∀ c, c ∈ [newCell a m 0 false false, newCell m e a true true] ↔
      c = newCell a m 0 false false ∨ c = newCell m e a true true := by
    intro c; simp
  constructor
  · intro c hc; rcases (hmem c).mp hc with rfl | rfl <;> simp only [newCell] <;> omega
  · intro c hc; rcases (hmem c).mp hc with rfl | rfl <;> simp only [newCell] <;> omega
  · simp [newCell]; omega
  · intro c hc hl; rcases (hmem c).mp hc with rfl | rfl
    · exact ⟨_, (hmem _).mpr (Or.inr rfl), rfl, rfl⟩
    · simp [newCell] at hl
  · intro c hc hp; rcases (hmem c).mp hc with rfl | rfl
    · simp [newCell] at hp
    · exact ⟨_, (hmem _).mpr (Or.inl rfl), rfl, rfl, rfl⟩
  · intro c hc hp; rcases (hmem c).mp hc with rfl | rfl
    · exact ha
    · simp [newCell] at hp; omega
  · intro x hx y hy hxy
    rcases (hmem x).mp hx with rfl | rfl <;> rcases (hmem y).mp hy with rfl | rfl <;>
      simp only [newCell] at hxy ⊢ <;> omega

theorem lists_nil {H : HeapModel} {F : Nat} (h : H.freeList = []) : Lists H F := by
  refine ⟨by simp [h], by simp [h], by simp [h], ?_, ?_⟩
  · intro i hi; simp [h] at hi
  · intro i hi; simp [h] at hi

theorem lists_one {H : HeapModel} {a : Nat} {c : CellM} (h : H.freeList = [a])
    (hc : H.cellAt a = some c) (hcf : c.allocated = false) (hnf : c.nextFree = 0) : Lists H 1 := by
  have h0 : ∀ i (hi : i < H.freeList.length), i = 0 ∧ H.freeList[i] = a := by
    intro i hi
    have : i = 0 := by simp [h] at hi; omega
    subst this
    exact ⟨rfl, by simp [h]⟩
  refine ⟨by simp [h], by simp [h], ?_, ?_, ?_⟩
  · intro b hb; rw [h] at hb; simp at hb; subst hb; exact ⟨c, hc, hcf⟩
  · intro i hi
    obtain ⟨rfl, e⟩ := h0 i hi
    rw [e]; refine ⟨c, hc, ?_⟩
    rw [h, hnf]; rfl
  · intro i hi c' hc' hodd
    obtain ⟨rfl, e⟩ := h0 i hi
    rw [e, hc] at hc'; cases hc'
    rw [hnf] at hodd; cases hodd

theorem lives_mono {H H' : HeapModel} {live : List (Nat × Nat)} (hv : Lives H live)
    (hold : ∀ c ∈ H.cells, c ∈ H'.cells) (hnew : ∀ z ∈ H'.cells, z.allocated = true → z ∈ H.cells) :
    Lives H' live := by
  refine ⟨?_, ?_, hv.live_nodup⟩
  · intro p s hm
    obtain ⟨hpos, c, hc, hca, hp, hle⟩ := hv.live_cell _ _ hm
    exact ⟨hpos, c, hold c hc, hca, hp, hle⟩
  · intro z hz hza; exact hv.cell_live z (hnew z hz hza) hza

theorem lives_append {H H' : HeapModel} {live : List (Nat × Nat)} (hv : Lives H live) {a s : Nat}
    {cA : CellM} (hb : ∀ c ∈ H.cells, c.addr < a) (hcA : cA ∈ H'.cells) (hA : cA.allocated = true)
    (hAa : cA.addr = a) (hs0 : 0 < s) (hs : s ≤ cA.size) (hold : ∀ c ∈ H.cells, c ∈ H'.cells)
    (hnew : ∀ z ∈ H'.cells, z.allocated = true → z ∈ H.cells ∨ z = cA) :
    Lives H' ((a + 8, s) :: live) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p s' hm
    rcases List.mem_cons.mp hm with e | hm
    · simp only [Prod.mk.injEq] at e; obtain ⟨rfl, rfl⟩ := e
      exact ⟨hs0, cA, hcA, hA, by rw [hAa], hs⟩
    · obtain ⟨hpos, c, hc, hca, hp, hle⟩ := hv.live_cell _ _ hm
      exact ⟨hpos, c, hold c hc, hca, hp, hle⟩
  · intro z hz hza
    rcases hnew z hz hza with hz | rfl
    · obtain ⟨s', h⟩ := hv.cell_live z hz hza; exact ⟨s', List.mem_cons_of_mem _ h⟩
    · exact ⟨s, by rw [hAa]; exact List.mem_cons_self⟩
  · rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, hv.live_nodup⟩
    intro hm
    obtain ⟨⟨p, s'⟩, hps, hp⟩ := List.mem_map.mp hm
    simp only at hp; subst hp
    obtain ⟨-, c, hc, -, hpc, -⟩ := hv.live_cell _ _ hps
    have := hb c hc; omega

section Fresh

variable {H : HeapModel} {live : List (Nat × Nat)} {F len E : Nat} (hw : H.wf live F) (hl : H.len = len)
  (ha0 : 0 < len) (hE2 : E % 65536 = 0) (hE3 : E < 2 ^ 32)
include hw hl ha0 hE2 hE3

theorem below (c : CellM) (hc : c ∈ H.cells) : c.addr < len := by
  have := hw.geo.bounds c hc; omega

/-- The fresh chunk stays one free cell, leaked (580 unlinked it). -/
theorem wf_freshU (hfl : H.freeList = []) (hE1 : len + 12 ≤ E) :
    HeapModel.wf { H with len := E, cells := H.cells ++ [newCell len E 0 true false] } live F := by
  have hlal : len % 65536 = 0 := hl ▸ hw.len_al
  refine ⟨hw.mem0_al, hw.mem0_pos, hE2, ?_, hE3, ?_, lists_nil hfl, ?_, ?_⟩
  · have := hw.mem0_le; show H.mem0 ≤ E; omega
  · exact geo_append hw.geo (geo_one len E false hlal hE1 (by omega)) (by simp; omega)
      (by have := hw.mem0_le; simp; omega) (by simp; omega) rfl rfl rfl
  · apply lives_mono hw.lives (fun c hc => List.mem_append_left _ hc)
    intro z hz hza
    rcases List.mem_append.mp hz with hz | hz
    · exact hz
    · simp only [List.mem_singleton] at hz; subst hz; simp [newCell] at hza
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hw.nf_lo z hz
    · simp only [List.mem_singleton] at hz; subst hz; simp [newCell]

/-- The fresh chunk taken whole by the allocation `(len + 8, s)`. -/
theorem wf_freshW (hfl : H.freeList = []) {s : Nat} (hs0 : 0 < s) (hs : len + 8 + s ≤ E) (hE1 : len + 12 ≤ E) :
    HeapModel.wf { H with len := E, cells := H.cells ++ [newCell len E 0 true true] }
      ((len + 8, s) :: live) F := by
  have hlal : len % 65536 = 0 := hl ▸ hw.len_al
  refine ⟨hw.mem0_al, hw.mem0_pos, hE2, ?_, hE3, ?_, lists_nil hfl, ?_, ?_⟩
  · have := hw.mem0_le; show H.mem0 ≤ E; omega
  · exact geo_append hw.geo (geo_one len E true hlal hE1 (by omega)) (by simp; omega)
      (by have := hw.mem0_le; simp; omega) (by simp; omega) rfl rfl rfl
  · apply lives_append hw.lives (below hw hl ha0 hE2 hE3) (List.mem_append_right _ (List.mem_singleton_self _))
      rfl rfl hs0 (by simp only [newCell, CellM.size]; omega) (fun c hc => List.mem_append_left _ hc)
    intro z hz _
    rcases List.mem_append.mp hz with hz | hz
    · exact Or.inl hz
    · simp only [List.mem_singleton] at hz; exact Or.inr hz
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hw.nf_lo z hz
    · simp only [List.mem_singleton] at hz; subst hz; simp [newCell]

/-- The fresh chunk split: the free remainder `len` (listed) and the allocated tail `m`
lent as `(m + 8, s)`. -/
theorem wf_freshS (hfl : H.freeList = []) {m s : Nat} (hm1 : len + 12 ≤ m) (hm2 : m % 4 = 0)
    (hs0 : 0 < s) (hs : m + 8 + s ≤ E) (hE1 : m + 12 ≤ E) :
    HeapModel.wf { H with len := E, cells := H.cells ++ [newCell len m 0 false false, newCell m E len true true], freeList := [len] } ((m + 8, s) :: live) 1 := by
  have hlal : len % 65536 = 0 := hl ▸ hw.len_al
  have hg : Geo { H with len := E, cells := H.cells ++ [newCell len m 0 false false, newCell m E len true true], freeList := [len] } :=
    geo_append hw.geo (geo_two len m E hlal ha0 hm1 hE1 hm2 (by omega)) (by simp; omega)
      (by have := hw.mem0_le; simp; omega) (by simp; omega) rfl rfl rfl
  refine ⟨hw.mem0_al, hw.mem0_pos, hE2, ?_, hE3, hg, ?_, ?_, ?_⟩
  · have := hw.mem0_le; show H.mem0 ≤ E; omega
  · apply lists_one (c := newCell len m 0 false false) rfl _ rfl rfl
    exact (cellAt_iff (nodup_of_sorted hg.sorted)).mpr ⟨by simp, rfl⟩
  · refine lives_append (H' := { H with len := E, cells := H.cells ++ [newCell len m 0 false false, newCell m E len true true], freeList := [len] }) (a := m) (cA := newCell m E len true true) hw.lives
      (fun c hc => by have := below hw hl ha0 hE2 hE3 c hc; omega)
      (List.mem_append_right _ (by simp)) rfl rfl hs0 (by simp only [newCell, CellM.size]; omega)
      (fun c hc => List.mem_append_left _ hc) ?_
    intro z hz hza
    rcases List.mem_append.mp hz with hz | hz
    · exact Or.inl hz
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, _root_.or_false] at hz
      rcases hz with rfl | rfl
      · simp [newCell] at hza
      · exact Or.inr rfl
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hw.nf_lo z hz
    · simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, _root_.or_false] at hz
      rcases hz with rfl | rfl <;> simp [newCell]

end Fresh

/-! ## Header words of the fresh cells -/

open WNear.Binary.AllocFirstFit (post1 vt w0 aN fits canSplit aligned szN aN_mod4 nextW)
open WNear.Binary.AllocDealloc (or2_ofNat cellRes_free_intro cellRes_alloc)
open WNear.Binary.AllocNewCell (memBytes_addr memBytes_eq)
open WNear.Binary.U128From (memBytes_split memBytes_join)

theorem w0_last (E : Nat) (hE4 : E % 4 = 0) (hE : E + 3 < 2 ^ 32) :
    w0 (UInt32.ofNat E) true = UInt32.ofNat (E + 2) := by
  simp only [w0, ↓reduceIte]; exact or2_ofNat E hE4 hE

theorem or1_two (x : Nat) (hx : x % 4 = 0) (h : x + 3 < 2 ^ 32) :
    UInt32.ofNat (x + 2) ||| 1 = UInt32.ofNat (x + 3) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_or, show (1 : UInt32).toNat = 1 from rfl, AllocRemove.nat_or_low _ _ (by decide)]
  simp only [UInt32.toNat_ofNat', Nat.mod_eq_of_lt (show x + 2 < 2 ^ 32 by omega),
    Nat.mod_eq_of_lt (show x + 3 < 2 ^ 32 by omega), show (x + 2) % 4 = 2 by omega, Nat.reduceOr]; omega

theorem w0_last_alloc (E : Nat) (hE4 : E % 4 = 0) (hE : E + 3 < 2 ^ 32) :
    w0 (UInt32.ofNat E) true ||| 1 = UInt32.ofNat (E + 3) := by
  rw [w0_last E hE4 hE, or1_two E hE4 hE]

theorem sub8_ofNat (r : UInt32) (h : 8 ≤ r.toNat) : r - 8 = UInt32.ofNat (r.toNat - 8) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub_of_le _ _ (by rw [UInt32.le_iff_toNat_le]; exact h)]
  have := r.toNat_lt; simp only [UInt32.toNat_ofNat']; simp; omega

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-! ## Resources -/

theorem cellRes_cons (n : Nat) {live : List (Nat × Nat)} (q : Nat × Nat) (x : CellM) :
    cellRes (GF := GF) n live x ⊢ cellRes n (q :: live) x := by
  unfold cellRes
  iintro ⟨H0, H1, H2⟩
  iframe H0 H1
  split
  · icases H2 with ⟨%s', %bs, %⟨h1, h2⟩, H⟩
    iexists s', bs
    iframe H
    ipureintro
    exact ⟨List.mem_cons_of_mem _ h1, h2⟩
  · iexact H2

theorem bigSep_cons (n : Nat) {live : List (Nat × Nat)} (q : Nat × Nat) (L : List CellM) :
    ([∗list] x ∈ L, cellRes (GF := GF) n live x) ⊢ [∗list] x ∈ L, cellRes n (q :: live) x :=
  BigSepL.bigSepL_mono (fun _ => cellRes_cons n q _)

/-- A fresh free cell's resources. -/
theorem cellRes_newFree (n : Nat) (live : List (Nat × Nat)) (a e pv : Nat) (lst : Bool) (v0 v1 : UInt32)
    (h0 : v0 = UInt32.ofNat (newCell a e pv lst false).word0) (h1 : v1 = UInt32.ofNat pv)
    (bs : List UInt8) (hbs : bs.length + 4 = e - a - 8) :
    n ↦[i32][ a ] v0 ∗ n ↦[i32][ a + 4 ] v1 ∗ n ↦[i32][ a + 8 ] 0 ∗ n ↦[wms][ a + 12 ] bs
      ⊢ cellRes (GF := GF) n live (newCell a e pv lst false) :=
  cellRes_free_intro (newCell a e pv lst false) rfl rfl h0.symm h1.symm rfl bs hbs

/-- A fresh allocated cell's resources: its header and the slack past the lent `s` bytes. -/
theorem cellRes_newAlloc (n : Nat) (live : List (Nat × Nat)) (a e pv : Nat) (lst : Bool) (v0 v1 : UInt32)
    (h0 : v0 = UInt32.ofNat (newCell a e pv lst true).word0) (h1 : v1 = UInt32.ofNat pv)
    (s : Nat) (hs : (a + 8, s) ∈ live) (bs : List UInt8) (hbs : bs.length = e - a - 8 - s) :
    n ↦[i32][ a ] v0 ∗ n ↦[i32][ a + 4 ] v1 ∗ n ↦[wms][ a + 8 + s ] bs
      ⊢ cellRes (GF := GF) n live (newCell a e pv lst true) := by
  iintro ⟨H0, H1, H2⟩
  iapply (cellRes_alloc (x := newCell a e pv lst true) n rfl).2
  subst h0 h1
  ihave H0 := memBytes_addr (a := a) (b := (newCell a e pv lst true).addr) rfl $$ H0
  ihave H1 := AllocDealloc.memBytes_at (a := a + 4) (b := (newCell a e pv lst true).addr + 4)
    (bs := bytes32 (UInt32.ofNat pv)) (bs' := bytes32 (UInt32.ofNat (newCell a e pv lst true).prev)) rfl rfl $$ H1
  ihave H2 := memBytes_addr (a := a + 8 + s) (b := (newCell a e pv lst true).addr + 8 + s) rfl $$ H2
  iframe H0 H1
  iexists s, bs
  iframe H2
  ipureintro; exact ⟨hs, hbs⟩

/-- Closing the invariant on a model. -/
theorem heapInv_intro {n maxP len F : Nat} {live : List (Nat × Nat)} (H : HeapModel) (hw : H.wf live F)
    (hl : H.len = len) (v : UInt32) (hv : v = UInt32.ofNat H.head) :
    n ↦[i32][ 1074896 ] v ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some maxP ∗
      ([∗list] c ∈ H.cells, cellRes n live c) ⊢ heapInv (GF := GF) n maxP len live F := by
  iintro ⟨Hh, Hl, Hm, Hc⟩
  iunfold heapInv
  iexists H
  isplitr
  · ipureintro; exact ⟨hw, hl⟩
  subst hv hl
  rw [show headAddr = 1074896 from rfl]
  iframe Hh Hl Hm Hc

/-- What `heapInv` keeps while 581 runs on an empty free list: the model, the limit, the cells. -/
def frameH (n maxP len : Nat) (live : List (Nat × Nat)) : IProp GF :=
  iprop(∃ H : HeapModel, ⌜H.wf live 0 ∧ H.len = len ∧ H.freeList = []⌝ ∗ n ↪[wmlimit] some maxP ∗
    [∗list] c ∈ H.cells, cellRes n live c)

/-- `heapInv` with `F = 0` gives 581's `ALLOC = 0` and the memory length. -/
theorem heapInv_open0 (n maxP len : Nat) (live : List (Nat × Nat)) :
    heapInv (GF := GF) n maxP len live 0 ⊢
      n ↦[i32][ 1074896 ] 0 ∗ n ↦[wmlength] len ∗ frameH n maxP len live := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%H, %⟨hw, hl⟩, Hh, Hl, Hm, Hc⟩
  have hfl : H.freeList = [] := List.eq_nil_of_length_eq_zero (by have := hw.lists.fl_len; omega)
  have e : bytes32 (UInt32.ofNat H.head) = bytes32 0 := by simp [HeapModel.head, hfl]
  ihave Hh := memBytes_eq e $$ Hh
  ihave Hh := memBytes_addr (a := headAddr) (b := 1074896) rfl $$ Hh
  subst hl
  iframe Hh Hl
  iunfold frameH
  iexists H
  iframe Hm Hc
  ipureintro; exact ⟨hw, rfl, hfl⟩

/-- `memory.grow` failed: the heap is unchanged. -/
theorem pack_fail (n maxP len : Nat) (live : List (Nat × Nat)) :
    frameH (GF := GF) n maxP len live ∗ n ↦[i32][ 1074896 ] 0 ∗ n ↦[wmlength] len ⊢
      heapInv n maxP len live 0 := by
  iintro ⟨Hf, Hh, Hl⟩
  iunfold frameH at Hf
  icases Hf with ⟨%H, %⟨hw, hl, hfl⟩, Hm, Hc⟩
  iapply heapInv_intro H hw hl 0 (by simp [HeapModel.head, hfl])
  iframe Hh Hl Hm Hc

/-- The outcome of an allocation of `size` bytes from a heap of length `len` and live
allocations `live`, when the memory may have grown to `E`: a block `p ≠ 0` lent (the heap
grown, its free list at most the split remainder), or `0` with the heap valid (unchanged,
or grown with the fresh chunk leaked). -/
def allocOut (n maxP len E : Nat) (live : List (Nat × Nat)) (size : Nat) (al p : UInt32) : IProp GF :=
  iprop((⌜p ≠ 0 ∧ p.toNat % al.toNat = 0⌝ ∗ heapInv n maxP E ((p.toNat, size) :: live) 1 ∗ block n p.toNat size) ∨
    (⌜p = 0⌝ ∗ ∃ len', ⌜len' = len ∨ len' = E⌝ ∗ heapInv n maxP len' live 0))

section Pack

variable {n maxP len E : Nat} {live : List (Nat × Nat)} (hl0 : 0 < len) (hE : len + 65536 ≤ E)
  (hE4 : E % 65536 = 0) (hE32 : E < 2 ^ 32)
include hl0 hE hE4 hE32

/-- 580 unlinked the fresh cell: it stays a leaked free cell. -/
theorem pack_U (rest : List UInt8) (hrest : rest.length + 12 + len = E) :
    frameH (GF := GF) n maxP len live ∗ n ↦[wmlength] E ∗ n ↦[i32][ len + 4 ] 0 ∗
      n ↦[i32][ 1074896 ] 0 ∗ n ↦[i32][ len ] w0 (UInt32.ofNat E) true ∗ n ↦[i32][ len + 8 ] 0 ∗
      n ↦[wms][ len + 12 ] rest
      ⊢ heapInv n maxP E live 0 := by
  iintro ⟨Hf, Hl, H4, Hh, H0, H8, Hd⟩
  iunfold frameH at Hf
  icases Hf with ⟨%H, %⟨hw, hl, hfl⟩, Hm, Hc⟩
  iapply heapInv_intro _ (wf_freshU hw hl hl0 hE4 hE32 hfl (by omega)) rfl 0
    (by simp [HeapModel.head, hfl])
  iframe Hh Hl Hm
  iapply BigSepL.bigSepL_snoc.2
  iframe Hc
  iapply cellRes_newFree n live len E 0 true (w0 (UInt32.ofNat E) true) 0 (by rw [w0_last E (by omega) (by omega)]; rfl) rfl rest
    (by omega)
  iframe H0 H4 H8 Hd

/-- 580 took the fresh cell whole: it is allocated, lent as `(len + 8, size)`. -/
theorem pack_W (rest : List UInt8) (hrest : rest.length + 12 + len = E) {size : Nat} (hs0 : 0 < size)
    (hsz : len + 8 + size ≤ E) :
    frameH (GF := GF) n maxP len live ∗ n ↦[wmlength] E ∗ n ↦[i32][ len + 4 ] 0 ∗
      n ↦[i32][ 1074896 ] 0 ∗ n ↦[i32][ len ] (w0 (UInt32.ofNat E) true ||| 1) ∗ n ↦[i32][ len + 8 ] 0 ∗
      n ↦[wms][ len + 12 ] rest
      ⊢ heapInv n maxP E ((len + 8, size) :: live) 1 ∗ block n (len + 8) size := by
  iintro ⟨Hf, Hl, H4, Hh, H0, H8, Hd⟩
  iunfold frameH at Hf
  icases Hf with ⟨%H, %⟨hw, hl, hfl⟩, Hm, Hc⟩
  ihave Hd := memBytes_addr (a := len + 12) (b := len + 8 + 4) (by omega) $$ Hd
  ihave Hd := memBytes_join n (len + 8) 4 (bytes32 0) rest (by simp) $$ [H8 Hd]
  · iframe H8 Hd
  icases memBytes_split n (len + 8) size (bytes32 0 ++ rest) (by simp; omega) $$ Hd with ⟨Hb, Hs⟩
  isplitr [Hb]
  · iapply heapInv_mono n maxP E _ 0 1 (by omega)
    iapply heapInv_intro _ (wf_freshW hw hl hl0 hE4 hE32 hfl hs0 hsz (by omega)) rfl 0
      (by simp [HeapModel.head, hfl])
    iframe Hh Hl Hm
    iapply BigSepL.bigSepL_snoc.2
    isplitl [Hc]
    · iapply bigSep_cons $$ Hc
    iapply cellRes_newAlloc n _ len E 0 true (w0 (UInt32.ofNat E) true ||| 1) 0
      (by rw [w0_last_alloc E (by omega) (by omega)]; rfl) rfl
      size List.mem_cons_self ((bytes32 0 ++ rest).drop size) (by simp; omega)
    iframe H0 H4 Hs
  · iunfold block
    iexists _
    iframe Hb
    ipureintro; simp; omega

/-- 580 split the fresh cell: the remainder `len` (listed) and the allocated tail `m`, lent
as `(m + 8, size)`. -/
theorem pack_S {m size : Nat} (hm1 : len + 12 ≤ m) (hm2 : m % 4 = 0) (hs0 : 0 < size)
    (hsz : m + 8 + size ≤ E) (hE1 : m + 12 ≤ E) (b0 : List UInt8) (hb0 : b0.length + 12 + len = m)
    (bs : List UInt8) (hbs : bs.length = E - m - 8) :
    frameH (GF := GF) n maxP len live ∗ n ↦[wmlength] E ∗ n ↦[i32][ len + 4 ] 0 ∗
      n ↦[i32][ 1074896 ] UInt32.ofNat len ∗ n ↦[i32][ len ] UInt32.ofNat m ∗ n ↦[i32][ len + 8 ] 0 ∗
      n ↦[wms][ len + 12 ] b0 ∗ n ↦[i32][ m ] (w0 (UInt32.ofNat E) true ||| 1) ∗
      n ↦[i32][ m + 4 ] UInt32.ofNat len ∗ n ↦[wms][ m + 8 ] bs
      ⊢ heapInv n maxP E ((m + 8, size) :: live) 1 ∗ block n (m + 8) size := by
  iintro ⟨Hf, Hl, H4, Hh, H0, H8, Hd, HN0, HN1, HB⟩
  iunfold frameH at Hf
  icases Hf with ⟨%H, %⟨hw, hl, hfl⟩, Hm, Hc⟩
  icases memBytes_split n (m + 8) size bs (by omega) $$ HB with ⟨Hb, Hs⟩
  isplitr [Hb]
  · iapply heapInv_intro _ (wf_freshS hw hl hl0 hE4 hE32 hfl hm1 hm2 hs0 hsz hE1) rfl (UInt32.ofNat len) rfl
    iframe Hl Hm
    isplitl [Hh]
    · iexact Hh
    rw [show H.cells ++ [newCell len m 0 false false, newCell m E len true true] =
      (H.cells ++ [newCell len m 0 false false]) ++ [newCell m E len true true] by simp]
    iapply BigSepL.bigSepL_snoc.2
    isplitl [Hc H0 H4 H8 Hd]
    · iapply BigSepL.bigSepL_snoc.2
      isplitl [Hc]
      · iapply bigSep_cons $$ Hc
      iapply cellRes_newFree n _ len m 0 false (UInt32.ofNat m) 0 (by simp [newCell, CellM.word0]) rfl b0
        (by omega)
      iframe H0 H4 H8 Hd
    iapply cellRes_newAlloc n _ m E len true (w0 (UInt32.ofNat E) true ||| 1) (UInt32.ofNat len)
      (by rw [w0_last_alloc E (by omega) (by omega)]; rfl) rfl
      size List.mem_cons_self (bs.drop size) (by simp; omega)
    iframe HN0 HN1 Hs
  · iunfold block
    iexists _
    iframe Hb
    ipureintro; simp; omega

/-- 581's grown branch, packed: whatever 580 did on the fresh cell, the heap is valid with
the memory length `E`, and a nonzero result is a lent block. -/
theorem pack_grown (w al : UInt32) (k : Nat) (hal : al.toNat = 2 ^ k) {size : Nat} (hs0 : 0 < size)
    (hsw : size ≤ 4 * w.toNat) (idx : UInt32) (ta a578 : Nat) (p : UInt32) :
    frameH (GF := GF) n maxP len live ∗ n ↦[wmlength] E ∗ n ↦[i32][ len + 4 ] 0 ∗
      (∃ rest : List UInt8, ⌜rest.length = E - len - 12⌝ ∗
        post1 n w al 1074896 (UInt32.ofNat len) (UInt32.ofNat E) 0 true rest 1057464 idx ta a578 [] [.i32 p])
      ⊢ vt n 1057464 idx ta a578 ∗ allocOut n maxP len E live size al p := by
  iintro ⟨Hf, Hl, H4, %rest, %hrl, Hp⟩
  iunfold post1 at Hp
  icases Hp with ⟨%r, %hrs, Hvt, Hc⟩
  obtain rfl : p = r := by simpa using hrs
  iframe Hvt
  have hcN : (UInt32.ofNat len).toNat = len := by simp only [UInt32.toNat_ofNat']; omega
  have hEN : (UInt32.ofNat E).toNat = E := by simp only [UInt32.toNat_ofNat']; omega
  iunfold allocOut
  icases Hc with (⟨%hU, Hs, H0, H8, Hd, -⟩ | ⟨%hW, Hs, H0, H8, Hd, -⟩ | ⟨%hS, Hs, H0, H8, Hd, HN0, HN1, HB, -⟩)
  · -- unlinked
    ihave Hs := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hs
    ihave H0 := memBytes_addr (b := len) hcN $$ H0
    ihave H8 := memBytes_addr (b := len + 8) (by omega) $$ H8
    ihave Hd := memBytes_addr (b := len + 12) (by omega) $$ Hd
    iright
    isplitr
    · ipureintro; exact hU.1
    iexists E
    isplitr
    · ipureintro; exact Or.inr rfl
    iapply pack_U hl0 hE hE4 hE32 rest (by omega)
    iframe Hf Hl H4 Hs H0 H8 Hd
  · -- taken whole
    obtain ⟨hp, hfit, -, hali⟩ := hW
    have hpn : p.toNat = len + 8 := by
      rw [hp, UInt32.toNat_add, hcN, show (8 : UInt32).toNat = 8 from rfl]; omega
    have hfit' : 4 * w.toNat ≤ E - len - 8 := by
      unfold fits szN at hfit; rw [hcN, hEN] at hfit; exact hfit
    ihave Hs := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hs
    ihave H0 := memBytes_addr (b := len) hcN $$ H0
    ihave H8 := memBytes_addr (b := len + 8) (by omega) $$ H8
    ihave Hd := memBytes_addr (b := len + 12) (by omega) $$ Hd
    ileft
    isplitr
    · ipureintro
      refine ⟨fun h => by rw [h] at hpn; simp at hpn, ?_⟩
      unfold aligned at hali; rw [hcN] at hali; rw [hpn]; exact hali
    rw [hpn]
    iapply pack_W hl0 hE hE4 hE32 rest (by omega) hs0 (by omega)
    iframe Hf Hl H4 Hs H0 H8 Hd
  · -- split
    obtain ⟨hp, hfit, hcs⟩ := hS
    have hfit' : 4 * w.toNat ≤ E - len - 8 := by
      unfold fits szN at hfit; rw [hcN, hEN] at hfit; exact hfit
    have hcs' : len + 80 ≤ p.toNat := by unfold canSplit at hcs; rw [hcN, ← hp] at hcs; exact hcs
    have hA1 : p.toNat + 4 * w.toNat ≤ E := by
      have : aN (UInt32.ofNat E) w al ≤ E - 4 * w.toNat := by unfold aN; rw [hEN]; exact Nat.sub_le _ _
      omega
    have hA4 : p.toNat % 4 = 0 := by rw [hp]; exact aN_mod4 _ w al k hal (by rw [hEN]; omega)
    have hw1 : 1 ≤ w.toNat := by omega
    ihave Hs := memBytes_addr (a := (1074896 : UInt32).toNat) (b := 1074896) rfl $$ Hs
    ihave H0 := AllocDealloc.memBytes_at (b := len) (bs' := bytes32 (UInt32.ofNat (p.toNat - 8))) hcN
      (by rw [sub8_ofNat p (by omega)]) $$ H0
    ihave H8 := memBytes_addr (b := len + 8) (by omega) $$ H8
    ihave Hd := memBytes_addr (b := len + 12) (by omega) $$ Hd
    ihave HN1 := memBytes_addr (b := p.toNat - 8 + 4) (by omega) $$ HN1
    icases HB with ⟨%bs, %hbs, HB⟩
    ileft
    isplitr
    · ipureintro
      refine ⟨fun h => by rw [h] at hcs'; simp at hcs', ?_⟩
      rw [hp]; unfold aN; exact Nat.sub_mod_eq_zero_of_mod_eq (Nat.mod_mod _ _).symm
    have key := pack_S (GF := GF) (n := n) (maxP := maxP) (live := live) hl0 hE hE4 hE32 (m := p.toNat - 8)
      (size := size) (by omega) (by omega) hs0 (by omega) (by omega)
      (rest.take (p.toNat - 8 - (UInt32.ofNat len).toNat - 12)) (by simp; omega) bs (by rw [hbs, hEN]; omega)
    rw [show p.toNat - 8 + 8 = p.toNat by omega] at key
    iapply key
    iframe Hf Hl H4 Hs H0 H8 Hd HN0 HN1 HB

end Pack

/-- Strengthening a specification's precondition by a frame `Fr` that its postcondition
gives back. -/
theorem MFunSpec_frame {cfg : WasmConfig} {lim : ExecLimits} {d : Nat} {type : FuncType} {inst : Nat}
    {mi : ModuleInst} {code : Func} {Cg : Nat} {P P' : List Value → IProp GF} {K : List Value → Nat}
    {Q Q' : List Value → List Value → IProp GF} (Fr : IProp GF) (hP : ∀ args, P' args ⊢ P args ∗ Fr)
    (hQ : ∀ args rs, Fr ∗ Q args rs ⊢ Q' args rs) :
    MFunSpec cfg lim d type inst mi code Cg P K Q ⊢ MFunSpec cfg lim d type inst mi code Cg P' K Q' := by
  unfold MFunSpec
  iintro #H
  imodintro
  iintro %args %R HP Hc
  icases hP args $$ HP with ⟨HP, HF⟩
  iapply mwpInvoke_wand
  isplitl [HP Hc]
  · iapply H $$ %args %R HP Hc
  isplit
  · dsimp only
    iintro %rs ⟨Hc, HQ⟩
    iframe Hc
    iapply hQ args rs
    iframe HF HQ
  · iintro HT; iexact HT

open WNear.Binary.AllocAlloc (res581 pre581 wordsOf chunkEnd f310_fresh)
open WNear.Binary.AllocNewCell (cellPages cellPages_bounds shl16_toNat)
open WNear.Binary.Interface (IfaceMod)

/-- `__rust_alloc(size, align)` (310 → 236 → 581) on a heap whose free list is empty
(`heapInv … 0`: every method's first allocation, and every one after a walk emptied the
list), against the heap invariant. `E = len + P · 65536` is the memory length after the
grow of `P = cellPages` pages. The result is a block `p ≠ 0` with the heap grown to `E` and
`(p, size)` live, its free list at most the split remainder (`F = 1`); or `0` with the heap
valid and live allocations unchanged (memory.grow failed: length `len`; or 580 left the
fresh chunk unused: length `E`). -/
theorem f310_spec_fresh (cfg : WasmConfig) (lim : ExecLimits) (d : Nat) (type : FuncType)
    (htype : type.results.length = 1) (inst : Nat) (mi : ModuleInst) (A : Nat → Nat) (n g ta : Nat)
    (hm : IfaceMod mi A n g ta) (hd : d + 5 < lim.maxCallDepth) (Cg : Nat)
    (gt : GlobalType) (sp size al idx : UInt32) (k : Nat) (maxP len : Nat) (live : List (Nat × Nat))
    (o1 o2 o4 : List UInt8)
    (hsp : 16 ≤ sp.toNat) (hal : al.toNat = 2 ^ k) (hk : k < 20)
    (hsize : 1 ≤ size.toNat) (hsize2 : size.toNat < 2 ^ 28)
    (hlen0 : len % 65536 = 0) (hlen1 : 0 < len)
    (ho1 : o1.length = 4) (ho2 : o2.length = 4) (ho4 : o4.length = 4)
    (hroom : len + (cellPages (wordsOf size) al).toNat * 65536 + 65536 ≤ 2 ^ 32) :
    A 236 ↪[wf] FuncInst.wasm types[13]! inst f236 ∗ A 581 ↪[wf] FuncInst.wasm types[15]! inst f581 ∗
      A 570 ↪[wf] FuncInst.wasm types[32]! inst f570 ∗ A 568 ↪[wf] FuncInst.wasm types[13]! inst f568 ∗
      A 580 ↪[wf] FuncInst.wasm types[34]! inst f580 ∗ A 577 ↪[wf] FuncInst.wasm types[45]! inst f577 ∗
      A 572 ↪[wf] FuncInst.wasm types[32]! inst f572 ∗ A 569 ↪[wf] FuncInst.wasm types[32]! inst f569 ∗
      A 573 ↪[wf] FuncInst.wasm types[32]! inst f573 ∗ A 574 ↪[wf] FuncInst.wasm types[0]! inst f574 ∗
      A 576 ↪[wf] FuncInst.wasm types[32]! inst f576 ∗ A 578 ↪[wf] FuncInst.wasm types[13]! inst f578 ∗
      inst ↪[inst] mi
      ⊢ MFunSpec (GF := GF) cfg lim d type inst mi f310 Cg
        (fun args => iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
          vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 0))
        (fun _ => 15 * cfg.regularOpCost + (15 * cfg.regularOpCost + (630 * cfg.regularOpCost +
          cfg.linearOpBaseCost + cfg.linearOpUnitCost * (cellPages (wordsOf size) al).toNat)))
        (fun _ rs => iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
          (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
            n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
          vt n 1057464 idx ta (A 578) ∗
          allocOut n maxP len (len + (cellPages (wordsOf size) al).toNat * 65536) live size.toNat al p)) := by
  have hW : (wordsOf size).toNat = (size.toNat + 3) / 4 := by
    simp only [wordsOf, UInt32.toNat_ofNat']; omega
  have hal20 : al.toNat < 2 ^ 20 := by rw [hal]; exact Nat.pow_lt_pow_right (by omega) hk
  have hPb := cellPages_bounds (wordsOf size) al (by rw [hW]; omega) hal20
  generalize hCP : cellPages (wordsOf size) al = CP at hPb hroom ⊢
  have hNX : chunkEnd len size al = UInt32.ofNat (len + CP.toNat * 65536) := by
    apply UInt32.toNat_inj.mp
    simp only [chunkEnd, hCP]
    rw [UInt32.toNat_add, shl16_toNat CP hPb.2]
    simp only [UInt32.toNat_ofNat']; omega
  have hP : ∀ args : List Value, iprop(⌜args = [.i32 size, .i32 al]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
      n ↦[wms][ sp.toNat - 16 ] o1 ∗ n ↦[wms][ sp.toNat - 12 ] o2 ∗ n ↦[wms][ sp.toNat - 4 ] o4 ∗
      vt n 1057464 idx ta (A 578) ∗ heapInv n maxP len live 0) ⊢
      iprop((⌜args = [.i32 size, .i32 al]⌝ ∗ (⌜[Value.i32 1074896, Value.i32 size, Value.i32 al] =
        [Value.i32 1074896, Value.i32 size, Value.i32 al]⌝ ∗ pre581 n g gt sp idx ta (A 578) len o1 o2 o4)) ∗
        frameH (GF := GF) n maxP len live) := by
    intro args
    iintro ⟨%ha, Hg, Ho1, Ho2, Ho4, Hvt, Hinv⟩
    icases heapInv_open0 n maxP len live $$ Hinv with ⟨Hh, Hl, Hfr⟩
    iframe Hfr
    isplitr
    · ipureintro; exact ha
    isplitr
    · ipureintro; rfl
    iunfold pre581
    iframe Hg Ho1 Ho2 Ho4 Hh Hl Hvt
  have hQ : ∀ (args rs : List Value), iprop(frameH (GF := GF) n maxP len live ∗
      ∃ p, ⌜rs = [.i32 p]⌝ ∗ res581 n g gt sp size al idx ta (A 578) len p) ⊢
      iprop(∃ p : UInt32, ⌜rs = [.i32 p]⌝ ∗ g ↦[wg] ⟨gt, .i32 sp⟩ ∗
        (∃ b1 b2 b4 : List UInt8, ⌜b1.length = 4 ∧ b2.length = 4 ∧ b4.length = 4⌝ ∗
          n ↦[wms][ sp.toNat - 16 ] b1 ∗ n ↦[wms][ sp.toNat - 12 ] b2 ∗ n ↦[wms][ sp.toNat - 4 ] b4) ∗
        vt n 1057464 idx ta (A 578) ∗
        allocOut n maxP len (len + CP.toNat * 65536) live size.toNat al p) := by
    intro args rs
    iintro ⟨Hfr, %p, %hrs, HR⟩
    iexists p
    isplitr
    · ipureintro; exact hrs
    iunfold res581 at HR
    rw [hCP, hNX, show pageSize = 65536 from rfl]
    icases HR with ⟨Hg, Hst, (⟨%hp0, Hh, Hl, Hvt⟩ | ⟨Hl, H4, %rest, %hrl, Hpost⟩)⟩
    · iframe Hg Hst Hvt
      iunfold allocOut
      iright
      isplitr
      · ipureintro; exact hp0
      iexists len
      isplitr
      · ipureintro; exact Or.inl rfl
      iapply pack_fail
      iframe Hfr Hh Hl
    · iframe Hg Hst
      iapply pack_grown hlen1 (by omega) (by omega) (by omega) (wordsOf size) al k hal (by omega)
        (by rw [hW]; omega) idx ta (A 578) p
      iframe Hfr Hl H4
      iexists rest
      iframe Hpost
      ipureintro; omega
  iintro H
  iapply (MFunSpec_frame (frameH n maxP len live) hP hQ)
  have h310 := f310_fresh (GF := GF) cfg lim d type htype inst mi A n g ta hm hd Cg gt sp size al idx k len
    o1 o2 o4 hsp hal hk hsize hsize2 hlen0 hlen1 ho1 ho2 ho4 (by rw [hCP]; omega)
  rw [hCP] at h310
  iapply h310
  iexact H

end Res

end WNear.Binary.AllocFresh
