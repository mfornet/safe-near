import NearLogic.Tactic.Control

/-!
# wee_alloc's heap invariant `HeapInv` (milestone M4, layer L3): the design

`contract.wasm` allocates through wee_alloc 0.4.5 with only its
`LargeAllocPolicy` (no size classes). This file states the design of the
heap invariant and of the allocator's specs, and defines the invariant. What
is proved so far is in

* `AllocLeaves.lean`: the helpers 568, 569, 570, 572, 573, 574, 576, 578;
* `AllocWrap.lean`: `__rust_alloc` (310) → `__rg_alloc` (236) → 581 and
  `__rust_dealloc` (311) → `__rg_dealloc` (237) → 582, parametric in the
  specs of 581/582 (cost `+30` / `+32`);
* `AllocGrow.lean`: the metered rule for `memory.grow`
  (`mwpi_memory_grow_either`);
* `AllocNewCell.lean`: `new_cell_for_free_list` (577), the fresh chunk;
* `AllocRemove.lean`: `Neighbors::remove` (575);
* `AllocDealloc.lean`: `dealloc` (582) and `__rust_dealloc` (311) against `heapInv`;
* `AllocFirstFit.lean`: `alloc_first_fit` (580) on lists of at most one cell;
* `AllocAlloc.lean`: `alloc` (581) and `__rust_alloc` (310) on an empty list, raw;
* `AllocFresh.lean`: the latter packed into `heapInv` (`f310_spec_fresh`);
* `AllocLimit.lean`: `memory.grow` holding the memory's limit, and 577 with it;
* `AllocGen.lean`: 581/310 for any first walk, limit-aware (`f310_gen`);
* `AllocSeqModel.lean`, `AllocSeqPack.lean`, `AllocSeq.lean`: alloc on `heapInv … 1`
  (`f310_spec_seq`: every sequence of allocations without frees) and with room
  (`f310_spec_room`: `p ≠ 0`);
* `AllocTwoSeq.lean`, `AllocTwoHeap.lean`: alloc on `heapInv … 2` with room (`f310_spec_two`).

## 1. The code, as it is in the binary

```
__rust_alloc(size, align)            310 → 236 → 581(&ALLOC, size, align)
__rust_dealloc(ptr, size, align)     311 → 237 → 582(&ALLOC, ptr, size, align)
ALLOC (the free-list head)           the word at 1074896, in .bss (0 at instantiation)
```

*Cells.* The heap is made of chunks, each obtained from one `memory.grow`
(577 asks for `ceil((max(4 * words, 8 * (align + 64)) + 8) / 65536)` pages, so
at least one page). A chunk is a sequence of cells; a cell `c` is

```
c + 0  word0 = next | NEXT_CELL_IS_INVALID (2) | ALLOCATED (1)
c + 4  word1 = prev                         (0 for the chunk's first cell)
c + 8  data, up to `next`                   size = next - c - 8   (576)
       a free cell's first data word is next_free | CAN_MERGE (1)
```

`next` is the next cell of the chunk, or the chunk's end with bit 1 set for
the last cell (so `next` never leaves the chunk); `prev` the previous cell.
A fresh chunk is one free cell (577: word0 = `end | 2`, word1 = 0,
next_free = 0).

*Alloc (581).* `size = 0` returns `align` (never on wNEAR's paths). Else
`words = ceil(size / 4)` (570), the head is copied into a stack slot, and
`alloc_first_fit` (580) walks the free list *from that slot*:

* a cell whose `CAN_MERGE` bit is set is merged into its previous neighbour
  (575, `Neighbors::remove`), which is free and becomes the current cell;
* a cell big enough is split at its end (the new allocated cell is the
  aligned tail, at least `min_cell_size = 16` words (578 through the policy's
  vtable, `call_indirect`) left in front) or, if it cannot be split and is
  aligned, taken whole (unlinked from the list);
* any other cell is **unlinked**: `*slot = cell.next_free`. wee_alloc 0.4.5's
  `walk_free_list` writes every step to the head itself, so cells walked past
  leave the free list for good (they stay free cells of their chunk and are
  reclaimed only by a later merge with a neighbour being freed). This is the
  well-known leak of wee_alloc, and it is what makes the walk cheap to bound.

If the walk fails the slot (and so the list) is empty; 577 grows memory and
pushes the fresh cell, and the walk runs again on that one cell, which fits
by construction. If `memory.grow` fails, 577 returns `Err`, 581 stores the
(now empty) list back and returns 0.

*Dealloc (582).* `ptr = 0` or `size = 0` returns. Else the cell `ptr - 8` is
marked free and:
* if its previous neighbour is free it is merged into it (575) and the list
  is unchanged;
* else if its next neighbour (not past the chunk end) is free, the cell is
  linked right after that neighbour, whose `next_free` gets `CAN_MERGE`
  (the merge happens lazily, in the next walk);
* else it is pushed at the head.

## 2. `HeapInv`

`heapInv n maxP len live F` is parametrised by the memory's length `len`, by
a *Lean-level* list `live` of the live allocations `(ptr, size)` — as the
harness's `__rust_alloc` contract (`Harness/Builtins.lean`) — and by `F`, an
upper bound on the length of the free list. No ghost state is needed: the
method proofs are sequential and thread `len`, `live` and `F` as values;
`dealloc` asks `(ptr, size) ∈ live` as a pure premise.

`len` is a parameter (not bounded by `maxP` inside the invariant): the
`memory.grow` rule 577 is proved with (`wpi_memory_grow_either`) does not see
the limit, so after a grow nothing relates the new length to `maxP`; the
caller tracks `len` exactly (alloc's spec says what it becomes) and gives
each allocation its room (`len + pages · 65536 + 65536 ≤ 2^32`).

`heapInv n maxP len live F` owns:

* the head word `1074896 ↦ head`;
* the memory's length `n ↦[wmlength] len` (only wee_alloc grows memory, and
  nothing else in the binary runs `memory.size`), and the persistent limit
  `n ↪[wmlimit] some maxP` (`maxP = 2048` pages under the protocol);
* for every cell of every chunk: its header (words 0 and 1); for a free cell
  also its whole data (`next_free` and the rest, any bytes); for an
  allocated cell the data bytes *not* lent to the client (the slack past
  `size` up to `next`).

and states the pure facts of a `HeapModel` (`chunks`, their cells,
`free list`), `HeapModel.wf` (a structure: `Geo` = (1)–(2), `Lists` =
(3)–(4), `Lives` = (5), `nf_lo`):

1. `mem0` and `len` page-aligned, `0 < mem0 ≤ len < 2^32`; every cell lies in
   `[mem0, len)`, word-aligned (`addr` and `next`, the latter also for the
   last cell of a chunk, whose `next` is the chunk end), with at least 4
   data bytes (`addr + 12 ≤ next`: a free cell's `next_free` word; a split
   lends cells of `4 · words` bytes, so `+ 24` would fail for small
   allocations); cells sorted by address and **disjoint** (`disj`: a cell
   ends before any cell above it starts — not derivable from the rest, and
   needed to insert a split cell in the middle of the list);
2. within a chunk, cells are consecutive (`c.next` is the next cell unless
   `c` is last), each `prev` is the previous cell, 0 only for the first,
   whose address is page-aligned;
3. the free list `head, f₁, …, f_k` is a list of *distinct free* cells,
   linked by `next_free & !3`, ending in 0, `k ≤ F`; every cell's
   `next_free` has bit 1 clear (`nf_lo : nextFree % 4 < 2`: 580 unlinks a
   cell with the *raw* `next_free`, only `CAN_MERGE` cleared);
4. a list cell with `CAN_MERGE` is followed in the list by its previous
   neighbour, which is free (so the merge in 580 finds a free neighbour, and
   `unchecked_unwrap` holds);
5. (`Lives`) every `(p, s) ∈ live` has `0 < s` and an allocated cell with
   `p = c + 8`, `s ≤ c.size`; every allocated cell has an entry; and
   `(live.map Prod.fst).Nodup` — one entry per cell, so `cellRes`'s slack is
   the client's `size`. (An earlier `↔` form forced every `(c + 8, s)` with
   `s ≤ size` into `live`, which no alloc or dealloc could re-establish;
   `0 < s` because dealloc returns early on `size = 0`.)
6. free cells not in the list ("leaked") are allowed.

At method entry the instance is fresh: `head = 0`, no chunk, `len = mem0`,
so `heapInv n maxP len [] 0` holds (`heapInv_init`).

## 3. The specs

`block n p size := n ↦[wms][ p ] bs` with `bs.length = size` (any bytes).

```
__rust_alloc(size, align)        -- 1 ≤ size < 2^28, align = 2^k ≤ 2^19, 0 < len page-aligned,
                                 -- E := len + cellPages(words, align) · 65536, E + 65536 ≤ 2^32
  { heapInv n maxP len live F ∗ g_sp ↦ sp ∗ shadow stack ∗ min_cell_size's vtable slot }
  returns p, with the stack restored and
  { p ≠ 0 ∗ heapInv n maxP E' ((p, size) :: live) (max F 1) ∗ block n p size
    ∨ p = 0 ∗ heapInv n maxP len' live 0 }
  cost ≤ 30 + A₀ + A₁ * F + linearOpBaseCost + linearOpUnitCost * cellPages(words, align)

__rust_dealloc(p, size, align)
  { heapInv n maxP len live F ∗ ⌜(p, size) ∈ live⌝ ∗ block n p size }
  { heapInv n maxP len (live.erase (p, size)) (F + 1) }
  cost ≤ 32 + D₀
```

Proved: dealloc for every `F` (`AllocDealloc.f311_spec`, `D₀ = 224`); alloc
for `F = 0` (`AllocFresh.f310_spec_fresh`: `E' = E`, `len' ∈ {len, E}`,
`A₀ = 630`) and for `F ≤ 1` (`AllocSeq.f310_spec_seq`: the result again `F = 1`,
`len' ∈ {len, E}`, `p % align = 0`, `A₀ = 910`, a failure saying why: the limit, or
a fresh cell misaligned for `align > 8`); `AllocSeq.f310_spec_room`: no failure
when `E / 65536 ≤ maxP` and `align ≤ 8`.

*Why alloc's postcondition holds.* Each walk step keeps (1)–(6) with the
walked prefix dropped from the list (it stays as leaked free cells); a split
creates a new allocated cell at the tail of a free cell `c` (`c.next` and
the new cell's `prev`/`next` updated, the following neighbour's `prev` —
which may be an allocated cell, so headers must belong to the invariant, not
to the clients), and lends `[p, p + size)` from the free cell's data, which
the invariant owned; merging (575) removes a cell from its chunk's
neighbour list and gives its header and data to the free previous cell
(clause 4 is exactly the premise that makes this sound). On the grow path
the fresh chunk is `[len, len + k·65536)`, appended to the cells
(`AllocFresh.wf_freshU/W/S`) and pushed; the second walk takes it (or, see
AllocFirstFit's finding 5, unlinks it: `p = 0` with the memory grown).

*Gas.* Every iteration of 580's outer loop pops (or returns) one list cell
and every iteration of its inner merge loop removes one list cell, so the
walk makes at most `2F` iterations; each costs a constant (`A₁`, by count
once 580 is proved; the harness provisionally uses 200 per free cell). The
grow path walks the empty list once more and then one cell, and pays
`memory.grow` (`linear_op_base_cost + linear_op_unit_cost * pages`, charged
also when it fails). wNEAR's methods allocate a bounded number of times, so
`F` stays bounded by the number of deallocations in the method (dealloc
adds at most one cell; alloc leaves at most `max F 1`).

*Failure.* `memory.grow` fails exactly when `len / 65536 + pages` exceeds
the limit. The spec reports it (`p = 0`, heap still valid with an empty
list); its callers (`RawVec::allocate_in` etc.) then call
`handle_alloc_error` (→ 314 → 843), which traps. For refinement this branch
must be shown unreachable: `len = mem0 + 65536 · (pages grown)`, each grow
happens only for an allocation that did not fit, and grows at most
`cellPages` pages; with `mem0` the protocol's initial memory and the
2048-page limit, a method whose allocations total `S` bytes in `N` calls
grows at most `N + (S + 528 N) / 65536` pages, far below the room left for
the inputs wNEAR accepts. Each method's proof discharges this from its own
allocation bound (`heapInv` records `len`, so the bound is a pure fact
available at every call). `AllocSeq.f310_spec_room` excludes the `p = 0`
branches given that room (`AllocLimit.mwpi_memory_grow_lim` sees the limit).

## 4. What is proved, what remains

Proved (no `sorry`): the leaves, the wrappers, `memory.grow`, 577, 575,
dealloc (582/311) against this invariant, 580 on lists of at most one cell
without merges, 581/310 on an empty list (`AllocAlloc`) and its packing into
this invariant (`AllocFresh`), alloc on `heapInv … 1` (`AllocSeq`: every
sequence of allocations without frees, limit-aware). Remaining:

* 580's general walk (`F ≥ 2`, merges: the lists dealloc leaves), with the
  loop invariant designed in `AllocFirstFit`.
-/

namespace WNear.Binary.AllocInv

open Wasm Wasm.Near WasmLogic NearLogic Iris Iris.BI Iris.ProgramLogic

/-- `ALLOC`, wee_alloc's free-list head (`Harness.Builtins.freeListHead`). -/
def headAddr : Nat := 1074896

/-- One cell of a chunk. `next` is the following cell or the chunk's end;
`last` says it is the end (bit `NEXT_CELL_IS_INVALID`). -/
structure CellM where
  addr : Nat
  next : Nat
  prev : Nat
  last : Bool
  allocated : Bool
  /-- For a free cell: its `next_free` word, flags included. -/
  nextFree : Nat
  deriving DecidableEq, Repr

namespace CellM

/-- Word 0 of the header. -/
def word0 (c : CellM) : Nat := c.next + (if c.last then 2 else 0) + (if c.allocated then 1 else 0)

/-- The data bytes. -/
def size (c : CellM) : Nat := c.next - c.addr - 8

end CellM

/-- The heap's abstract state: the memory length at instantiation, the
cells of every chunk in address order, the free list, the live
allocations. -/
structure HeapModel where
  mem0 : Nat
  len : Nat
  cells : List CellM
  freeList : List Nat
  deriving Repr

namespace HeapModel

/-- The cell at an address. -/
def cellAt (H : HeapModel) (a : Nat) : Option CellM := H.cells.find? (·.addr == a)

/-- The head word: the first cell of the free list, or 0. -/
def head (H : HeapModel) : Nat := H.freeList.headD 0

end HeapModel

/-- Clauses (1)–(2): the cells' geometry. -/
structure Geo (H : HeapModel) : Prop where
  /-- Every cell has at least the 4 data bytes of a free cell's `next_free` word
  (`+ 12`, not `+ 16` data bytes: a split lends cells of `4 · words ≥ 4` bytes). -/
  bounds : ∀ c ∈ H.cells, H.mem0 ≤ c.addr ∧ c.addr + 12 ≤ c.next ∧ c.next ≤ H.len ∧ c.addr % 4 = 0
  /-- `next` is word-aligned also for the last cell of a chunk (the chunk end). -/
  next_al : ∀ c ∈ H.cells, c.next % 4 = 0
  sorted : (H.cells.map (·.addr)).Pairwise (· < ·)
  next_nb : ∀ c ∈ H.cells, c.last = false → ∃ d ∈ H.cells, d.addr = c.next ∧ d.prev = c.addr
  prev_nb : ∀ c ∈ H.cells, c.prev ≠ 0 → ∃ d ∈ H.cells, d.addr = c.prev ∧ d.next = c.addr ∧ d.last = false
  first : ∀ c ∈ H.cells, c.prev = 0 → c.addr % 65536 = 0
  /-- Cells do not overlap: a cell ends before any cell above it starts. -/
  disj : ∀ c ∈ H.cells, ∀ d ∈ H.cells, c.addr < d.addr → c.next ≤ d.addr

/-- Clauses (3)–(4): the free list: distinct free cells, linked by `next_free`, at most
`F`; a list cell with `CAN_MERGE` is followed by its free previous neighbour. -/
structure Lists (H : HeapModel) (F : Nat) : Prop where
  fl_nodup : H.freeList.Nodup
  fl_len : H.freeList.length ≤ F
  fl_free : ∀ a ∈ H.freeList, ∃ c, H.cellAt a = some c ∧ c.allocated = false
  fl_link : ∀ i (h : i < H.freeList.length), ∃ c, H.cellAt H.freeList[i] = some c ∧
    c.nextFree / 4 * 4 = H.freeList.getD (i + 1) 0
  fl_merge : ∀ i (h : i < H.freeList.length), ∀ c, H.cellAt H.freeList[i] = some c → c.nextFree % 2 = 1 →
    ∃ d, H.freeList[i + 1]? = some d.addr ∧ H.cellAt d.addr = some d ∧ d.allocated = false ∧
      c.prev = d.addr

/-- Clause (5): the live allocations are the allocated cells, one entry each. -/
structure Lives (H : HeapModel) (live : List (Nat × Nat)) : Prop where
  /-- Every live allocation is an allocated cell's data, of a positive size no larger
  than the cell's, ... -/
  live_cell : ∀ p s, (p, s) ∈ live → 0 < s ∧ ∃ c ∈ H.cells, c.allocated = true ∧ p = c.addr + 8 ∧ s ≤ c.size
  /-- ... every allocated cell is lent, ... -/
  cell_live : ∀ c ∈ H.cells, c.allocated = true → ∃ s, (c.addr + 8, s) ∈ live
  /-- ... and once. -/
  live_nodup : (live.map Prod.fst).Nodup

/-- Clauses (1)–(6) of the design (clause (6), leaked free cells, is the absence of a
constraint), for the live allocations `live` and the bound `F` on the free list. -/
structure HeapModel.wf (H : HeapModel) (live : List (Nat × Nat)) (F : Nat) : Prop where
  mem0_al : H.mem0 % 65536 = 0
  /-- `mem0` is the memory length at instantiation, positive for every real heap: no cell at
  address 0 (so a listed cell is never confused with the list's end, `AllocTwoSeq`). -/
  mem0_pos : 0 < H.mem0
  len_al : H.len % 65536 = 0
  mem0_le : H.mem0 ≤ H.len
  len_lt : H.len < 2 ^ 32
  geo : Geo H
  lists : Lists H F
  lives : Lives H live
  /-- `next_free` never has bit 1 (`NEXT_CELL_IS_INVALID`) set: 580 unlinks with the raw
  word, so only `CAN_MERGE` may be set. -/
  nf_lo : ∀ c ∈ H.cells, c.nextFree % 4 < 2

section Res

variable {GF : BundledGFunctors} [WasmGS NearState GF]

/-- What the invariant owns of one cell: its header, and the data a client
does not hold (all of it for a free cell, the slack past the lent `size`
for an allocated one). -/
def cellRes (n : Nat) (live : List (Nat × Nat)) (c : CellM) : IProp GF :=
  iprop(n ↦[wms][ c.addr ] bytes32 (UInt32.ofNat c.word0) ∗
    n ↦[wms][ c.addr + 4 ] bytes32 (UInt32.ofNat c.prev) ∗
    if c.allocated then
      ∃ s bs, ⌜(c.addr + 8, s) ∈ live ∧ bs.length = c.size - s⌝ ∗ n ↦[wms][ c.addr + 8 + s ] bs
    else
      ∃ bs, ⌜bs.length + 4 = c.size⌝ ∗ n ↦[wms][ c.addr + 8 ] bytes32 (UInt32.ofNat c.nextFree) ∗
        n ↦[wms][ c.addr + 12 ] bs)

/-- `HeapInv n maxP len live F`: the allocator's state, with the live allocations
`live`, at most `F` cells in the free list and the memory's length `len`; `maxP` the
memory's limit in pages. -/
def heapInv (n maxP len : Nat) (live : List (Nat × Nat)) (F : Nat) : IProp GF :=
  iprop(∃ H : HeapModel, ⌜H.wf live F ∧ H.len = len⌝ ∗
    n ↦[wms][ headAddr ] bytes32 (UInt32.ofNat H.head) ∗ n ↦[wmlength] H.len ∗
    n ↪[wmlimit] some maxP ∗ [∗list] c ∈ H.cells, cellRes n live c)

/-- A block lent to the client: `size` bytes at `p`, any contents. -/
def block (n p size : Nat) : IProp GF :=
  iprop(∃ bs : List UInt8, ⌜bs.length = size⌝ ∗ n ↦[wms][ p ] bs)

/-- At instantiation: the head is 0 and there is no chunk. -/
theorem heapInv_init (n maxP len : Nat) (h1 : len % 65536 = 0) (h0 : 0 < len) (h3 : len < 2 ^ 32) :
    n ↦[wms][ headAddr ] bytes32 0 ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some maxP
      ⊢ heapInv (GF := GF) n maxP len [] 0 := by
  iintro ⟨Hh, Hl, Hm⟩
  iunfold heapInv
  iexists { mem0 := len, len := len, cells := [], freeList := [] }
  isplitr
  · ipureintro
    refine ⟨⟨h1, h0, h1, Nat.le_refl len, h3, ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩,
      ⟨by simp, by simp, by simp, by simp, by simp⟩, ⟨by simp, by simp, by simp⟩, by simp⟩, rfl⟩
  simp only [HeapModel.head, List.headD_nil]
  iframe Hh Hl Hm
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- A larger bound on the free list is still a bound. -/
theorem heapInv_mono (n maxP len : Nat) (live : List (Nat × Nat)) (F F' : Nat) (h : F ≤ F') :
    heapInv (GF := GF) n maxP len live F ⊢ heapInv n maxP len live F' := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hwf, hlen⟩, Hh, Hl, Hm, Hc⟩
  iunfold heapInv
  iexists M
  isplitr
  · ipureintro
    exact ⟨{ hwf with lists := { hwf.lists with fl_len := Nat.le_trans hwf.lists.fl_len h } }, hlen⟩
  iframe Hh Hl Hm Hc

end Res

end WNear.Binary.AllocInv
