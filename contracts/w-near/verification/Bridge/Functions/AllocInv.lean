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
* `AllocNewCell.lean`: `new_cell_for_free_list` (577), the fresh chunk.

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

`HeapInv n live F` (below, `heapInv`) is parametrised by a *Lean-level*
list `live` of the live allocations `(ptr, size)` — as the harness's
`__rust_alloc` contract (`Harness/Builtins.lean`) — and by `F`, an upper
bound on the length of the free list. No ghost state is needed: the method
proofs are sequential and thread `live` and `F` as values; `dealloc` asks
`(ptr, size) ∈ live` as a pure premise.

`heapInv n live F` owns:

* the head word `1074896 ↦ head`;
* the memory's length `n ↦[wmlength] len` (only wee_alloc grows memory, and
  nothing else in the binary runs `memory.size`), and the persistent limit
  `n ↪[wmlimit] some maxP` (`maxP = 2048` pages under the protocol);
* for every cell of every chunk: its header (words 0 and 1); for a free cell
  also its whole data (`next_free` and the rest, any bytes); for an
  allocated cell the data bytes *not* lent to the client (the slack past
  `size` up to `next`).

and states the pure facts of a `HeapModel` (`chunks`, their cells,
`free list`), `HeapModel.wf`:

1. chunks are disjoint, page-aligned, and tile `[mem0, len)` where `mem0` is
   the memory length at instantiation (so `len` is a multiple of 65536 and,
   under `maxP`, `len ≤ 2048 * 65536 < 2^32`: no address arithmetic of 576,
   577 or 580 overflows, so none of their `panic` branches (853) is taken);
2. within a chunk, cells are consecutive (`c.next` is the next cell, or the
   end with bit 1), each `prev` is the previous cell (0 for the first),
   every cell has at least 16 data bytes;
3. the free list `head, f₁, …, f_k` is a list of *distinct free* cells,
   linked by `next_free & !3`, ending in 0, `k ≤ F`;
4. a list cell with `CAN_MERGE` is followed in the list by its previous
   neighbour, which is free (so the merge in 580 finds a free neighbour, and
   `unchecked_unwrap` holds);
5. `live` is exactly the allocated cells, each `(c + 8, size)` with
   `size ≤ c.next - c - 8` and `c + 8` aligned as requested;
6. free cells not in the list ("leaked") are allowed.

At method entry the instance is fresh: `head = 0`, no chunk, `len = mem0`,
so `heapInv n [] 0` holds (`heapInv_init`).

## 3. The specs

`Block n p size := n ↦[wms][ p ] bs` with `bs.length = size` (any bytes).

```
__rust_alloc(size, align)            -- 0 < size, align a power of 2, size + align ≤ 2^31
  { heapInv n live F ∗ g_sp ↦ sp ∗ 16 bytes of shadow stack below sp }
  returns p, with the stack restored and
  { p ≠ 0 ∗ ⌜p % align = 0⌝ ∗ heapInv n ((p, size) :: live) (max F 1) ∗ Block n p size
    ∨ p = 0 ∗ heapInv n live 0 }                  -- memory.grow failed
  cost ≤ 30 + A₀ + A₁ * F + linearOpBaseCost + linearOpUnitCost * cellPages(words, align)

__rust_dealloc(p, size, align)
  { heapInv n live F ∗ ⌜(p, size) ∈ live⌝ ∗ Block n p size }
  { heapInv n (live.erase (p, size)) (F + 1) }
  cost ≤ 32 + D₀
```

*Why alloc's postcondition holds.* Each walk step keeps (1)–(6) with the
walked prefix dropped from the list (it stays as leaked free cells); a split
creates a new allocated cell at the tail of a free cell `c` (`c.next` and
the new cell's `prev`/`next` updated, the following neighbour's `prev` —
which may be an allocated cell, so headers must belong to the invariant, not
to the clients), and lends `[p, p + size)` from the free cell's data, which
the invariant owned; merging (575) removes a cell from its chunk's
neighbour list and gives its header and data to the free previous cell
(clause 4 is exactly the premise that makes this sound). On the grow path
the fresh chunk is `[len, len + k·65536)`, appended to the tiling (clause 1)
and pushed; the second walk takes it.

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
available at every call).

## 4. What is proved, what remains

Proved (no `sorry`): the leaves, the wrappers, `memory.grow`, and 577 (both
the success and the failure branch). Remaining, bottom-up:

* 575 `Neighbors::remove` (straight-line, four conditional header updates);
* 582 `dealloc`'s three cases from (1)–(6) (straight-line, calls 570, 576,
  575);
* 580 `alloc_first_fit` (690 instructions, two nested loops, one
  `call_indirect` to the policy's `min_cell_size`): loop invariant = clauses
  (1)–(6) for the remaining list plus the leaked prefix, and credits
  `A₁ * (remaining list cells)`;
* 581 from 580 and 577; then `__rust_alloc`/`__rust_dealloc` by
  `AllocWrap`.
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

/-- Clauses (1)–(6) of the design, for the live allocations `live` and the
bound `F` on the free list. -/
def wf (H : HeapModel) (live : List (Nat × Nat)) (F : Nat) : Prop :=
  -- (1) the chunks tile `[mem0, len)`: cells are consecutive, page-aligned chunk starts
  H.mem0 % 65536 = 0 ∧ H.len % 65536 = 0 ∧ H.mem0 ≤ H.len ∧ H.len < 2 ^ 32 ∧
  (∀ c ∈ H.cells, H.mem0 ≤ c.addr ∧ c.addr + 24 ≤ c.next ∧ c.next ≤ H.len ∧ c.addr % 4 = 0) ∧
  (H.cells.map (·.addr)).Pairwise (· < ·) ∧
  -- (2) neighbours: `next`/`prev` link consecutive cells of a chunk
  (∀ c ∈ H.cells, c.last = false → ∃ d ∈ H.cells, d.addr = c.next ∧ d.prev = c.addr) ∧
  (∀ c ∈ H.cells, c.prev ≠ 0 → ∃ d ∈ H.cells, d.addr = c.prev ∧ d.next = c.addr ∧ d.last = false) ∧
  (∀ c ∈ H.cells, c.prev = 0 → c.addr % 65536 = 0) ∧
  -- (3) the free list: distinct free cells, linked by `next_free`, at most `F`
  H.freeList.Nodup ∧ H.freeList.length ≤ F ∧
  (∀ a ∈ H.freeList, ∃ c, H.cellAt a = some c ∧ c.allocated = false) ∧
  (∀ i (h : i < H.freeList.length), ∃ c, H.cellAt H.freeList[i] = some c ∧
    c.nextFree / 4 * 4 = H.freeList.getD (i + 1) 0) ∧
  -- (4) `CAN_MERGE`: followed in the list by its free previous neighbour
  (∀ i (h : i < H.freeList.length), ∀ c, H.cellAt H.freeList[i] = some c → c.nextFree % 2 = 1 →
    ∃ d, H.freeList[i + 1]? = some d.addr ∧ H.cellAt d.addr = some d ∧ d.allocated = false ∧
      c.prev = d.addr) ∧
  -- (5) the live allocations are the allocated cells
  (∀ p s, (p, s) ∈ live ↔ ∃ c ∈ H.cells, c.allocated = true ∧ p = c.addr + 8 ∧ s ≤ c.size) ∧
  live.Nodup

end HeapModel

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

/-- `HeapInv n live F`: the allocator's state, with the live allocations
`live` and at most `F` cells in the free list; `maxP` the memory's limit in
pages. -/
def heapInv (n maxP : Nat) (live : List (Nat × Nat)) (F : Nat) : IProp GF :=
  iprop(∃ H : HeapModel, ⌜H.wf live F ∧ H.len ≤ maxP * 65536⌝ ∗
    n ↦[wms][ headAddr ] bytes32 (UInt32.ofNat H.head) ∗ n ↦[wmlength] H.len ∗
    n ↪[wmlimit] some maxP ∗ [∗list] c ∈ H.cells, cellRes n live c)

/-- A block lent to the client: `size` bytes at `p`, any contents. -/
def block (n p size : Nat) : IProp GF :=
  iprop(∃ bs : List UInt8, ⌜bs.length = size⌝ ∗ n ↦[wms][ p ] bs)

/-- At instantiation: the head is 0 and there is no chunk. -/
theorem heapInv_init (n maxP len : Nat) (h1 : len % 65536 = 0) (h2 : len ≤ maxP * 65536)
    (h3 : len < 2 ^ 32) :
    n ↦[wms][ headAddr ] bytes32 0 ∗ n ↦[wmlength] len ∗ n ↪[wmlimit] some maxP
      ⊢ heapInv (GF := GF) n maxP [] 0 := by
  iintro ⟨Hh, Hl, Hm⟩
  iunfold heapInv
  iexists { mem0 := len, len := len, cells := [], freeList := [] }
  isplitr
  · ipureintro
    refine ⟨⟨h1, h1, Nat.le_refl len, h3, by simp, by simp, by simp, by simp, by simp, by simp,
      by simp, by simp, by simp, by simp, by simp, by simp⟩, h2⟩
  simp only [HeapModel.head, List.headD_nil]
  iframe Hh Hl Hm
  iapply BigSepL.bigSepL_nil.2
  iempintro

/-- A larger bound on the free list is still a bound. -/
theorem heapInv_mono (n maxP : Nat) (live : List (Nat × Nat)) (F F' : Nat) (h : F ≤ F') :
    heapInv (GF := GF) n maxP live F ⊢ heapInv n maxP live F' := by
  iintro H
  iunfold heapInv at H
  icases H with ⟨%M, %⟨hwf, hlen⟩, Hh, Hl, Hm, Hc⟩
  iunfold heapInv
  iexists M
  isplitr
  · ipureintro
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16⟩ := hwf
    exact ⟨⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, by omega, a12, a13, a14, a15, a16⟩, hlen⟩
  iframe Hh Hl Hm Hc

end Res

end WNear.Binary.AllocInv
