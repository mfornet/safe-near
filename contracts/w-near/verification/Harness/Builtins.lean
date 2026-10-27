import Harness.Contract

/-!
# First contracts: compiler builtins and the allocator

The functions that fix the harness's interface (plan, M1): `memcpy`,
`memset`, `bcmp` and `__multi3` (compiler_builtins), and `__rust_alloc`
(wee_alloc 0.4.5 behind `alloc`'s global allocator). Indices and names are
from `Binary/functions.tsv`.

Costs are in units of `regular_op_cost`, counted from the bodies under
`Wasm.Near.runMetered`'s rules: every instruction but `block` costs one, a
taken branch back to a `loop` one more, and entering a function
`activationGas` (64 bytes plus its parameters and locals, in 8-byte units).
-/

namespace WNear.Testing

open Wasm Wasm.Near

def i32 (n : Nat) : Value := .i32 (UInt32.ofNat n)
def i64 (n : Nat) : Value := .i64 (UInt64.ofNat n)

def u32Arg (args : List Value) (k : Nat) : Nat :=
  match args[k]? with
  | some (.i32 v) => v.toNat
  | _ => 0

def u64Arg (args : List Value) (k : Nat) : Nat :=
  match args[k]? with
  | some (.i64 v) => v.toNat
  | _ => 0

def op (h : Harness) (n : Nat) : Nat := h.cfg.wasm.regularOpCost * n

def returnsU32 (r : Run) : Option Nat :=
  match r.ending with
  | .returned [.i32 v] => some v.toNat
  | _ => none

/-- The run returned normally. -/
def ended (r : Run) : Option String :=
  match r.ending with
  | .returned _ => none
  | e => some e.describe

def overlap (a n b m : Nat) : Bool := a < b + m && b < a + n

/-! ## `memcpy` (951)

`memcpy(dst, src, n) -> dst`, a forward byte loop. Non-overlapping ranges
inside memory: the loop copies forward, so `dst > src` with overlap
duplicates bytes instead of copying them. -/

def memcpy : Contract Unit where
  name := "memcpy"
  func := 951
  pre h i :=
    let (dst, src, n) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    if dst + n > h.memSize i.store then some "dst + n beyond memory"
    else if src + n > h.memSize i.store then some "src + n beyond memory"
    else if n > 0 && overlap dst n src n then some "ranges overlap"
    else none
  footprint _ i := [(u32Arg i.args 0, u32Arg i.args 2)]
  post h i r :=
    let (dst, src, n) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    (ended r).or <|
    if returnsU32 r != some dst then some "does not return dst"
    else if h.read r.after dst n != h.read r.before src n then some "dst is not the source bytes"
    else none
  -- Activation 10; block, eqz, br_if 3; then for n > 0: the two sets 2,
  -- `loop` 1, 17 per iteration and 1 per back-edge; the result 1.
  cost h i := let n := u32Arg i.args 2; op h (if n == 0 then 14 else 16 + 18 * n)
  ghostOf _ _ := some ()

/-! ## `memset` (952)

`memset(dst, c, n) -> dst`: the low byte of `c` in `n` bytes from `dst`. -/

def memset : Contract Unit where
  name := "memset"
  func := 952
  pre h i :=
    if u32Arg i.args 0 + u32Arg i.args 2 > h.memSize i.store then some "dst + n beyond memory" else none
  footprint _ i := [(u32Arg i.args 0, u32Arg i.args 2)]
  post h i r :=
    let (dst, c, n) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    (ended r).or <|
    if returnsU32 r != some dst then some "does not return dst"
    else if h.read r.after dst n != List.replicate n (UInt8.ofNat c) then some "bytes are not c"
    else none
  cost h i := let n := u32Arg i.args 2; op h (if n == 0 then 14 else 16 + 13 * n)
  ghostOf _ _ := some ()

/-! ## `bcmp` (953)

`bcmp(a, b, n)`: zero exactly when the `n` bytes agree; otherwise the
difference of the first pair that differs, as an `i32`. Its cost depends on
where that pair is. -/

/-- The index of the first differing byte. -/
def firstDiff (xs ys : List UInt8) : Option Nat :=
  ((xs.zip ys).zipIdx.find? fun ((x, y), _) => x != y).map (·.2)

def bcmp : Contract Unit where
  name := "bcmp"
  func := 953
  pre h i :=
    let (a, b, n) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    if a + n > h.memSize i.store || b + n > h.memSize i.store then some "range beyond memory" else none
  footprint _ _ := []
  post h i r :=
    let (a, b, n) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    let xs := h.read r.before a n
    let ys := h.read r.before b n
    let expected := match firstDiff xs ys with
      | none => 0
      | some k => (xs[k]!.toNat + 2 ^ 32 - ys[k]!.toNat) % 2 ^ 32
    (ended r).or <|
    if returnsU32 r != some expected then s!"returns {r.ending.describe}, expected {expected}" else none
  -- Activation 11; the result's set, the length test 5; then per equal pair
  -- 24 (23 instructions and the back-edge). The last equal pair leaves the
  -- loop after 22; a differing pair after 8, then the subtraction 4. The
  -- result 1.
  cost h i :=
    let (a, b, n) := (u32Arg i.args 0, u32Arg i.args 1, u32Arg i.args 2)
    op h <| match firstDiff (h.read i.store a n) (h.read i.store b n) with
      | none => if n == 0 then 17 else 16 + 24 * n
      | some k => 30 + 24 * k
  ghostOf _ _ := some ()

/-! ## `__multi3` (954)

`__multi3(out, a_lo, a_hi, b_lo, b_hi)`: the product of two `u128`s, modulo
`2^128`, stored little-endian in the 16 bytes at `out`. -/

def multi3 : Contract Unit where
  name := "__multi3"
  func := 954
  pre h i := if u32Arg i.args 0 + 16 > h.memSize i.store then some "out + 16 beyond memory" else none
  footprint _ i := [(u32Arg i.args 0, 16)]
  post h i r :=
    let a := u64Arg i.args 1 + 2 ^ 64 * u64Arg i.args 2
    let b := u64Arg i.args 3 + 2 ^ 64 * u64Arg i.args 4
    (ended r).or <|
    if h.readNat r.after (u32Arg i.args 0) 16 != a * b % 2 ^ 128 then some "product is wrong" else none
  -- Activation 20 (36 bytes of parameters, 56 of locals); 60 instructions.
  cost h _ := op h 80
  ghostOf _ _ := some ()

/-! ## `__rust_alloc` (310)

`__rust_alloc(size, align)` through wee_alloc. The ghost is the list of live
allocations `(ptr, size)`: the result is null or a block of `size` bytes,
aligned, above `__heap_base`, inside memory and disjoint from every live
one, and no live block's bytes changed. Its footprint is the allocator's:
the heap, the free-list head and its stack frames.

The cost walks the free list: one bound per free cell. -/

/-- `WeeAlloc`'s free-list head (the static `ALLOC` in `.bss`). -/
def freeListHead : Nat := 1074896

/-- `__heap_base`, global 2. -/
def heapBase : Nat := 1074944

/-- The free cells, walked from the head through `next_free` (offset 8),
whose low bits are flags; at most `bound`. -/
def freeCells (h : Harness) (s : Store NearState) (bound : Nat := 10000) : Nat := Id.run do
  let mut p := h.readNat s freeListHead 4
  let mut n := 0
  for _ in [0:bound] do
    if p == 0 then break
    n := n + 1
    p := h.readNat s (p + 8) 4 / 4 * 4
  pure n

def isPow2 (n : Nat) : Bool := n != 0 && n &&& (n - 1) == 0

def alloc : Contract (List (Nat × Nat)) where
  name := "__rust_alloc"
  func := 310
  pre h i :=
    let (size, align) := (u32Arg i.args 0, u32Arg i.args 1)
    if !isPow2 align then some "align is not a power of two"
    else if size == 0 then some "size is zero"
    else if size + align > 2 ^ 31 then some "size overflows isize"
    else if i.ghost.any fun (p, n) => p < heapBase || p + n > h.memSize i.store then
      some "a live block outside the heap"
    else none
  footprint _ _ := [(freeListHead, 4), (heapBase, 2 ^ 32 - heapBase)]
  stack := 64
  grows := true
  post h i r :=
    let (size, align) := (u32Arg i.args 0, u32Arg i.args 1)
    (ended r).or <|
    match returnsU32 r with
    | none => some "no pointer returned"
    | some 0 => none
    | some p =>
      if p % align != 0 then some s!"{p} is not {align}-aligned"
      else if p < heapBase then some s!"{p} below __heap_base"
      else if p + size > h.memSize r.after then some s!"{p} + {size} beyond memory"
      else if i.ghost.any fun (q, n) => overlap p size q n then some s!"{p} overlaps a live block"
      else if i.ghost.any fun (q, n) => h.read r.before q n != h.read r.after q n then
        some "a live block changed"
      else none
  -- Provisional (M4 states the allocator's cost properly): fixed work plus
  -- a bound per free cell walked, and the `memory.grow` of a fresh cell.
  cost h i := op h (2000 + 200 * freeCells h i.store) +
    h.cfg.wasm.linearOpBaseCost + h.cfg.wasm.linearOpUnitCost * (u32Arg i.args 0 / pageSize + 2)
  ghostOf _ _ := some []

end WNear.Testing
