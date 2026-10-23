import Wasm.Value

/-!
# Linear memory

A memory is an array of pages; a page is either untouched (an empty
`ByteArray`, read as zeros) or materialised (64 KiB). Untouched pages cost
nothing, so a memory grown to its 4 GiB maximum is fine until written to.
`ByteArray` updates happen in place when the memory is not shared.

Everything is addressed in bytes with `Nat`; callers check bounds through
the `Option` results.
-/

namespace Wasm

def pageSize : Nat := 65536

/-- The largest memory the spec allows, in pages. -/
def maxPages : Nat := 65536

structure Memory where
  pages : Array ByteArray
  max : Option Nat
deriving Inhabited

namespace Memory

def new (min : Nat) (max : Option Nat) : Memory :=
  { pages := Array.replicate min ByteArray.empty, max }

/-- Size in pages. -/
def size (m : Memory) : Nat := m.pages.size

def byteSize (m : Memory) : Nat := m.pages.size * pageSize

def inBounds (m : Memory) (addr len : Nat) : Bool := addr + len ≤ m.byteSize

def read8 (m : Memory) (addr : Nat) : UInt8 :=
  match m.pages[addr / pageSize]? with
  | some page => if page.size = 0 then 0 else page[addr % pageSize]!
  | none => 0

def materialise (page : ByteArray) : ByteArray :=
  if page.size = 0 then ByteArray.mk (Array.replicate pageSize 0) else page

/-- Write one byte; the address must be in bounds. -/
def write8 (m : Memory) (addr : Nat) (b : UInt8) : Memory :=
  { m with pages := m.pages.modify (addr / pageSize) fun page =>
      (materialise page).set! (addr % pageSize) b }

/-- Read `len` bytes as a little-endian natural number. -/
def readNat (m : Memory) (addr len : Nat) : Option Nat :=
  if m.inBounds addr len then
    some ((List.range len).foldr (fun i acc => acc * 256 + (m.read8 (addr + i)).toNat) 0)
  else none

/-- Write the low `len` bytes of `v`, little-endian. -/
def writeNat (m : Memory) (addr len : Nat) (v : Nat) : Option Memory :=
  if m.inBounds addr len then
    some ((List.range len).foldl (fun m i => m.write8 (addr + i) (UInt8.ofNat (v >>> (8 * i)))) m)
  else none

def readBytes (m : Memory) (addr len : Nat) : Option ByteArray :=
  if m.inBounds addr len then
    some ((List.range len).foldl (fun acc i => acc.push (m.read8 (addr + i)))
      (ByteArray.emptyWithCapacity len))
  else none

def writeBytes (m : Memory) (addr : Nat) (bytes : ByteArray) : Option Memory :=
  if m.inBounds addr bytes.size then
    some ((List.range bytes.size).foldl (fun m i => m.write8 (addr + i) bytes[i]!) m)
  else none

/-- Read bytes as a list; out-of-bounds bytes read as zero. Host functions
that check bounds themselves use this total form. Irreducible so that
unification never unfolds a byte loop; proofs go through lemmas. -/
@[irreducible] def readList (m : Memory) (addr len : Nat) : List UInt8 :=
  (List.range len).map fun i => m.read8 (addr + i)

@[simp] theorem readList_length (m : Memory) (addr len : Nat) :
    (m.readList addr len).length = len := by
  unfold readList
  simp

/-- Write a list of bytes; out-of-bounds bytes are dropped. -/
@[irreducible] def writeList (m : Memory) (addr : Nat) (data : List UInt8) : Memory :=
  (List.range data.length).foldl
    (fun m i => if addr + i < m.byteSize then m.write8 (addr + i) data[i]! else m) m

/-- `memory.fill`: bounds are checked before anything is written. -/
def fill (m : Memory) (addr len : Nat) (b : UInt8) : Option Memory :=
  if m.inBounds addr len then
    some ((List.range len).foldl (fun m i => m.write8 (addr + i) b) m)
  else none

/-- `memory.copy`, with overlapping ranges handled as `memmove`. -/
def copy (m : Memory) (dst src len : Nat) : Option Memory :=
  if m.inBounds dst len && m.inBounds src len then
    let bytes := (List.range len).map fun i => m.read8 (src + i)
    some ((List.range len).foldl (fun m i => m.write8 (dst + i) bytes[i]!) m)
  else none

/-- Grow by `delta` pages. Fails beyond the declared maximum or the spec's
limit, in which case the memory is unchanged. -/
def grow (m : Memory) (delta : Nat) : Option Memory :=
  let newSize := m.size + delta
  if newSize > maxPages then none
  else if m.max.any (newSize > ·) then none
  else some { m with pages := m.pages ++ Array.replicate delta ByteArray.empty }

end Memory

end Wasm
