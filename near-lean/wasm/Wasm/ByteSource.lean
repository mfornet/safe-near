import Wasm.Binary

/-!
# Byte sources the kernel reads quickly

Proofs about a deployed binary let the kernel run the decoder on its bytes.
Read from a `ByteArray`, every byte costs a walk down a list from the start,
so decoding a large module in the kernel is quadratic in its size and out of
reach. A `ByteSource` holds the same bytes as little-endian chunks at the
leaves of a complete binary tree: reading byte `i` descends the tree to its
chunk and shifts it, a few steps of `Nat` arithmetic, which the kernel does
natively.

`ByteSource.toBytes` is the byte array a source holds, and
`decode_toBytes` says decoding it is decoding the source: the kernel never
has to build the array.
-/

namespace Wasm

/-- Chunks of bytes, each a little-endian `Nat`, at the leaves of a tree. -/
inductive ByteTree where
  | leaf (chunk : Nat)
  | node (left right : ByteTree)

/-- The `i`-th leaf of a complete tree of depth `depth` (leaves numbered from
the left), or `0` past the end. -/
def ByteTree.chunk : ByteTree → (depth i : Nat) → Nat
  | .leaf c, _, _ => c
  | .node l r, d + 1, i => if i < 2 ^ d then l.chunk d i else r.chunk d (i - 2 ^ d)
  | .node _ _, 0, _ => 0

/-- `size` bytes, in chunks of `chunkSize` bytes at the leaves of a complete
tree of depth `depth`. -/
structure ByteSource where
  tree : ByteTree
  depth : Nat
  chunkSize : Nat
  size : Nat

namespace ByteSource

/-- Byte `i` of the source, `0` past its end. -/
def read (s : ByteSource) (i : Nat) : UInt8 :=
  if i < s.size then
    ((s.tree.chunk s.depth (i / s.chunkSize) >>> (8 * (i % s.chunkSize))) % 256).toUInt8
  else 0

/-- The bytes of the source. -/
def toBytes (s : ByteSource) : ByteArray := ⟨Array.ofFn (n := s.size) fun i => s.read i⟩

/-- The decoder's input for the whole source. -/
def input (s : ByteSource) : Binary.Input := { read := s.read, size := s.size, limit := s.size }

@[simp] theorem size_toBytes (s : ByteSource) : s.toBytes.size = s.size := by
  simp [toBytes, ByteArray.size]

theorem getElem?_toBytes (s : ByteSource) (i : Nat) : s.toBytes[i]?.getD 0 = s.read i := by
  by_cases h : i < s.size
  · rw [getElem?_pos _ _ (by simpa using h)]
    simp [toBytes, ByteArray.getElem_eq_getElem_data]
  · rw [getElem?_neg _ _ (by simpa using h)]
    simp [read, h]

/-- The decoder reads the bytes of a source as it reads the source. -/
theorem ofBytes_toBytes (s : ByteSource) : Binary.Input.ofBytes s.toBytes = s.input := by
  simp only [Binary.Input.ofBytes, input, size_toBytes, getElem?_toBytes]

theorem decode_toBytes (s : ByteSource) : Binary.decode s.toBytes = Binary.decodeInput s.input := by
  rw [Binary.decode, ofBytes_toBytes]

end ByteSource

end Wasm
