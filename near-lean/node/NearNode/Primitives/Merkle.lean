import NearNode.Primitives.Outcome

/-!
# Merkle trees

`near-primitives::merkle` at `=0.37.4`: `combine_hash`, `merklize` with its proofs, path
verification and `PartialMerkleTree` (the block merkle tree). `MerklePathItem` is in `Outcome`.
-/

namespace Near.Node

open Borsh

/-- `combine_hash`: the hash of two concatenated hashes. -/
def combineHash (a b : CryptoHash) : CryptoHash :=
  CryptoHash.hash (a.bytes ++ b.bytes)

/-- `merklize` on the leaf hashes: the root and the proof of every leaf. An empty list has the zero
root. The proofs are built bottom-up, exactly as nearcore does. -/
def merklizeHashes (leaves : Array CryptoHash) : CryptoHash × Array (Array MerklePathItem) :=
  if leaves.isEmpty then (CryptoHash.zero, #[])
  else
    let n := leaves.size
    let len0 := n.nextPowerOfTwo
    if len0 == 1 then (leaves[0]!, #[#[]])
    else
      Id.run do
        let mut hashes := leaves
        let mut paths : Array (Array MerklePathItem) :=
          (Array.range n).map fun i =>
            if i % 2 == 0 then if i + 1 < n then #[⟨hashes[i + 1]!, .right⟩] else #[]
            else #[⟨hashes[i - 1]!, .left⟩]
        let mut len := len0
        let mut arrLen := n
        let mut counter := 1
        for _ in [0:len0.log2] do
          len := len / 2
          counter := counter * 2
          for i in [0:len] do
            if 2 * i >= arrLen then
              continue
            let h :=
              if 2 * i + 1 >= arrLen then hashes[2 * i]!
              else combineHash hashes[2 * i]! hashes[2 * i + 1]!
            hashes := hashes.set! i h
            if len > 1 then
              if i % 2 == 0 then
                for j in [0:counter] do
                  let index := (i + 1) * counter + j
                  if index < n then
                    paths := paths.modify index (·.push ⟨h, .left⟩)
              else
                for j in [0:counter] do
                  let index := (i - 1) * counter + j
                  if index < n then
                    paths := paths.modify index (·.push ⟨h, .right⟩)
          arrLen := (arrLen + 1) / 2
        return (hashes[0]!, paths)

/-- `merklize`: the leaf of an item is the hash of its Borsh encoding. -/
def merklize [Codec α] (items : Array α) : CryptoHash × Array (Array MerklePathItem) :=
  merklizeHashes (items.map CryptoHash.hashBorsh)

/-- `compute_root_from_path`. -/
def computeRootFromPath (path : Array MerklePathItem) (leaf : CryptoHash) : CryptoHash :=
  path.foldl (init := leaf) fun acc item =>
    match item.direction with
    | .left => combineHash item.hash acc
    | .right => combineHash acc item.hash

/-- `verify_hash`. -/
def verifyHash (root : CryptoHash) (path : Array MerklePathItem) (leaf : CryptoHash) : Bool :=
  computeRootFromPath path leaf == root

/-- `verify_path`. -/
def verifyPath [Codec α] (root : CryptoHash) (path : Array MerklePathItem) (item : α) : Bool :=
  verifyHash root path (CryptoHash.hashBorsh item)

/-- `PartialMerkleTree`: the path of the next leaf and the number of leaves. -/
structure PartialMerkleTree where
  path : Array CryptoHash
  size : UInt64
  deriving BEq, Inhabited

instance : Codec PartialMerkleTree :=
  .iso (Array CryptoHash × UInt64) (fun (p, s) => ⟨p, s⟩) fun x => (x.path, x.size)

namespace PartialMerkleTree

/-- The path has one hash per set bit of the size. -/
def isWellFormed (t : PartialMerkleTree) : Bool :=
  t.path.size == (Nat.toDigits 2 t.size.toNat).count '1'

/-- The root of the tree; the zero hash when empty. -/
def root (t : PartialMerkleTree) : CryptoHash :=
  match t.path.back? with
  | none => CryptoHash.zero
  | some last => (t.path.pop.foldr (fun h acc => combineHash h acc) last)

/-- Append a leaf. Needs a well-formed tree. -/
def insert (t : PartialMerkleTree) (elem : CryptoHash) : PartialMerkleTree :=
  Id.run do
    let mut s := t.size
    let mut node := elem
    let mut path := t.path
    for _ in [0:path.size + 1] do
      if s % 2 == 1 then
        match path.back? with
        | some last =>
          node := combineHash last node
          path := path.pop
        | none =>
          pure ()
        s := s / 2
      else
        break
    return ⟨path.push node, t.size + 1⟩

end PartialMerkleTree

end Near.Node
