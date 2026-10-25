import NearInterface.TrieConstruction
import NearNode.Trie.Mem

/-!
# Trie specification

`NearInterface.TrieConstruction.build` is the specification: the canonical root, memory usage and
node set of a complete entry set, written without any update algorithm. The `Impl` of this package
must agree with it on the root, the memory usage and the multiset of nodes.
-/

namespace Near.Node.Trie

open Near.TrieConstruction

/-- The canonical root and memory usage of a complete entry set. -/
def specRoot (entries : List (ByteArray × ByteArray)) : Except String (CryptoHash × Nat) := do
  let b ← Near.TrieConstruction.build (entries.map fun (k, v) => (k.toList, v.toList))
  return (⟨ByteArray.mk b.root.toArray⟩, b.memoryUsage)

/-- The objects (nodes and values) of the canonical trie by hash. -/
def specObjects (entries : List (ByteArray × ByteArray)) :
    Except String (List (CryptoHash × ByteArray)) := do
  let b ← Near.TrieConstruction.build (entries.map fun (k, v) => (k.toList, v.toList))
  return b.witness.map fun (h, d) => (⟨ByteArray.mk h.toArray⟩, ByteArray.mk d.toArray)

end Near.Node.Trie
