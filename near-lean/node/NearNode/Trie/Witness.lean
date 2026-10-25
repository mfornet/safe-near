import Std.Data.HashSet
import NearNode.Trie.Lookup

/-!
# Every object of a trie

The nodes of a trie and the values they point at, each once, by hash: what
`Near.TrieConstruction.build` returns as its witness for the same entries (the Spec builds the trie
again from the entries on every chunk with the list-based SHA-256; the node reads the one it
stores).
-/

namespace Near.Node.Trie

open Borsh

/-- The root node's memory usage and every node and value reachable from `root`, each once. An
empty trie has no objects and memory usage 0. -/
partial def objects (src : NodeSource) (root : CryptoHash) :
    Except String (UInt64 × Array (CryptoHash × ByteArray)) := do
  if root == emptyRoot then
    return (0, #[])
  let mut seen : Std.HashSet CryptoHash := {}
  let mut out : Array (CryptoHash × ByteArray) := #[]
  let mut stack : Array CryptoHash := #[root]
  let mut usage : UInt64 := 0
  let mut first := true
  while !stack.isEmpty do
    let h := stack.back!
    stack := stack.pop
    if seen.contains h then
      continue
    seen := seen.insert h
    let some bytes := src.read h | throw s!"missing trie node {hashHex h}"
    out := out.push (h, bytes)
    let n ←
      match Codec.decodeAll (α := RawTrieNodeWithSize) bytes with
      | .ok n =>
        pure n
      | .error e =>
        throw s!"corrupt trie node {hashHex h}: {repr e}"
    if first then
      usage := n.memoryUsage
      first := false
    let mut valueRef : Option ValueRef := none
    match n.node with
    | .leaf _ v =>
      valueRef := some v
    | .extension _ c =>
      stack := stack.push c
    | .branchNoValue c =>
      stack := c.present.foldl (·.push ·) stack
    | .branchWithValue v c =>
      valueRef := some v
      stack := c.present.foldl (·.push ·) stack
    if let some v := valueRef then
      unless seen.contains v.hash do
        let some data := src.read v.hash | throw s!"missing trie value {hashHex v.hash}"
        seen := seen.insert v.hash
        out := out.push (v.hash, data)
  return (usage, out)

end Near.Node.Trie
