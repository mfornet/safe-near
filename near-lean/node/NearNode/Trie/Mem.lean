import NearNode.Trie.Lookup

/-!
# An in-memory node store

Trie nodes and values by hash with their reference counts, as the `State` column keeps them, and
the application of `TrieChanges` (`StoreUpdate::trie_changes` and the refcount merge of
`DBCol::State`).
-/

namespace Near.Node.Trie

/-- Nodes and values by hash with their reference counts. -/
structure MemStore where
  map : Std.HashMap CryptoHash (ByteArray × Int) := {}

namespace MemStore

def source (s : MemStore) : NodeSource :=
  ⟨fun h => s.map.get? h |>.bind fun (d, rc) => if rc > 0 then some d else none⟩

/-- Add and remove references; an entry whose count reaches zero is dropped, a negative one is an
error (`DBCol::State` cannot hold fewer than zero references). -/
def apply (s : MemStore) (c : TrieChanges) : Except String MemStore := do
  let mut m := s.map
  for a in c.insertions do
    let (_, rc) := m.getD a.hash (a.data, 0)
    m := m.insert a.hash (a.data, rc + a.rc.toNat)
  for d in c.deletions do
    match m.get? d.hash with
    | none =>
      throw s!"removing a reference to an absent node {hashHex d.hash}"
    | some (data, rc) =>
      let rc := rc - d.rc.toNat
      if rc < 0 then
        throw s!"negative refcount for {hashHex d.hash}"
      m := if rc == 0 then m.erase d.hash else m.insert d.hash (data, rc)
  return ⟨m⟩

def size (s : MemStore) : Nat :=
  s.map.size

end MemStore

/-- The trie of a complete entry set: every entry inserted into the empty trie. -/
def fromEntries (entries : Array (ByteArray × ByteArray)) : Except String (TrieChanges) := do
  let src : NodeSource := ⟨fun _ => none⟩
  let u ← update src emptyRoot (entries.map fun (k, v) => (k, some v))
  return u.changes

end Near.Node.Trie
