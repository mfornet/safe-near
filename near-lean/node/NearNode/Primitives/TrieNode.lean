import NearNode.Primitives.Storage

/-!
# Raw trie nodes

`core/store/src/trie/raw_node.rs` (nearcore `44f7ae6`): the Borsh form of a trie node and of a
node with the memory usage of its subtree. `Children` is a 16-bit bitmap followed by the hashes of
the children present, in index order.
-/

namespace Near.Node

open Borsh

/-- The 16 child slots of a branch. -/
structure Children where
  slots : Array (Option CryptoHash)
  deriving BEq, Inhabited

namespace Children

def empty : Children :=
  ⟨Array.replicate 16 none⟩

/-- The bitmap of occupied slots. -/
def mask (c : Children) : UInt16 :=
  (List.range 16).foldl (fun m i => if (c.slots[i]!).isSome then m ||| (1 <<< i.toUInt16) else m) 0

/-- The hashes present, in slot order. -/
def present (c : Children) : Array CryptoHash :=
  c.slots.filterMap id

end Children

private def childrenSpec : Spec.Codec Children where
  enc c := Spec.u16.enc c.mask ++ (c.present.toList.flatMap fun h => h.bytes.toList)
  dec l := do
    let (m, r) ← Spec.u16.dec l
    let mut slots : Array (Option CryptoHash) := Array.replicate 16 none
    let mut rest := r
    for i in [0:16] do
      if (m >>> i.toUInt16) &&& 1 == 1 then
        let (h, r') ← (Spec.fixed 32).dec rest
        slots := slots.set! i (some ⟨h⟩)
        rest := r'
    pure (⟨slots⟩, rest)

private def childrenImpl : Impl.Codec Children where
  put c d :=
    Id.run do
      let mut d := Impl.u16.put c.mask d
      for s in c.slots do
        if let some h := s then
          d := d.append h.bytes
      return d
  get d p :=
    match Impl.u16.get d p with
    | .err e => .err e
    | .ok m q =>
      Id.run do
        let mut slots : Array (Option CryptoHash) := Array.replicate 16 none
        let mut pos := q
        for i in [0:16] do
          if (m >>> i.toUInt16) &&& 1 == 1 then
            if pos + 32 ≤ d.size then
              slots := slots.set! i (some ⟨d.extract pos (pos + 32)⟩)
              pos := pos + 32
            else
              return .err .eof
        return .ok ⟨slots⟩ pos

instance : Codec Children :=
  ⟨childrenSpec, childrenImpl⟩

/-- `RawTrieNode`; the keys are hex-prefix encoded nibble paths. -/
inductive RawTrieNode where
  | leaf (key : ByteArray) (value : ValueRef)
  | branchNoValue (children : Children)
  | branchWithValue (value : ValueRef) (children : Children)
  | extension (key : ByteArray) (child : CryptoHash)
  deriving BEq, Inhabited

instance : Codec RawTrieNode :=
  .enum "RawTrieNode"
    [.variant 0 (ByteArray × ValueRef) (fun (k, v) => .leaf k v) fun
        | .leaf k v => some (k, v)
        | _ => none,
      .variant 1 Children .branchNoValue fun
        | .branchNoValue c => some c
        | _ => none,
      .variant 2 (ValueRef × Children) (fun (v, c) => .branchWithValue v c) fun
        | .branchWithValue v c => some (v, c)
        | _ => none,
      .variant 3 (ByteArray × CryptoHash) (fun (k, c) => .extension k c) fun
        | .extension k c => some (k, c)
        | _ => none]

/-- `RawTrieNodeWithSize`: the node and the memory usage of its subtree. -/
structure RawTrieNodeWithSize where
  node : RawTrieNode
  memoryUsage : UInt64
  deriving BEq, Inhabited

instance : Codec RawTrieNodeWithSize :=
  .iso (RawTrieNode × UInt64) (fun (n, m) => ⟨n, m⟩) fun x => (x.node, x.memoryUsage)

end Near.Node
