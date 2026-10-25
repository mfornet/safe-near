import Std.Data.HashSet
import NearNode.Trie.Lookup

/-!
# State parts

`core/store/src/trie/state_parts.rs` and the iterator of `ops/iter.rs` (nearcore `44f7ae6`): how a
trie is cut into parts for state sync, how a part is checked against the state root, and what
applying it stores.

The state is cut by a depth-first walk of the trie: the boundary of part `i` of `n` is the first node
holding a value after about `total_size / n * i` of the nodes' own memory usage
(`find_state_part_boundary`). A part is the set of nodes and values the walk of the interval
`[boundary i, boundary i+1)` reads, including the path to both boundaries and the siblings left of
them (`visit_nodes_interval`, `find_child_in_dfs_order`); the receiver does the same walk on the
part alone, so that every node it reads has to be in the part, and the part has to hold nothing else
(`validate_state_part`: the nodes read are exactly the nodes given).

Everything here reads through a `NodeSource` and records the hashes read, so the same walk generates
a part from a stored trie and checks one. `partNodes` is the generation used by the tests (nearcore
generates from flat storage and gets the same set); applying a part adds one reference to each node
and value of the interval (`apply_state_part_impl`).
-/

namespace Near.Node.Trie

open Borsh

/-- The walk's monad: the hashes read so far. -/
abbrev PM :=
  StateT (Std.HashSet CryptoHash) (Except String)

/-- A node as the state part code sees it (`TrieStorageNode`). -/
inductive SN where
  | empty
  | leaf (ext : ByteArray) (value : ValueRef)
  | extension (ext : ByteArray) (child : CryptoHash)
  | branch (children : Array (Option CryptoHash)) (value : Option ValueRef)
  deriving Inhabited

/-- A node and the memory usage of its subtree. -/
structure SNs where
  node : SN
  usage : UInt64
  deriving Inhabited

private def readObject (src : NodeSource) (h : CryptoHash) : PM ByteArray := do
  match src.read h with
  | some b =>
    modify (·.insert h)
    pure b
  | none =>
    throw s!"missing trie value {hashHex h}"

private def decodeNode (b : ByteArray) (h : CryptoHash) : Except String SNs :=
  match Codec.decodeAll (α := RawTrieNodeWithSize) b with
  | .error e => throw s!"corrupt trie node {hashHex h}: {repr e}"
  | .ok n =>
    let node : SN :=
      match n.node with
      | .leaf k v => .leaf k v
      | .extension k c => .extension k c
      | .branchNoValue c => .branch c.slots none
      | .branchWithValue v c => .branch c.slots (some v)
    .ok ⟨node, n.memoryUsage⟩

/-- `retrieve_storage_node`: the empty root is the empty node. -/
def loadNode (src : NodeSource) (h : CryptoHash) : PM SNs := do
  if h == emptyRoot then
    return ⟨.empty, 0⟩
  decodeNode (← readObject src h) h

/-- `memory_usage_direct`: the cost of one node (`TRIE_COSTS` 50, 2 and 1). -/
def SN.usageDirect : SN → UInt64
  | .empty => 0
  | .leaf ext v => 50 + ext.size.toUInt64 * 2 + (v.length.toUInt64 + 50)
  | .branch _ v => 50 + (v.map fun v => v.length.toUInt64 + 50).getD 0
  | .extension ext _ => 50 + ext.size.toUInt64 * 2

private def extNibs (ext : ByteArray) : Except String Nibs := do
  pure (← hpDecode ext).1

private def extArray (ext : ByteArray) : Except String (Array UInt8) := do
  pure (← extNibs ext).data

/-- The key bytes of an even-length nibble path (`NibbleSlice::nibbles_to_bytes`, which asserts the
length is even). -/
private def nibblesToBytes (n : Array UInt8) : Except String ByteArray := do
  unless n.size % 2 == 0 do
    throw "state part boundary with an odd number of nibbles"
  pure (ofNibs ⟨n⟩)

/-- Where the search for the boundary node goes next. -/
private inductive Next where
  | found (key : Array UInt8)
  | go (node : SNs) (skipped : UInt64) (key : Array UInt8)

/-- One step towards the node where the memory skipped passes the threshold
(`find_child_in_dfs_order`). -/
private def descend (src : NodeSource) (threshold : UInt64) (node : SNs) (skipped : UInt64)
    (key : Array UInt8) : PM Next := do
  let skipped := skipped + node.node.usageDirect
  match node.node with
  | .empty =>
    pure (.found key)
  | .leaf ext _ =>
    pure (.found (key ++ (← extArray ext)))
  | .branch children value =>
    if skipped > threshold && value.isSome then
      return .found key
    let mut skipped := skipped
    for i in [0:16] do
      if let some child := children[i]! then
        let c ← loadNode src child
        if skipped + c.usage > threshold then
          return .go c skipped (key.push i.toUInt8)
        skipped := skipped + c.usage
    throw s!"skipped all children of a node while searching for memory threshold {threshold}"
  | .extension ext child =>
    let c ← loadNode src child
    pure (.go c skipped (key ++ (← extArray ext)))

/-- The nibbles of the first key-value node whose prefix memory usage passes `threshold`
(`find_node_in_dfs_order`). -/
partial def findNodeInDfsOrder (src : NodeSource) (root : SNs) (threshold : UInt64) :
    PM (Array UInt8) := do
  let rec go (node : SNs) (skipped : UInt64) (key : Array UInt8) : PM (Array UInt8) := do
    match ← descend src threshold node skipped key with
    | .found k =>
      pure k
    | .go c s k =>
      go c s k
  go root 0 #[]

/-- The key at which part `idx` of `total` starts: the empty key for the first part, none for the end
(`find_state_part_boundary`). -/
def partBoundary (src : NodeSource) (root : CryptoHash) (idx total : UInt64) :
    PM (Option ByteArray) := do
  if idx > total then
    throw "state part index above the part count"
  if idx == 0 then
    return some ByteArray.empty
  if idx == total then
    return none
  let rootNode ← loadNode src root
  let totalSize := rootNode.usage
  let start := totalSize / total * idx + min idx (totalSize % total)
  if rootNode.usage ≤ start then
    return none
  let nibbles ← findNodeInDfsOrder src rootNode start
  pure (some (← nibblesToBytes nibbles))

/-! ### The iterator -/

private inductive CS where
  | entering
  | at_
  | atChild (i : Nat)
  | exiting

private structure Crumb where
  node : SN
  status : CS

private inductive Step where
  | cont
  | pop
  | descend (h : CryptoHash)
  | value (v : ValueRef)

private structure It where
  trail : Array Crumb := #[]
  key : Array UInt8 := #[]

private def lexCmp (a b : Array UInt8) (ai bi : Nat) : Ordering :=
  Id.run do
    let n := min (a.size - ai) (b.size - bi)
    for i in [0:n] do
      let x := a[ai + i]!
      let y := b[bi + i]!
      if x != y then
        return compare x y
    return compare (a.size - ai) (b.size - bi)

private def commonPrefix (a : Array UInt8) (ai : Nat) (b : Array UInt8) (bi : Nat) : Nat :=
  Id.run do
    let n := min (a.size - ai) (b.size - bi)
    let mut i := 0
    while i < n && a[ai + i]! == b[bi + i]! do
      i := i + 1
    return i

/-- `seek_nibble_slice` for a range seek: positions the iterator on the first node at or after `key`;
returns the pointer of the last node entered. -/
private def seek (src : NodeSource) (root : CryptoHash) (target : Array UInt8) :
    PM (It × Option CryptoHash) := do
  let mut it : It := {}
  let mut ptr : Option CryptoHash := if root == emptyRoot then none else some root
  let mut key := target
  repeat
    let node ←
      match ptr with
      | some h =>
        pure (← loadNode src h).node
      | none =>
        pure SN.empty
    let mut crumb : Crumb := { node, status := .entering }
    let mut stop := false
    match node with
    | .empty =>
      stop := true
    | .leaf ext _ =>
      let e ← extArray ext
      if lexCmp e key 0 0 == .lt then
        it := { it with key := it.key ++ e }
        crumb := { crumb with status := .exiting }
      stop := true
    | .branch children _ =>
      if key.isEmpty then
        stop := true
      else
        let idx := key[0]!
        it := { it with key := it.key.push idx }
        crumb := { crumb with status := .atChild idx.toNat }
        match children[idx.toNat]! with
        | some child =>
          ptr := some child
          key := key.extract 1 key.size
        | none =>
          stop := true
    | .extension ext child =>
      let e ← extArray ext
      if commonPrefix key 0 e 0 == e.size then
        key := key.extract e.size key.size
        ptr := some child
        crumb := { crumb with status := .at_ }
        it := { it with key := it.key ++ e }
      else
        if lexCmp e key 0 0 == .lt then
          crumb := { crumb with status := .exiting }
          it := { it with key := it.key ++ e }
        stop := true
    it := { it with trail := it.trail.push crumb }
    if stop then
      break
  pure (it, ptr)

/-- `iter_step`: advance the last crumb and say what to do. -/
private def iterStep (it : It) : Except String (Option (It × Step)) := do
  let some last := it.trail.back? | return none
  -- `Crumb::increment` (no prefix boundary here)
  let status : CS :=
    match last.node, last.status with
    | .empty, _ => .exiting
    | _, .entering => .at_
    | .branch .., .at_ => .atChild 0
    | .branch .., .atChild x => if x < 15 then .atChild (x + 1) else .exiting
    | _, _ => .exiting
  let trail := it.trail.set! (it.trail.size - 1) { last with status }
  let it : It := { it with trail }
  match status, last.node with
  | .exiting, n =>
    let key ←
      match n with
      | .leaf ext _ | .extension ext _ =>
        let e ← extArray ext
        pure (it.key.extract 0 (it.key.size - e.size))
      | .branch .. =>
        pure it.key.pop
      | .empty =>
        pure it.key
    pure (some ({ it with key }, .pop))
  | .at_, .branch _ value =>
    pure
        (some
          (it,
            match value with
            | some v => .value v
            | none => .cont))
  | .at_, .leaf ext v =>
    let e ← extArray ext
    pure (some ({ it with key := it.key ++ e }, .value v))
  | .at_, .extension ext child =>
    let e ← extArray ext
    pure (some ({ it with key := it.key ++ e }, .descend child))
  | .atChild i, .branch children _ =>
    let key := if i == 0 then it.key.push 0 else it.key
    match children[i]! with
    | some child =>
      let key := if i != 0 then key.set! (key.size - 1) i.toUInt8 else key
      pure (some ({ it with key }, .descend child))
    | none =>
      pure (some ({ it with key }, .cont))
  | _, _ =>
    throw "trie iterator in an impossible state"

/-- The key of the node the iterator is at, if it holds a value (`has_value` and `key`). -/
private def currentKey (it : It) : Except String (Option ByteArray) := do
  let holds :=
    match it.trail.back? with
    | some c =>
      match c.status, c.node with
      | .at_, .branch _ (some _) => true
      | .at_, .leaf .. => true
      | _, _ => false
    | none => false
  if !holds then
    return none
  let mut out := ByteArray.empty
  let mut i := 1
  while i < it.key.size do
    out := out.push ((it.key[i - 1]! <<< 4) ||| it.key[i]!)
    i := i + 2
  pure (some out)

/-- `visit_nodes_interval`: the hash of every node and value in `[pathBegin, pathEnd)` in order, with
the key of the ones that hold a value. -/
def visitInterval (src : NodeSource) (root : CryptoHash) (pathBegin pathEnd : Option ByteArray) :
    PM (Array (CryptoHash × Option ByteArray)) := do
  let begin_ := (toNibs (pathBegin.getD (ByteArray.mk #[16]))).data
  let end_ : Array UInt8 :=
    match pathEnd with
    | some p => (toNibs p).data
    | none => #[16]
  let (it0, ptr) ← seek src root begin_
  let lastHash := ptr.getD CryptoHash.zero
  let mut it := it0
  let mut prefixLen := commonPrefix end_ 0 it.key 0
  if lexCmp it.key end_ prefixLen prefixLen != .lt then
    return #[]
  let mut out : Array (CryptoHash × Option ByteArray) := #[]
  if lexCmp it.key begin_ 0 0 != .lt then
    out := out.push (lastHash, ← currentKey it)
  repeat
    let some (it', step) ← iterStep it | break
    it := it'
    match step with
    | .pop =>
      it := { it with trail := it.trail.pop }
      prefixLen := min it.key.size prefixLen
    | .descend h =>
      prefixLen := prefixLen + commonPrefix end_ prefixLen it.key prefixLen
      if lexCmp it.key end_ prefixLen prefixLen != .lt then
        break
      let node ←
        if h == emptyRoot then
          pure SN.empty
        else
          pure (← loadNode src h).node
      it := { it with trail := it.trail.push { node, status := .entering } }
      out := out.push (h, none)
    | .cont =>
      pure ()
    | .value v =>
      if lexCmp it.key end_ prefixLen prefixLen != .lt then
        break
      let _ ← readObject src v.hash
      out := out.push (v.hash, ← currentKey it)
  pure out

/-- The walk both generation and validation do: the nodes and values read for part `idx` of `total`
(`visit_nodes_for_state_part`), as the items visited. -/
def visitPart (src : NodeSource) (root : CryptoHash) (idx total : UInt64) :
    PM (Array (CryptoHash × Option ByteArray)) := do
  let b ← partBoundary src root idx total
  let e ← partBoundary src root (idx + 1) total
  visitInterval src root b e

/-- A part of a stored trie: every node and value the walk reads (nearcore returns the same set; the
order of a set is not part of a part). -/
def partNodes (src : NodeSource) (root : CryptoHash) (idx total : UInt64) :
    Except String (Array ByteArray) := do
  let (_, seen) ← (visitPart src root idx total).run {}
  let mut out := #[]
  for h in seen.toList do
    match src.read h with
    | some b =>
      out := out.push b
    | none =>
      throw s!"missing trie value {hashHex h}"
  pure out

/-- A node source from the nodes of a part (`PartialStorage`): each node by its hash. -/
def partSource (nodes : Array ByteArray) : NodeSource :=
  let m : Std.HashMap CryptoHash ByteArray :=
    nodes.foldl (fun m n => m.insert (CryptoHash.hash n) n) {}
  ⟨fun h => m[h]?⟩

/-- `Trie::validate_state_part`: the walk of the part, with the part as the only storage, reads
every node it was given and nothing else. A part of an empty trie is empty. -/
def validatePart (root : CryptoHash) (idx total : UInt64) (nodes : Array ByteArray) :
    Except String Unit := do
  let (_, seen) ← (visitPart (partSource nodes) root idx total).run {}
  unless seen.size == nodes.size do
    throw "unexpected trie value in a state part"

/-- What applying a part stores (`apply_state_part_impl`): one reference to each node and value of
the interval, as `(hash, data, references)` sorted by hash, and the keys with the values they hold.
The part must have been validated. -/
def applyPart (root : CryptoHash) (idx total : UInt64) (nodes : Array ByteArray) :
    Except String (Array (CryptoHash × ByteArray × UInt32)) := do
  if root == emptyRoot then
    return #[]
  let src := partSource nodes
  let (items, _) ← (visitPart src root idx total).run {}
  let mut counts : Std.HashMap CryptoHash UInt32 := {}
  let mut order : Array CryptoHash := #[]
  for (h, _) in items do
    match counts[h]? with
    | some n =>
      counts := counts.insert h (n + 1)
    | none =>
      counts := counts.insert h 1
      order := order.push h
  let mut out := #[]
  for h in order do
    let some data := src.read h | throw s!"missing trie value {hashHex h}"
    out := out.push (h, data, counts[h]!)
  pure (out.qsort fun a b => Borsh.compareBytes a.1.bytes b.1.bytes == .lt)

end Near.Node.Trie
