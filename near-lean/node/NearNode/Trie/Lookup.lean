import NearNode.Trie.Update

/-!
# Trie lookups and iteration

`Trie::get`, `contains_key`, the recording of the nodes a lookup reads (`TrieRecorder`), and
in-order iteration with a lower bound (`TrieIterator::seek` followed by `next`).

Lookups read the stored bytes in place, without building a node.
-/

namespace Near.Node.Trie

open Borsh

private def u16At (b : ByteArray) (o : Nat) : Nat :=
  (b.get! o).toNat ||| (b.get! (o + 1)).toNat <<< 8

private def u32At (b : ByteArray) (o : Nat) : Nat :=
  u16At b o ||| u16At b (o + 2) <<< 16

private def refAt (b : ByteArray) (o : Nat) : ValueRef :=
  ⟨(u32At b o).toUInt32, ⟨b.extract (o + 4) (o + 36)⟩⟩

private def popcount (x : Nat) : Nat :=
  (List.range 16).foldl (fun n i => if x >>> i &&& 1 == 1 then n + 1 else n) 0

/-- The nibble of `key` at position `p`. -/
def nibbleAt (key : ByteArray) (p : Nat) : UInt8 :=
  let b := key.get! (p / 2)
  if p % 2 == 0 then b >>> 4 else b &&& 15

/-- Does the hex-prefix path `enc` equal `key[p..]`, and is it the end? Returns the path length. -/
private def pathMatch (enc : ByteArray) (key : ByteArray) (p : Nat) : Except String (Option Nat) :=
  do
  let (e, _) ← hpDecode enc
  let rest := 2 * key.size - p
  if e.size > rest then
    return none
  for i in [0:e.size] do
    if e.get! i != nibbleAt key (p + i) then
      return none
  return some e.size

private def read (src : NodeSource) (h : CryptoHash) : Except String ByteArray :=
  match src.read h with
  | some b => .ok b
  | none => .error s!"missing trie node {hashHex h}"

/-- The reference to the value of `key`, with the nodes read recorded in `rec`
(`lookup_from_state_column`). -/
def getRef (src : NodeSource) (root : CryptoHash) (key : ByteArray) (rc : Option Recorder := none) :
    Except String (Option ValueRef × Option Recorder) := do
  let mut h := root
  let mut p := 0
  let mut rc := rc
  let total := 2 * key.size
  for _ in [0:total + 2] do
    if h == emptyRoot then
      return (none, rc)
    let b ← read src h
    rc := rc.map (·.insert h b)
    match b.get! 0 with
    | 0 =>
      let n := u32At b 1
      let m ← pathMatch (b.extract 5 (5 + n)) key p
      return (if m == some (total - p) then some (refAt b (5 + n)) else none, rc)
    | 3 =>
      let n := u32At b 1
      match ← pathMatch (b.extract 5 (5 + n)) key p with
      | some len =>
        h := ⟨b.extract (5 + n) (37 + n)⟩
        p := p + len
      | none =>
        return (none, rc)
    | tag =>
      if tag != 1 && tag != 2 then
        throw s!"corrupt trie node {hashHex h}"
      let maskAt := if tag == 1 then 1 else 37
      let mask := u16At b maskAt
      if p == total then
        return (if tag == 2 then some (refAt b 1) else none, rc)
      let i := (nibbleAt key p).toNat
      if mask >>> i &&& 1 == 0 then
        return (none, rc)
      let k := popcount (mask &&& ((1 <<< i) - 1))
      let o := maskAt + 2 + 32 * k
      h := ⟨b.extract o (o + 32)⟩
      p := p + 1
  throw "trie deeper than its key"

/-- `Trie::get`: the value of `key`; the value is recorded as well. -/
def get (src : NodeSource) (root : CryptoHash) (key : ByteArray) (rc : Option Recorder := none) :
    Except String (Option ByteArray × Option Recorder) := do
  let (r, rc) ← getRef src root key rc
  match r with
  | none =>
    return (none, rc)
  | some r =>
    let v ← read src r.hash
    return (some v, rc.map (·.insert r.hash v))

/-- `Trie::contains_key`: reads no value. -/
def contains (src : NodeSource) (root : CryptoHash) (key : ByteArray) : Except String Bool := do
  return (← getRef src root key).1.isSome

private def lexCmp (a b : Nibs) : Ordering :=
  Id.run do
    for i in [0:min a.size b.size] do
      if a.get! i != b.get! i then
        return compare (a.get! i) (b.get! i)
    return compare a.size b.size

/-- Where the subtree below `path` lies against the bound: all keys smaller (`lt`), possibly some
(`eq`), or all at least the bound (`gt`). -/
private def rel (path lo : Nibs) : Ordering :=
  Id.run do
    for i in [0:min path.size lo.size] do
      if path.get! i != lo.get! i then
        return compare (path.get! i) (lo.get! i)
    return if path.size < lo.size then .eq else .gt

mutual
/-- The subtree at `h`, whose path is `path`. -/
private partial def walk (src : NodeSource) (ln : Nibs) (f : α → ByteArray → ValueRef → α × Bool)
    (h : CryptoHash) (path : Nibs) (acc : α) : Except String (α × Bool) := do
  if h == emptyRoot then
    return (acc, true)
  let r := rel path ln
  if r == .lt then
    return (acc, true)
  let b ← read src h
  match Codec.decodeAll (α := RawTrieNodeWithSize) b with
  | .error e =>
    throw s!"corrupt trie node {hashHex h}: {repr e}"
  | .ok n =>
    match n.node with
    | .leaf k v =>
      let (e, _) ← hpDecode k
      let full := path ++ e
      if lexCmp full ln == .lt then
        return (acc, true)
      return f acc (ofNibs full) v
    | .extension k c =>
      let (e, _) ← hpDecode k
      walk src ln f c (path ++ e) acc
    | .branchNoValue c =>
      children src ln f c path acc
    | .branchWithValue v c =>
      let (acc, go) := if r == .gt then f acc (ofNibs path) v else (acc, true)
      if go then
        children src ln f c path acc
      else
        return (acc, false)
private partial def children (src : NodeSource) (ln : Nibs)
    (f : α → ByteArray → ValueRef → α × Bool) (c : Children) (path : Nibs) (acc : α) :
    Except String (α × Bool) := do
  let mut acc := acc
  for i in [0:16] do
    if let some ch := c.slots[i]! then
      let (a, go) ← walk src ln f ch (path.push i.toUInt8) acc
      acc := a
      if !go then
        return (acc, false)
  return (acc, true)
end

/-- Visit the entries with key at least `lo`, in key order, until `f` answers `false`. -/
def foldFrom (src : NodeSource) (root : CryptoHash) (lo : ByteArray) (init : α)
    (f : α → ByteArray → ValueRef → α × Bool) : Except String α := do
  return (← walk src (toNibs lo) f root ByteArray.empty init).1

/-- All entries, in key order, as references. -/
def entries (src : NodeSource) (root : CryptoHash) : Except String (Array (ByteArray × ValueRef)) :=
  foldFrom src root ByteArray.empty #[] fun acc k v => (acc.push (k, v), true)

end Near.Node.Trie
