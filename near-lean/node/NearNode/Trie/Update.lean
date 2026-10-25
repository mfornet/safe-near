import NearNode.Trie.Types

/-!
# Trie update

`Trie::update` of nearcore `44f7ae6` (`core/store/src/trie/mod.rs`, `trie_storage_update.rs`,
`ops/insert_delete.rs`, `ops/squash.rs`): a batch of insertions and deletions applied to the trie at
a root, producing the new root and the refcount deltas.

The trie is a function of its entries, so the result is the canonical trie; what matters beyond
the root are the other outputs, and they follow nearcore exactly:

* the nodes read are the ones `move_node_to_mutable` loads (the path of every key, the surviving
  child when a branch collapses), each one loaded is a reference removed, and each node of the new
  trie that was loaded or created is a reference added; a node that comes back with the same hash
  cancels out;
* a value is a reference added when it is written and a reference removed when it is replaced or
  deleted;
* the memory usage of a node is `direct + children`, kept as a delta along the path so an untouched
  child is never read for its size.

A working node is one of nearcore's updated nodes: `old h` is a subtree not loaded.
-/

namespace Near.Node.Trie

open Borsh

/-- A value in the working trie: already stored, or new. -/
inductive Val where
  | ref (r : ValueRef)
  | mem (data : ByteArray)

namespace Val

def length : Val → UInt64
  | .ref r => r.length.toUInt64
  | .mem d => d.size.toUInt64

end Val

/-- A working node with the memory usage of its subtree. A branch has 16 slots; `empty` is an
absent child. -/
inductive W where
  | old (h : CryptoHash)
  | empty
  | leaf (ext : Nibs) (v : Val) (mem : UInt64)
  | ext (ext : Nibs) (child : W) (mem : UInt64)
  | branch (cs : Array W) (v : Option Val) (mem : UInt64)
  deriving Inhabited

namespace W

def mem : W → UInt64
  | .leaf _ _ m | .ext _ _ m | .branch _ _ m => m
  | _ => 0

end W

/-- `memory_usage_direct` of each node kind (`ops/interface.rs`). -/
def valueCost (len : UInt64) : UInt64 :=
  len * byteOfValue + nodeCost

def directLeaf (ext : Nibs) (v : Val) : UInt64 :=
  nodeCost + (hpSize ext.size).toUInt64 * byteOfKey + valueCost v.length

def directExt (ext : Nibs) : UInt64 :=
  nodeCost + (hpSize ext.size).toUInt64 * byteOfKey

def directBranch (v : Option Val) : UInt64 :=
  nodeCost + (v.map fun v => valueCost v.length).getD 0

def mkLeaf (ext : Nibs) (v : Val) : W :=
  .leaf ext v (directLeaf ext v)

/-- An extension over a child whose subtree has `childMem`. -/
def mkExt (ext : Nibs) (child : W) (childMem : UInt64) : W :=
  .ext ext child (directExt ext + childMem)

def mkBranch (cs : Array W) (v : Option Val) (childrenMem : UInt64) : W :=
  .branch cs v (directBranch v + childrenMem)

def emptySlots : Array W :=
  Array.replicate 16 W.empty

/-- Reference counts changed by an update: data to store and signed count per hash. -/
abbrev Deltas :=
  Std.HashMap CryptoHash (Option ByteArray × Int)

structure St where
  deltas : Deltas := {}
  recorder : Option Recorder := none

abbrev M :=
  ReaderT NodeSource (StateT St (Except String))

def addRef (h : CryptoHash) (data : ByteArray) (n : Int) : M Unit :=
  modify fun s =>
    let (_, rc) := s.deltas.getD h (none, 0)
    { s with deltas := s.deltas.insert h (some data, rc + n) }

def subRef (h : CryptoHash) (n : Int) : M Unit :=
  modify fun s =>
    let (d, rc) := s.deltas.getD h (none, 0)
    { s with deltas := s.deltas.insert h (d, rc - n) }

def record (h : CryptoHash) (data : ByteArray) : M Unit :=
  modify fun s => { s with recorder := s.recorder.map (·.insert h data) }

private def u16At (b : ByteArray) (o : Nat) : Nat :=
  (b.get! o).toNat ||| (b.get! (o + 1)).toNat <<< 8

private def u32At (b : ByteArray) (o : Nat) : Nat :=
  u16At b o ||| u16At b (o + 2) <<< 16

private def u64At (b : ByteArray) (o : Nat) : UInt64 :=
  (List.range 8).foldl (fun acc i => acc ||| (b.get! (o + i)).toUInt64 <<< (8 * i).toUInt64) 0

private def popcount16 (x : Nat) : Nat :=
  (List.range 16).foldl (fun n i => if x >>> i &&& 1 == 1 then n + 1 else n) 0

private def refAt (b : ByteArray) (o : Nat) : ValueRef :=
  ⟨(u32At b o).toUInt32, ⟨b.extract (o + 4) (o + 36)⟩⟩

/-- The children of a branch whose bitmap is at `o`, as working slots. -/
private def slotsAt (b : ByteArray) (o : Nat) : Array W :=
  Id.run do
    let mask := u16At b o
    let mut slots := emptySlots
    let mut p := o + 2
    for i in [0:16] do
      if mask >>> i &&& 1 == 1 then
        slots := slots.set! i (.old ⟨b.extract p (p + 32)⟩)
        p := p + 32
    return slots

/-- Decode the bytes of a stored node into a working node, whose children are not loaded. This is
`RawTrieNodeWithSize`'s Borsh decoder with the same rejections (a cut or over-long node), without
building the intermediate value. -/
def decodeW (b : ByteArray) : Except String W := do
  if b.size < 9 then
    throw "trie node too short"
  let mem := u64At b (b.size - 8)
  let bad : Except String W := throw "corrupt trie node"
  match b.get! 0 with
  | 0 =>
    let n := u32At b 1
    if b.size != 5 + n + 36 + 8 then
      bad
    else
      let (e, _) ← hpDecode (b.extract 5 (5 + n))
      return .leaf e (.ref (refAt b (5 + n))) mem
  | 1 =>
    if b.size < 11 then
      bad
    else if b.size != 3 + 32 * popcount16 (u16At b 1) + 8 then
      bad
    else
      return .branch (slotsAt b 1) none mem
  | 2 =>
    if b.size < 47 then
      bad
    else if b.size != 39 + 32 * popcount16 (u16At b 37) + 8 then
      bad
    else
      return .branch (slotsAt b 37) (some (.ref (refAt b 1))) mem
  | 3 =>
    let n := u32At b 1
    if b.size != 5 + n + 32 + 8 then
      bad
    else
      let (e, _) ← hpDecode (b.extract 5 (5 + n))
      return .ext e (.old ⟨b.extract (5 + n) (37 + n)⟩) mem
  | _ =>
    bad

/-- `move_node_to_mutable`: read a node, record it and drop its reference. -/
def load (h : CryptoHash) : M W := do
  if h == emptyRoot then
    return .empty
  match (← read).read h with
  | none =>
    throw s!"missing trie node {hashHex h}"
  | some bytes =>
    record h bytes
    match decodeW bytes with
    | .error e =>
      throw s!"corrupt trie node {hashHex h}: {e}"
    | .ok w =>
      subRef h 1
      return w

def ensure : W → M W
  | .old h => load h
  | w => pure w

/-- A replaced or deleted stored value is a reference removed; a new one is not counted yet. -/
def dropValue : Val → M Unit
  | .ref r => subRef r.hash 1
  | .mem _ => pure ()

/-- Insert `value` at `key[p..]` below the non-old node `n` (`generic_insert`). -/
partial def ins (n : W) (key : Nibs) (p : Nat) (value : ByteArray) : M W := do
  match n with
  | .old h =>
    ins (← load h) key p value
  | .empty =>
    return mkLeaf (slice key p key.size) (.mem value)
  | .branch cs bv mem =>
    if p == key.size then
      if let some o := bv then
        dropValue o
      let nv := some (.mem value)
      return .branch cs nv (mem - directBranch bv + directBranch nv)
    else
      let i := (key.get! p).toNat
      let c ← ensure cs[i]!
      let c' ← ins c key (p + 1) value
      return .branch (cs.set! i c') bv (mem - c.mem + c'.mem)
  | .leaf e ov _ =>
    let cm := common key p e
    if cm == e.size && cm == key.size - p then
      dropValue ov
      return mkLeaf e (.mem value)
    else if cm == 0 then
      let br :=
        if e.size == 0 then mkBranch emptySlots (some ov) 0
        else
          let leaf := mkLeaf (slice e 1 e.size) ov
          mkBranch (emptySlots.set! (e.get! 0).toNat leaf) none leaf.mem
      ins br key p value
    else
      let leaf := mkLeaf (slice e cm e.size) ov
      ins (mkExt (slice e 0 cm) leaf leaf.mem) key p value
  | .ext e child mem =>
    let cm := common key p e
    let childMem := mem - directExt e
    if cm == 0 then
      let (node, nodeMem) :=
        if e.size == 1 then (child, childMem)
        else
          let inner := mkExt (slice e 1 e.size) child childMem
          (inner, inner.mem)
      ins (mkBranch (emptySlots.set! (e.get! 0).toNat node) none nodeMem) key p value
    else if cm == e.size then
      let c ← ensure child
      let c' ← ins c key (p + cm) value
      return .ext e c' (mem - c.mem + c'.mem)
    else
      let inner := mkExt (slice e cm e.size) child childMem
      ins (mkExt (slice e 0 cm) inner inner.mem) key p value

/-- Merge an extension into its child (`extend_child`). -/
def extendChild (e : Nibs) (child : W) : M W := do
  match ← ensure child with
  | .empty =>
    return .empty
  | .leaf ce v _ =>
    return mkLeaf (e ++ ce) v
  | c@(.branch ..) =>
    return mkExt e c c.mem
  | .ext ce inner m =>
    return .ext (e ++ ce) inner (m - directExt ce + directExt (e ++ ce))
  | .old _ =>
    throw "unreachable"

/-- Restore the canonical shape of a node after a deletion below it (`squash_node`). -/
def squash : W → M W
  | .branch cs bv mem => do
    let present :=
      (List.range 16).filterMap fun i =>
        match cs[i]! with
        | .empty => none
        | c => some (i, c)
    match present, bv with
    | [], none =>
      return .empty
    | [], some v =>
      return mkLeaf ByteArray.empty v
    | [(i, c)], none =>
      extendChild (ByteArray.empty.push i.toUInt8) c
    | _, _ =>
      return .branch cs bv mem
  | .ext e c _ => extendChild e c
  | w => pure w

/-- Delete `key[p..]` below the non-old node `n` (`generic_delete`); the flag says whether the key
was there. -/
partial def del (n : W) (key : Nibs) (p : Nat) : M (W × Bool) := do
  match n with
  | .old h =>
    del (← load h) key p
  | .empty =>
    return (.empty, false)
  | .leaf e v _ =>
    if common key p e == e.size && e.size == key.size - p then
      dropValue v
      return (.empty, true)
    else
      return (n, false)
  | .branch cs bv mem =>
    if p == key.size then
      match bv with
      | none =>
        return (n, false)
      | some o =>
        dropValue o
        return (← squash (.branch cs none (mem - directBranch bv + directBranch none)), true)
    else
      let i := (key.get! p).toNat
      match cs[i]! with
      | .empty =>
        return (n, false)
      | slot =>
        let c ← ensure slot
        let (c', deleted) ← del c key (p + 1)
        if deleted then
          return (← squash (.branch (cs.set! i c') bv (mem - c.mem + c'.mem)), true)
        else
          return (.branch (cs.set! i c') bv mem, false)
  | .ext e child mem =>
    if common key p e == e.size then
      let c ← ensure child
      let (c', deleted) ← del c key (p + e.size)
      if deleted then
        return (← squash (.ext e c' (mem - c.mem + c'.mem)), true)
      else
        return (.ext e c' mem, false)
    else
      return (n, false)

private def le32 (d : ByteArray) (x : Nat) : ByteArray :=
  d.push x.toUInt8 |>.push (x >>> 8).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 24).toUInt8

private def le64 (d : ByteArray) (x : UInt64) : ByteArray :=
  (List.range 8).foldl (fun d i => d.push (x >>> (8 * i).toUInt64).toUInt8) d

private def putRef (d : ByteArray) (r : ValueRef) : ByteArray :=
  (le32 d r.length.toNat).append r.hash.bytes

/-- Write a new value or reuse a stored one (`flatten_value`). -/
def flattenValue : Val → M ValueRef
  | .ref r => pure r
  | .mem data => do
    let h := CryptoHash.hash data
    addRef h data 1
    return ⟨data.size.toUInt32, h⟩

/-- Serialize and hash the nodes bottom up, adding a reference for each (`flatten_nodes`). -/
partial def flatten : W → M CryptoHash
  | .old h => pure h
  | .empty => pure emptyRoot
  | .leaf e v mem => do
    let r ← flattenValue v
    let enc := hpEncode true e
    emit (putRef ((le32 (ByteArray.empty.push 0) enc.size).append enc) r) mem
  | .ext e c mem => do
    let ch ← flatten c
    let enc := hpEncode false e
    emit (((le32 (ByteArray.empty.push 3) enc.size).append enc).append ch.bytes) mem
  | .branch cs bv mem => do
    let mut mask : Nat := 0
    let mut hashes := ByteArray.empty
    for i in [0:16] do
      match cs[i]! with
      | .empty =>
        pure ()
      | c =>
        mask := mask ||| (1 <<< i)
        hashes := hashes.append (← flatten c).bytes
    let head ←
      match bv with
      | none =>
        pure (ByteArray.empty.push 1)
      | some v =>
        do
          pure (putRef (ByteArray.empty.push 2) (← flattenValue v))
    emit ((head.push mask.toUInt8 |>.push (mask >>> 8).toUInt8).append hashes) mem
where emit (body : ByteArray) (mem : UInt64) : M CryptoHash := do
    let bytes := le64 body mem
    let h := CryptoHash.hash bytes
    addRef h bytes 1
    return h

/-- `TrieRefcountDeltaMap::into_changes`, sorted by hash. -/
def intoChanges (d : Deltas) : Array Addition × Array Subtraction :=
  let (ins, del) :=
    d.fold
      (fun (ins, del) h (data, rc) =>
        if rc > 0 then (ins.push ⟨h, data.getD ByteArray.empty, rc.toNat.toUInt32⟩, del)
        else if rc < 0 then (ins, del.push ⟨h, (-rc).toNat.toUInt32⟩) else (ins, del))
      (#[], #[])
  let lt (a b : CryptoHash) := Borsh.compareBytes a.bytes b.bytes == .lt
  (ins.qsort fun a b => lt a.hash b.hash, del.qsort fun a b => lt a.hash b.hash)

/-- A change: write a value, or delete (`None`). -/
abbrev Change :=
  ByteArray × Option ByteArray

/-- The result of an update with the nodes it read, when recording. -/
structure Updated where
  changes : TrieChanges
  recorded : Option Recorder

/-- `Trie::update`: apply the changes in order to the trie at `root`. -/
def update (src : NodeSource) (root : CryptoHash) (changes : Array Change)
    (recorder : Option Recorder := none) : Except String Updated := do
  let run : M CryptoHash := do
    let mut node ← load root
    for (key, value) in changes do
      let k := toNibs key
      match value with
      | some v =>
        node ← ins node k 0 v
      | none =>
        node := (← del node k 0).1
    flatten node
  let (newRoot, st) ← (run.run src).run { recorder }
  let (insertions, deletions) := intoChanges st.deltas
  return ⟨⟨root, newRoot, insertions, deletions⟩, st.recorder⟩

end Near.Node.Trie
