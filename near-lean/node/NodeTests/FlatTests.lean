import NearNode.Store
import NodeTests.Rng

/-!
Flat storage tests (`node-store-tests`): lookups at the blocks of random forked chains against a
model that applies the changes along the ancestry, across head moves and a restart; and, on the
corpus, the flat state of a chunk's pre-state, the delta of its `stateDiff`, and the head move.
-/

open Near.Node Near.Node.Store Near.Node.Trie Near.Node.Borsh

namespace FlatTests

structure Chain where
  blocks : Array FlatBlockInfo
  /-- Index of the parent of each block (block 0 is the genesis). -/
  parent : Array Nat
  changes : Array (Array (ByteArray × Option ByteArray))

def blockHash (i : Nat) : CryptoHash :=
  CryptoHash.hash ("block".toUTF8 ++ ByteArray.mk #[i.toUInt8, (i >>> 8).toUInt8])

def keyUniverse : Array ByteArray :=
  (Array.range 12).map fun i => ByteArray.mk #[i.toUInt8, 1, 2]

def genValue : R ByteArray := do
  let kind ← below 10
  let n ← below 40
  let extra ← below 3
  let len := if kind == 0 then 4000 + extra else if kind == 1 then 3999 else n
  return ⟨(Array.range len).map fun i => UInt8.ofNat (i + kind)⟩

def genChain (n : Nat) : R Chain := do
  let mut blocks := #[(⟨blockHash 0, 100, CryptoHash.zero⟩ : FlatBlockInfo)]
  let mut parent := #[0]
  let mut changes := #[(#[] : Array (ByteArray × Option ByteArray))]
  for i in [1:n] do
    let back ← below 4
    let p := i - 1 - min back (i - 1)
    let count ← below 4
    let mut cs : Array (ByteArray × Option ByteArray) := #[]
    for _ in [0:count] do
      let k := keyUniverse[← below keyUniverse.size]!
      cs := cs.filter (·.1 != k)
      let del ← below 3
      let v ← genValue
      cs := cs.push (k, if del == 0 then none else some v)
    blocks := blocks.push ⟨blockHash i, 100 + i.toUInt64, blocks[p]!.hash⟩
    parent := parent.push p
    changes := changes.push cs
  return ⟨blocks, parent, changes⟩

/-- The state at block `i`: the genesis state with the changes along the ancestry applied. -/
def stateAt (c : Chain) (genesis : Std.HashMap ByteArray ByteArray) (i : Nat) :
    Std.HashMap ByteArray ByteArray :=
  Id.run do
    let mut path := #[]
    let mut cur := i
    for _ in [0:c.blocks.size] do
      if cur == 0 then
        break
      path := path.push cur
      cur := c.parent[cur]!
    let mut m := genesis
    for b in path.reverse do
      for (k, v) in c.changes[b]! do
        m :=
          match v with
          | some v => m.insert k v
          | none => m.erase k
    return m

def isAncestor (c : Chain) (a b : Nat) : Bool :=
  Id.run do
    let mut x := b
    for _ in [0:c.blocks.size] do
      if x == a then
        return true
      if x == 0 then
        return false
      x := c.parent[x]!
    return false

def check (ok : Bool) (what : String) (seed : Nat) : IO Bool := do
  if !ok then
    IO.eprintln s!"FAIL flat storage {what} (case {seed})"
  return ok

def lookupsAgree (fs : FlatStorage) (t : Tables) (shard : ByteArray) (c : Chain)
    (genesis : Std.HashMap ByteArray ByteArray) (i : Nat) (seed : Nat) : IO Bool := do
  let model := stateAt c genesis i
  let mut ok := true
  for k in keyUniverse do
    let v := fs.getValue t c.blocks[i]!.hash k
    let got :=
      match v with
      | .ok (some v) => FlatStorage.deref t shard v
      | _ => none
    ok :=
      ok &&
        (←
          check
              (match v with
              | .ok _ => true
              | .error _ => false)
              s!"lookup at block {i} failed" seed)
    ok := ok && (← check (got == model.get? k) s!"value of key {k.get! 0} at block {i}" seed)
    ok :=
      ok &&
        (←
          check ((fs.containsKey t c.blocks[i]!.hash k).toOption == some (model.contains k))
              s!"contains key {k.get! 0} at block {i}" seed)
  return ok

/-- Values that the flat state keeps by reference are in the `State` column. -/
def valueOps (shard : ByteArray) (m : Array ByteArray) : Array Op :=
  m.map fun v => Op.rcAdd .state (Store.stateKey shard (CryptoHash.hash v)) v 1

def model (seed : Nat) : IO Bool := do
  let dir := System.FilePath.mk ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"flat-{← IO.monoNanosNow}"
  let shard := shardUIdKey 0 3
  let ((chain, genesisEntries), _) :=
    (do
          let c ← genChain 24
          let mut g := #[]
          for k in keyUniverse.extract 0 6 do
            g := g.push (k, ← genValue)
          return (c, g) : R _).run
      (⟨(seed.toUInt64 + 1) * 0x9E3779B97F4A7C15⟩ : Rng)
  let genesis : Std.HashMap ByteArray ByteArray :=
    genesisEntries.foldl (fun m (k, v) => m.insert k v) {}
  let (s, _) ← Store.open dir
  let mut ok := true
  -- the values that deltas reference are in the trie's column, as the chunk application wrote them
  let allValues :=
    chain.changes.foldl
      (fun acc cs =>
        cs.foldl
          (fun acc (_, v) =>
            match v with
            | some v => acc.push v
            | none => acc)
          acc)
      #[]
  discard <|
      s.commit
        (valueOps shard (allValues ++ genesisEntries.map (·.2)) ++
          FlatStorage.initOps shard chain.blocks[0]! genesisEntries)
  let mut fs ← IO.ofExcept ((FlatStorage.load (← s.view) shard).mapError toString)
  let mut head := 0
  for i in [1:chain.blocks.size] do
    let flat := FlatStorage.changesOfRaw chain.changes[i]!
    -- the parent may have been dropped by a head move; then the block cannot be added
    let supported :=
      fs.deltas.contains chain.blocks[i]!.prevHash || chain.blocks[i]!.prevHash == fs.flatHead.hash
    let md := fs.deltaMetadata chain.blocks[i]! flat
    match fs.addDelta md flat with
    | .error e =>
      ok :=
        ok &&
          (←
            check (!supported && e == .blockNotSupported fs.flatHead.hash chain.blocks[i]!.hash)
                s!"adding block {i}" seed)
    | .ok (fs', ops) =>
      ok := ok && (← check supported s!"block {i} added without a parent" seed)
      discard <| s.commit ops
      fs := fs'
      for j in [0:i + 1] do
        if (fs.blocksToHead chain.blocks[j]!.hash).toOption.isSome && isAncestor chain head j then
          ok := ok && (← lookupsAgree fs (← s.view) shard chain genesis j seed)
    -- sometimes move the head to an ancestor of the newest block
    if i % 5 == 0 then
      let candidates :=
        (List.range (i + 1)).filter fun j =>
          j > head && isAncestor chain head j && fs.deltas.contains chain.blocks[j]!.hash
      match candidates.getLast? with
      | none =>
        pure ()
      | some _ =>
        let target := candidates[candidates.length / 2]!
        let (fs', ops) ←
          IO.ofExcept ((fs.updateFlatHead (← s.view) chain.blocks[target]!.hash).mapError toString)
        discard <| s.commit ops
        fs := fs'
        head := target
        ok := ok && (← check (fs.flatHead == chain.blocks[target]!) "head moved" seed)
        -- the stored genesis of the model moves with the head
        ok :=
          ok &&
            (←
              check
                  (fs.deltas.fold
                    (fun b _ d => b && d.metadata.block.height > chain.blocks[target]!.height) true)
                  "deltas at or below the head dropped" seed)
  -- unknown blocks are not supported
  ok :=
    ok &&
      (←
        check
            (match fs.getValue (← s.view) (blockHash 999) keyUniverse[0]! with
            | .error e => e == .blockNotSupported fs.flatHead.hash (blockHash 999)
            | .ok _ => false)
            "unknown block" seed)
  -- a restart finds the same head and deltas
  s.close
  let (s2, _) ← Store.open dir
  let fs2 ← IO.ofExcept ((FlatStorage.load (← s2.view) shard).mapError toString)
  ok :=
    ok &&
      (←
        check
            (fs2.flatHead == fs.flatHead && fs2.deltas.size == fs.deltas.size &&
              fs.deltas.fold
                (fun b h d =>
                  b &&
                    (fs2.deltas.get? h).any fun d' =>
                      d'.metadata == d.metadata && d'.changes.size == d.changes.size)
                true)
            "restart" seed)
  for j in [0:chain.blocks.size] do
    if (fs2.blocksToHead chain.blocks[j]!.hash).toOption.isSome && isAncestor chain head j then
      ok := ok && (← lookupsAgree fs2 (← s2.view) shard chain genesis j seed)
  s2.close
  IO.FS.removeDirAll dir
  return ok

/-- The flat state of a corpus chunk: the pre-state, the delta of the `stateDiff`, the head move. -/
def corpusChunk (name : String) (preRoot postRoot : CryptoHash)
    (pre : Array (ByteArray × ByteArray)) (diff : Array Change) : IO (Bool × Nat × Nat) := do
  let dir :=
    System.FilePath.mk ((← IO.getEnv "TMPDIR").getD "/tmp") / s!"flat-corpus-{← IO.monoNanosNow}"
  let shard := shardUIdKey 0 0
  let b0 : FlatBlockInfo := ⟨blockHash 1000, 500, blockHash 999⟩
  let b1 : FlatBlockInfo := ⟨blockHash 1001, 501, b0.hash⟩
  let (s, _) ← Store.open dir
  let built ← IO.ofExcept (fromEntries pre)
  discard <| s.commit (trieInsertOps shard built ++ FlatStorage.initOps shard b0 pre)
  let mut fs ← IO.ofExcept ((FlatStorage.load (← s.view) shard).mapError toString)
  let upd ← IO.ofExcept (update ((← s.view).nodeSource shard) preRoot diff)
  discard <| s.commit (trieInsertOps shard upd.changes)
  let flat := FlatStorage.changesOfRaw diff
  let (fs', ops) ← IO.ofExcept ((fs.addDelta (fs.deltaMetadata b1 flat) flat).mapError toString)
  discard <| s.commit ops
  fs := fs'
  let postEntries :=
    (pre.foldl (fun (m : Std.HashMap ByteArray ByteArray) (k, v) => m.insert k v) {} |> fun m =>
      diff.foldl
        (fun m (k, v) =>
          match v with
          | some v => m.insert k v
          | none => m.erase k)
        m)
  let preMap := pre.foldl (fun (m : Std.HashMap ByteArray ByteArray) (k, v) => m.insert k v) {}
  let t ← s.view
  let mut ok := true
  let bad (what : String) : IO Bool := do
    IO.eprintln s!"FAIL {name}: flat storage {what}"
    return false
  let keys := (pre.map (·.1)) ++ (diff.map (·.1))
  for k in keys do
    let at0 := (fs.getValue t b0.hash k).toOption.bind id |>.bind (FlatStorage.deref t shard)
    let at1 := (fs.getValue t b1.hash k).toOption.bind id |>.bind (FlatStorage.deref t shard)
    let inTrie := (get (t.nodeSource shard) postRoot k).toOption.bind (·.1)
    if at0 != preMap.get? k then
      ok := ok && (← bad "value at the head block")
    if at1 != postEntries.get? k then
      ok := ok && (← bad "value at the child block")
    if inTrie != postEntries.get? k then
      ok := ok && (← bad "trie lookup disagrees with the post-state")
    if (fs.containsKey t b1.hash k).toOption != some (postEntries.contains k) then
      ok := ok && (← bad "contains_key at the child block")
  -- move the head and compare the whole flat state
  let (fs2, ops2) ← IO.ofExcept ((fs.updateFlatHead t b1.hash).mapError toString)
  discard <| s.commit ops2
  let t ← s.view
  ok := ok && (fs2.flatHead == b1 && fs2.deltas.isEmpty)
  let mut inlined := 0
  let mut refs := 0
  let mut seen := 0
  for (k, v) in t.plain[Col.flatState.id.toNat]! do
    seen := seen + 1
    let key := k.extract 8 k.size
    match Codec.decodeAll (α := FlatStateValue) v with
    | .ok fv =>
      match fv with
      | .inlined x =>
        inlined := inlined + 1;
        if x.size > FlatStateValue.inlineThreshold then
          ok := ok && (← bad "inlined a large value")
      | .ref r =>
        refs := refs + 1;
        if r.length.toNat ≤ FlatStateValue.inlineThreshold then
          ok := ok && (← bad "referenced a small value")
      if FlatStorage.deref t shard fv != postEntries.get? key then
        ok := ok && (← bad "flat state differs from the post-state")
    | .error _ =>
      ok := ok && (← bad "undecodable flat state value")
  if seen != postEntries.size then
    ok := ok && (← bad s!"has {seen} entries, the post-state {postEntries.size}")
  s.close
  IO.FS.removeDirAll dir
  return (ok, inlined, refs)

end FlatTests
