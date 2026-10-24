import NodeBench.Harness
import NearNode.Store

/-!
# Trie and store benchmarks (M4)

A state of 100 000 entries in the shape of a shard's trie (accounts, access keys and contract data
under 1 000 accounts, values of 8 to 200 bytes) is built, updated in batches of 1 000 writes (70%
overwrites, 20% inserts, 10% deletes), read and iterated, and written to a store. Every result counts
keys, so `nanosPerIteration` is nanoseconds per key.
-/

namespace Near.Node.Bench.Trie

open Near.Node Near.Node.Trie Near.Node.Store

/-- SplitMix64. -/
private def mix (x : UInt64) : UInt64 :=
  let z := (x + 0x9E3779B97F4A7C15) * 0xBF58476D1CE4E5B9
  let z := (z ^^^ (z >>> 27)) * 0x94D049BB133111EB
  z ^^^ (z >>> 31)

private def account (i : Nat) : ByteArray :=
  s!"user{i}.near".toUTF8

/-- The `i`-th key: contract data of an account, with a few other columns. -/
private def keyOf (i : Nat) : ByteArray :=
  let a := account (i % 1000)
  match i % 20 with
  | 0 => (ByteArray.empty.push 0).append a
  | 1 =>
    (((ByteArray.empty.push 2).append a).push 2).append
      (ByteArray.mk ((Array.range 33).map fun j => UInt8.ofNat (j + i % 7)))
  | _ => (((ByteArray.empty.push 9).append a).push 0x2c).append s!"key-{i}".toUTF8

private def valueOf (i : Nat) (salt : UInt64) : ByteArray :=
  let n := 8 + ((mix (i.toUInt64 + salt)).toNat % 193)
  ⟨(Array.range n).map fun j => UInt8.ofNat (j + i + salt.toNat)⟩

private def genEntries (n : Nat) : Array (ByteArray × ByteArray) :=
  (Array.range n).map fun i => (keyOf i, valueOf i 0)

/-- A batch: 70% overwrites of present keys, 20% inserts of new ones, 10% deletes. -/
private def batch (n total round : Nat) : Array Change :=
  (Array.range n).map fun j =>
    let r := (mix (round.toUInt64 * 1000003 + j.toUInt64)).toNat
    let kind := r % 10
    if kind < 7 then (keyOf (r / 10 % total), some (valueOf j (round.toUInt64 + 1)))
    else
      if kind < 9 then (keyOf (total + round * n + j), some (valueOf j 7))
      else (keyOf (r / 10 % total), none)

/-- Time a pure computation. It takes the clock reading as an argument so that it cannot be
evaluated before the clock starts, and its result is checked before the clock stops so that it
cannot be evaluated after. -/
private def timedPure (f : UInt64 → Except String α) (force : α → UInt64) : IO (α × Nat) := do
  let a ← IO.monoNanosNow
  let r := f a.toUInt64
  let c :=
    match r with
    | .ok x => force x
    | .error _ => 1
  if c == 0x1234567 then
    throw (IO.userError "benchmark guard")
  let b ← IO.monoNanosNow
  match r with
  | .ok x =>
    return (x, b - a)
  | .error e =>
    throw (IO.userError e)

@[noinline]
private def insertAll (es : Array (ByteArray × ByteArray)) (_salt : UInt64) : Except String W := do
  let src : NodeSource := ⟨fun _ => none⟩
  let run : M W := do
    let mut node : W := .empty
    for (k, v) in es do
      node ← ins node (toNibs k) 0 v
    return node
  return (← (run.run src).run {}).1

@[noinline]
private def hashAll (w : W) (_salt : UInt64) : Except String CryptoHash := do
  let src : NodeSource := ⟨fun _ => none⟩
  return (← ((flatten w).run src).run {}).1

@[noinline]
private def buildAll (es : Array (ByteArray × ByteArray)) (_salt : UInt64) :
    Except String TrieChanges :=
  fromEntries es

@[noinline]
private def updateAll (src : NodeSource) (root : CryptoHash) (b : Array Change) (_salt : UInt64) :
    Except String TrieChanges := do
  return (← update src root b).changes

@[noinline]
private def applyAll (s : MemStore) (c : TrieChanges) (_salt : UInt64) : Except String MemStore :=
  s.apply c

private def timed (f : IO α) : IO (α × Nat) := do
  let a ← IO.monoNanosNow
  let x ← f
  let b ← IO.monoNanosNow
  return (x, b - a)

private def result (name : String) (keys nanos : Nat) (checksum : UInt64) : Result :=
  { name, iterations := keys, totalNanos := nanos, checksum }

def run (filter : String) : IO (Array Result) := do
  let wanted (n : String) := filter.isEmpty || (n.splitOn filter).length > 1
  let mut out : Array Result := #[]
  -- a value known only at run time, so that no step is evaluated before it is timed
  let total := 100000 + (← IO.monoNanosNow) % 1
  let es := genEntries total
  let log (r : Result) : IO Unit := IO.eprintln s!"{r.name}: {r.nanosPerIteration} ns/key"
  let emit (r : Result) (out : Array Result) : IO (Array Result) := do
    log r
    return out.push r
  -- insertion into the working trie, then hashing
  if wanted "trie/insert (no hashing)" || wanted "trie/hash the nodes" then
    let (w, t1) ← timedPure (insertAll es) (·.mem)
    out ← emit (result s!"trie/insert (no hashing), {total} keys" total t1 w.mem) out
    let (h, t2) ← timedPure (hashAll w) (·.bytes[0]!.toUInt64)
    out ←
      emit (result s!"trie/hash the nodes (root of {total} keys)" total t2 h.bytes[0]!.toUInt64) out
  -- the whole build, and the state the updates run on
  let (built, t) ← timedPure (buildAll es) (·.newRoot.bytes[0]!.toUInt64)
  out ←
    emit (result s!"trie/build root from {total} entries" total t built.newRoot.bytes[0]!.toUInt64)
        out
  let (store0, t) ← timedPure (applyAll {} built) (·.size.toUInt64)
  out ←
    emit (result s!"trie/apply the refcounts of {total} entries to an in-memory store" total t 0)
        out
  let mut store := store0
  let mut root := built.newRoot
  if wanted "trie/update" then
    let rounds := 5
    let mut nanos := 0
    let mut keys := 0
    for r in [0:rounds] do
      let b := batch 1000 total r
      let (u, t) ← timedPure (updateAll store.source root b) (·.newRoot.bytes[0]!.toUInt64)
      nanos := nanos + t
      keys := keys + b.size
      store ← IO.ofExcept (store.apply u)
      root := u.newRoot
    out ←
      emit
          (result s!"trie/update, batches of 1000 writes on {total} entries" keys nanos
            root.bytes[0]!.toUInt64)
          out
  if wanted "trie/get" then
    let n := 20000
    let (c, t) ←
      timed
          (do
            let mut c := 0
            for i in [0:n] do
              match get store.source root (keyOf (i * 5 % total)) with
              | .ok (some v, _) =>
                c := c + v.size
              | _ =>
                pure ()
            return c)
    out ← emit (result s!"trie/get" n t c.toUInt64) out
  if wanted "trie/get with recording" then
    let n := 2000
    let (c, t) ←
      timed
          (do
            let mut c := 0
            for i in [0:n] do
              match get store.source root (keyOf (i * 5 % total)) (some {}) with
              | .ok (some v, some r) =>
                c := c + v.size + r.size
              | _ =>
                pure ()
            return c)
    out ← emit (result s!"trie/get with recording" n t c.toUInt64) out
  if wanted "trie/iterate" then
    let (c, t) ←
      timed
          (do
            match Trie.entries store.source root with
            | .ok es =>
              pure es.size
            | .error _ =>
              pure 0)
    out ← emit (result s!"trie/iterate in key order" c t c.toUInt64) out
  -- the store
  if wanted "store/" then
    let dir : System.FilePath :=
      System.FilePath.mk ((← IO.getEnv "TMPDIR").getD "/tmp") /
        s!"node-bench-store-{← IO.monoNanosNow}"
    let shard := shardUIdKey 0 0
    let (s, _) ← Store.open dir { logLimit := 1 <<< 40 }
    let (_, t) ←
      timed
          (do
            discard <| s.commit (trieInsertOps shard built))
    out ←
      emit
          (result s!"store/commit the nodes of {total} entries ({built.insertions.size} nodes)"
            built.insertions.size t 0)
          out
    let mut keys := 0
    let mut nanos := 0
    let mut bytes := 0
    let mut r := built.newRoot
    for round in [0:5] do
      let b := batch 1000 total round
      let src := (← s.view).nodeSource shard
      let u ← IO.ofExcept (update src r b)
      let ops := trieInsertOps shard u.changes ++ trieDeleteOps shard u.changes
      let (_, t) ←
        timed
            (do
              discard <| s.commit ops)
      nanos := nanos + t
      keys := keys + b.size
      bytes :=
        bytes +
          (ops.foldl
            (fun n o =>
              match o with
              | .rcAdd _ k d _ => n + k.size + d.size + 12
              | _ => n)
            0)
      r := u.changes.newRoot
    out ←
      emit
          (result s!"store/commit the changes of 1000 writes ({bytes / 5000} B/key)" keys nanos
            bytes.toUInt64)
          out
    let nreads := 50000
    let t0 ← IO.monoNanosNow
    let mut c := 0
    let view ← s.view
    for i in [0:nreads] do
      let h := built.insertions[i % built.insertions.size]!.hash
      if (view.get .state (stateKey shard h)).isSome then
        c := c + 1
    let t1 ← IO.monoNanosNow
    out ← emit (result "store/read a node by hash" nreads (t1 - t0) c.toUInt64) out
    let logBytes := (← (dir / "log-0.bin").metadata).byteSize.toNat
    s.close
    let (s2, rec) ← timed (Store.open dir { logLimit := 1 <<< 40 })
    out ←
      emit
          (result s!"store/open and replay a log of {logBytes / 1048576} MiB" built.insertions.size
            rec 0)
          out
    let (_, t) ← timed (s2.1.compact)
    out ← emit (result "store/compact (write a snapshot)" built.insertions.size t 0) out
    s2.1.close
    IO.FS.removeDirAll dir
  return out

end Near.Node.Bench.Trie
