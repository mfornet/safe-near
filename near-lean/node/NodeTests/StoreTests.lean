import NearNode.Store
import NearNode.Trie
import NodeTests.Rng
import NodeTests.FlatTests

/-!
`node-store-tests [CASES [CHUNKS]]`: the persistent store.

The unit tests exercise the columns and the reference counted `State` column, the lock, a clean
restart, compaction and the recovery of every file state a crash can leave: a log cut at every
byte, a flipped byte, and a crash at each step of compaction.

With a directory of corpus cases (`tools/localnet/state_roots.py --cases-only`) the tries of the
first `CHUNKS` (default 148, all the single-shard chunks) single-shard chunks are written to the store, the pre-state of each
then the update by its `stateDiff`, with a head pointer in `BlockMisc` per chunk. The test

* restarts cleanly and rebuilds the root of every committed trie from what the store returns,
* cuts the log at random points (the process was killed in the middle of a write), reopens, and
  checks that the recovered commits are exactly those that were complete and that their roots are
  readable and identical,
* repeats the clean restart with a small log limit, so the store compacts several times.
-/

open Near.Node Near.Node.Store Near.Node.Trie

private def fail (what : String) : IO Bool := do
  IO.eprintln s!"FAIL {what}"
  return false

private def check (ok : Bool) (what : String) : IO Bool :=
  if ok then pure true else fail what

private def tempDir (name : String) : IO System.FilePath := do
  let base :=
    System.FilePath.mk ((← IO.getEnv "TMPDIR").getD "/tmp") /
      s!"node-store-tests-{← IO.monoNanosNow}-{name}"
  IO.FS.createDirAll base
  return base

private def copyDir (src dst : System.FilePath) (log : Option (System.FilePath × Nat) := none) :
    IO Unit := do
  IO.FS.createDirAll dst
  for e in ← src.readDir do
    if e.fileName != "LOCK" then
      let d ← IO.FS.readBinFile e.path
      let d :=
        match log with
        | some (name, cut) => if e.path == name then d.extract 0 cut else d
        | none => d
      IO.FS.writeBinFile (dst / e.fileName) d

private def rng (seed : Nat) : Rng :=
  ⟨(seed.toUInt64 + 1) * 0xD1B54A32D192ED03⟩

private def genBlob (maxLen : Nat) : R ByteArray := do
  let n ← below (maxLen + 1)
  let tag ← below 250
  return ⟨(Array.range n).map fun i => UInt8.ofNat (tag + i)⟩

private def plainCols : List Col :=
  [.flatState, .flatStateChanges, .flatStateDeltaMetadata, .flatStorageStatus, .blockMisc,
    .chunkExtra]

/-- A random commit: sets and deletes in the plain columns, references in `State`. -/
private def genOps : R (Array Op) := do
  let n ← below 8
  let mut ops := #[]
  for _ in [0:n] do
    let kind ← below 5
    let key : ByteArray := ByteArray.empty.push (UInt8.ofNat (← below 12))
    if kind == 0 then
      ops := ops.push (.delete plainCols[← below plainCols.length]! key)
    else if kind == 1 then
      ops := ops.push (.rcAdd .state key (← genBlob 30) (Int.ofNat (← below 3) + 1))
    else if kind == 2 then
      ops := ops.push (.rcAdd .state key ByteArray.empty (-1))
    else
      ops := ops.push (.set plainCols[← below plainCols.length]! key (← genBlob 40))
  return ops

private def model (cs : List (Array Op)) : Tables :=
  cs.foldl (fun t ops => ops.foldl Tables.apply t) {}

-- Unit tests

private def basics : IO Bool := do
  let dir ← tempDir "basics"
  let (s, r) ← Store.open dir
  let mut ok ← check (r.commits == 0 && r.tornBytes == 0) "fresh store"
  let k := "k".toUTF8
  let seq1 ← s.commit #[.set .blockMisc k "v".toUTF8, .rcAdd .state k "node".toUTF8 2]
  ok := ok && (← check (seq1 == 1) "first commit number")
  ok := ok && (← check ((← s.get .blockMisc k) == some "v".toUTF8) "set")
  ok := ok && (← check ((← s.get .state k) == some "node".toUTF8) "rc read")
  discard <| s.commit #[.rcAdd .state k ByteArray.empty (-1)]
  ok := ok && (← check ((← s.get .state k) == some "node".toUTF8) "one reference left")
  discard <| s.commit #[.rcAdd .state k ByteArray.empty (-1)]
  ok :=
    ok && (← check ((← s.get .state k).isNone && (← s.view).refcount k == 0) "no reference left")
  discard <| s.commit #[.rcAdd .state k ByteArray.empty (-1)]
  ok := ok && (← check ((← s.get .state k).isNone && (← s.view).refcount k == -1) "negative count")
  discard <| s.commit #[.rcAdd .state k "late".toUTF8 2]
  ok := ok && (← check ((← s.get .state k) == some "late".toUTF8) "added after the removal")
  discard <| s.commit #[.delete .blockMisc k]
  ok := ok && (← check ((← s.get .blockMisc k).isNone) "delete")
  let bad ←
    try
      s.commit #[.set .state k k] *> pure false
    catch _ =>
      pure true
  ok := ok && (← check bad "set on a counted column is refused")
  let second ←
    try
      let _ ← Store.open dir
      pure false
    catch _ =>
      pure true
  ok := ok && (← check second "a second open is refused while the store is open")
  s.close
  let (_, r) ← Store.open dir
  ok := ok && (← check (r.commits == 6) "restart replays every commit")
  IO.FS.removeDirAll dir
  return ok

private def restart (seed : Nat) (limit : Nat) : IO Bool := do
  let dir ← tempDir "restart"
  let commits : Array (Array Op) :=
    (do
          let mut out := #[]
          for _ in [0:40] do
            out := out.push (← genOps)
          return out : R _).run'
      (rng seed)
  let (s, _) ← Store.open dir { logLimit := limit }
  for c in commits do
    discard <| s.commit c
  let want := model commits.toList
  let mut ok ← check (Tables.equal (← s.view) want) "memory equals the model"
  let gens ← s.generation
  s.close
  let (s2, r) ← Store.open dir { logLimit := limit }
  ok :=
    ok && (← check (Tables.equal (← s2.view) want) s!"restart (limit {limit}, generation {gens})")
  ok := ok && (← check (r.generation == gens) "same generation")
  ok := ok && (← check ((← s2.seq) == 40) "same sequence number")
  s2.close
  IO.FS.removeDirAll dir
  return ok

/-- A log cut at every byte, and a flipped byte in every record. -/
private def tornLog (seed : Nat) : IO Bool := do
  let dir ← tempDir "torn"
  let commits : Array (Array Op) :=
    (do
          let mut out := #[]
          for _ in [0:8] do
            out := out.push (← genOps)
          return out : R _).run'
      (rng seed)
  let (s, _) ← Store.open dir
  for c in commits do
    discard <| s.commit c
  s.close
  let logFile := dir / "log-0.bin"
  let log ← IO.FS.readBinFile logFile
  let mut ends := #[0]
  let mut pos := 0
  let mut go := true
  while go do
    match nextRecord log pos with
    | .commit _ _ next =>
      ends := ends.push next;
      pos := next
    | .end =>
      go := false
  let mut ok ← check (ends.size == 9 && pos == log.size) "log scan"
  let work ← tempDir "torn-copy"
  for cut in [0:log.size + 1] do
    IO.FS.removeDirAll work
    copyDir dir work (some (logFile, cut))
    let (s, r) ← Store.open work
    let complete := (ends.filter (· ≤ cut)).size - 1
    let want := model (commits.toList.take complete)
    ok :=
      ok &&
        (←
          check (r.commits == complete && r.tornBytes == cut - ends[complete]!)
              s!"cut at {cut}: {r.commits} commits, torn {r.tornBytes}")
    ok := ok && (← check (Tables.equal (← s.view) want) s!"cut at {cut}: content")
    -- the store is usable: a new commit lands after the clean prefix and survives a restart
    let extra : Array Op := #[.set .blockMisc "after".toUTF8 "crash".toUTF8]
    discard <| s.commit extra
    s.close
    let (s2, r2) ← Store.open work
    ok := ok && (← check (r2.commits == complete + 1 && r2.tornBytes == 0) s!"cut at {cut}: append")
    ok :=
      ok &&
        (←
          check (Tables.equal (← s2.view) (model (commits.toList.take complete ++ [extra])))
              s!"cut at {cut}: content after append")
    s2.close
  -- a flipped byte ends the log at the record that holds it
  for i in [0:8] do
    let mut bad := log
    let at_ := (ends[i]! + ends[i + 1]!) / 2
    bad := bad.set! at_ (bad.get! at_ ^^^ 0x40)
    IO.FS.removeDirAll work
    copyDir dir work
    IO.FS.writeBinFile (work / "log-0.bin") bad
    let (s, r) ← Store.open work
    ok := ok && (← check (r.commits == i) s!"flip in record {i}: {r.commits} commits")
    ok :=
      ok &&
        (←
          check (Tables.equal (← s.view) (model (commits.toList.take i)))
              s!"flip in record {i}: content")
    s.close
  IO.FS.removeDirAll work
  IO.FS.removeDirAll dir
  return ok

/-- A crash after each step of compaction. -/
private def compactionCrash (seed : Nat) : IO Bool := do
  let mut ok := true
  for stage in [Store.Stage.snapshotWritten, .snapshotPublished, .logStarted, .done] do
    let dir ← tempDir "compact"
    let commits : Array (Array Op) :=
      (do
            let mut out := #[]
            for _ in [0:12] do
              out := out.push (← genOps)
            return out : R _).run'
        (rng seed)
    let (s, _) ← Store.open dir
    for c in commits.extract 0 6 do
      discard <| s.commit c
    s.compact
    for c in commits.extract 6 12 do
      discard <| s.commit c
    let want := model commits.toList
    s.compactUntil stage
    -- the process dies here: a copy of the directory is what the next start sees
    let work ← tempDir "compact-copy"
    copyDir dir work
    s.close
    let (s2, r) ← Store.open work
    ok := ok && (← check (Tables.equal (← s2.view) want && (← s2.seq) == 12) "compaction crash")
    let names := (← work.readDir).map (·.fileName) |>.qsort (· < ·)
    ok := ok && (← check (names.contains "LOCK" && !(names.any (·.endsWith ".tmp"))) "no leftovers")
    ok :=
      ok &&
        (← check ((names.filter fun n => n.startsWith "snapshot-").size == 1) "one snapshot left")
    IO.eprintln
        s!"  crash after {if stage == .snapshotWritten then "snapshotWritten" else if stage == .snapshotPublished then "snapshotPublished" else if stage == .logStarted then "logStarted" else "done"}: generation {r.generation}, {r.commits} commits replayed"
    s2.close
    IO.FS.removeDirAll work
    IO.FS.removeDirAll dir
  -- a snapshot of the new generation that is cut short is ignored while the old one is there
  let dir ← tempDir "compact-bad"
  let commits : Array (Array Op) :=
    (do
          let mut out := #[]
          for _ in [0:6] do
            out := out.push (← genOps)
          return out : R _).run'
      (rng seed)
  let (s, _) ← Store.open dir
  for c in commits do
    discard <| s.commit c
  s.compactUntil .snapshotPublished
  s.close
  let snap := dir / "snapshot-1.bin"
  let d ← IO.FS.readBinFile snap
  IO.FS.writeBinFile snap (d.extract 0 (d.size - 5))
  let (s, r) ← Store.open dir
  ok :=
    ok &&
      (←
        check (r.generation == 0 && Tables.equal (← s.view) (model commits.toList))
            "a cut snapshot falls back to the previous generation")
  s.close
  IO.FS.removeDirAll dir
  return ok

/-- The ratio rule: the same keys are overwritten for ever (the live data stays at 200 values of 100 bytes). Without it the
log grows with the number of commits; with it the files stay within a constant factor of the live data, the store
compacts several times, and a restart finds the same content. -/
private def ratioCompaction : IO Bool := do
  let dir ← tempDir "ratio"
  let fileBytes (d : System.FilePath) : IO Nat := do
    let mut n := 0
    for e in ← d.readDir do
      if e.fileName != "LOCK" then
        n := n + (← e.path.metadata).byteSize.toNat
    return n
  let write (s : Store) (round : Nat) : IO Unit := do
    let ops := (Array.range 20).map fun i =>
      Op.set .blockMisc s!"key{(round * 7 + i) % 200}".toUTF8 ⟨Array.replicate 100 (UInt8.ofNat round)⟩
    discard <| s.commit ops
  -- without the rule
  let (plain, _) ← Store.open (dir / "plain")
  for r in [0:3000] do
    write plain r
  let plainBytes ← fileBytes (dir / "plain")
  plain.close
  -- with it
  let opts : Options := { minLog := 20000, logPercent := 100 }
  let (s, _) ← Store.open (dir / "ratio") opts
  let mut worst := 0
  for r in [0:3000] do
    write s r
    if r % 50 == 0 then
      worst := max worst (← fileBytes (dir / "ratio"))
  let gens ← s.generation
  let want ← s.view
  s.close
  let (s2, r) ← Store.open (dir / "ratio") opts
  let mut ok ← check (Tables.equal (← s2.view) want) "ratio: restart content"
  ok := ok && (← check (r.generation == gens) "ratio: same generation")
  -- live data is 200 * (100 + 6) bytes: the files stay below about 3 times it plus the minimum log
  ok := ok && (← check (gens ≥ 5) s!"ratio: compacted {gens} times")
  ok := ok && (← check (worst < 3 * 22000 + 2 * 20000) s!"ratio: files at most {worst} bytes")
  ok := ok && (← check (plainBytes > 5 * worst) s!"ratio: without the rule {plainBytes} bytes against {worst}")
  s2.close
  IO.FS.removeDirAll dir
  return ok

-- Corpus

/-- The pre-state entries and root, the diff and the post-state root of a case file. -/
private def parseCase :
    Store.P (CryptoHash × Array (ByteArray × ByteArray) × Array Change × CryptoHash) := do
  if (← take 4) != "NSR1".toUTF8 then
    throw "not a case file"
  let preRoot ← take 32
  let n ← u32
  let mut pre := #[]
  for _ in [0:n] do
    let k ← blob
    pre := pre.push (k, ← blob)
  let m ← u32
  let mut diff : Array Change := #[]
  for _ in [0:m] do
    let k ← blob
    if (← take 1).get! 0 == 1 then
      diff := diff.push (k, some (← blob))
    else
      diff := diff.push (k, none)
  let postRoot ← take 32
  return (⟨preRoot⟩, pre, diff, ⟨postRoot⟩)

/-- Rebuild the root of the trie at `root` from what the store returns for it. -/
private def rebuild (t : Tables) (shard : ByteArray) (root : CryptoHash) : Except String Unit := do
  let src := t.nodeSource shard
  let refs ← entries src root
  let mut es := #[]
  for (k, r) in refs do
    match src.read r.hash with
    | some v =>
      es := es.push (k, v)
    | none =>
      throw s!"value of key {k.size} bytes missing"
  let c ← fromEntries es
  if c.newRoot != root then
    throw s!"rebuilt root differs ({es.size} entries)"

private structure Commit where
  seq : UInt64
  /-- The root the commit made current; none for garbage collection. -/
  head : Option CryptoHash
  /-- The post-state roots committed so far: garbage collection never removes them. -/
  posts : Array CryptoHash
  /-- The number of entries of the `State` column after it. -/
  counted : Nat
  deriving Inhabited

private def headKey : ByteArray :=
  "HEAD".toUTF8

private def le64 (x : UInt64) : ByteArray :=
  (List.range 8).foldl (fun d i => d.push (x >>> (8 * i).toUInt64).toUInt8) ByteArray.empty

/-- The head pointer: the commit number and the root that commit made current. -/
private def headValue (seq : UInt64) (root : CryptoHash) : ByteArray :=
  le64 seq ++ root.bytes

private abbrev Case :=
  CryptoHash × Array (ByteArray × ByteArray) × Array Change × CryptoHash

private def applyDiff (pre : Array (ByteArray × ByteArray)) (diff : Array Change) :
    Array (ByteArray × ByteArray) :=
  let m : Std.HashMap ByteArray ByteArray := pre.foldl (fun m (k, v) => m.insert k v) {}
  (diff.foldl
      (fun m (k, v) =>
        match v with
        | some v => m.insert k v
        | none => m.erase k)
      m).toArray

/-- For each case three commits: its pre-state trie imported, its update by the `stateDiff` (the new
nodes added, as when a chunk is applied), and later the garbage collection of the update (the
replaced nodes released). Returns the commits and the references the `State` column must hold at the
end: those of the post-state tries. -/
private def corpusWrite (s : Store) (shard : ByteArray) (cases : Array Case) :
    IO (Array Commit × Std.HashMap ByteArray Int) := do
  let mut out := #[]
  let mut posts : Array CryptoHash := #[]
  let mut collect : Array (Array Op) := #[]
  let mut expected : Std.HashMap ByteArray Int := {}
  for (preRoot, pre, diff, postRoot) in cases do
    let built ← IO.ofExcept (fromEntries pre)
    if built.newRoot != preRoot then
      throw (IO.userError "pre-state root differs")
    let n := (← s.seq) + 1
    discard <|
        s.commit (trieInsertOps shard built ++ #[.set .blockMisc headKey (headValue n preRoot)])
    out := out.push ⟨n, some preRoot, posts, (← s.view).rc.size⟩
    let upd ← IO.ofExcept (update ((← s.view).nodeSource shard) preRoot diff)
    if upd.changes.newRoot != postRoot then
      throw (IO.userError "post-state root differs")
    let n := (← s.seq) + 1
    posts := posts.push postRoot
    discard <|
        s.commit
          (trieInsertOps shard upd.changes ++ #[.set .blockMisc headKey (headValue n postRoot)])
    out := out.push ⟨n, some postRoot, posts, (← s.view).rc.size⟩
    collect := collect.push (trieDeleteOps shard upd.changes)
    let scratch ← IO.ofExcept (fromEntries (applyDiff pre diff))
    for a in scratch.insertions do
      let k := stateKey shard a.hash
      expected := expected.insert k (expected.getD k 0 + a.rc.toNat)
  for ops in collect do
    let n := (← s.seq) + 1
    discard <| s.commit (ops ++ #[.set .blockMisc headKey (headValue n posts.back!)])
    out := out.push ⟨n, none, posts, (← s.view).rc.size⟩
  return (out, expected)

/-- After a restart at commit `q`: the head, the size of the column and the tries are those the
writer had at `q`. `all` rebuilds every root that must be readable, otherwise the head and two
post-state roots. -/
private def verify (what : String) (s : Store) (shard : ByteArray) (commits : Array Commit)
    (all : Bool) (seed : Nat) : IO Bool := do
  let q := (← s.seq).toNat
  if q == 0 then
    return ← check ((← s.view).size .state == 0) s!"{what}: nothing recovered"
  let some c := commits[q - 1]? | fail s!"{what}: recovered commit {q}, which was never written"
  let t ← s.view
  let mut ok ← check (c.seq.toNat == q) s!"{what}: commit numbers"
  let headRoot := c.head.getD c.posts.back!
  ok :=
    ok &&
      (←
        check (t.get .blockMisc headKey == some (headValue c.seq headRoot))
            s!"{what}: head pointer")
  ok := ok && (← check (t.rc.size == c.counted) s!"{what}: number of stored nodes")
  let roots :=
    if all then c.posts ++ (c.head.toArray)
    else
      let p := c.posts
      (if p.isEmpty then #[] else #[p[seed % p.size]!, p[(seed / 7) % p.size]!]) ++ c.head.toArray
  for r in roots do
    match rebuild t shard r with
    | .ok _ =>
      pure ()
    | .error e =>
      ok := false
      IO.eprintln s!"FAIL {what}: a trie committed by {q} is unreadable: {e}"
  return ok

private def fileSize (p : System.FilePath) : IO Nat := do
  return (← p.metadata).byteSize.toNat

private def corpusTests (dir : System.FilePath) (count : Nat) : IO Bool := do
  let mut files := #[]
  for e in ← dir.readDir do
    if e.fileName.startsWith "single-" && e.path.extension == some "case" then
      files := files.push e.path
  files := (files.qsort fun a b => a.toString < b.toString).extract 0 count
  let mut cases : Array Case := #[]
  for f in files do
    cases := cases.push (← IO.ofExcept ((parseCase.run' { data := ← IO.FS.readBinFile f })))
  let shard := shardUIdKey 0 0
  let mut flatOk := true
  let mut inlined := 0
  let mut refs := 0
  for i in [0:min 12 cases.size] do
    let (preRoot, pre, diff, postRoot) := cases[i]!
    let (good, a, b) ← FlatTests.corpusChunk (files[i]!.fileStem.getD "?") preRoot postRoot pre diff
    flatOk := flatOk && good
    inlined := inlined + a
    refs := refs + b
  IO.println
      s!"  flat storage on {min 12 cases.size} chunks: {if flatOk then "ok" else "FAILED"} ({inlined} inlined values, {refs} references)"
  let work ← tempDir "corpus"
  let started ← IO.monoMsNow
  let (s, _) ← Store.open (work / "a") { logLimit := 1 <<< 40 }
  let (commits, expected) ← corpusWrite s shard cases
  let total := (← s.seq).toNat
  s.close
  let logFile := work / "a" / "log-0.bin"
  let logSize ← fileSize logFile
  IO.println
      s!"  {cases.size} chunks, {total} commits, log {logSize / 1024} KiB, written in {(← IO.monoMsNow) - started} ms"
  -- clean restart
  let mut ok := flatOk
  let t0 ← IO.monoMsNow
  let (s, r) ← Store.open (work / "a")
  ok :=
    ok && (← check (r.commits == total && r.tornBytes == 0) "clean restart replays every commit")
  ok := ok && (← verify "clean restart" s shard commits true 0)
  let t ← s.view
  ok :=
    ok &&
      (←
        check
            (t.rc.size == expected.size && expected.fold (fun b k n => b && t.refcount k == n) true)
            "after garbage collection the references are those of the post-state tries")
  s.close
  IO.println
      s!"  clean restart: {r.commits} commits replayed and every root rebuilt in {(← IO.monoMsNow) - t0} ms"
  -- killed in the middle of a write: the log cut at random points
  let log ← IO.FS.readBinFile logFile
  let mut ends := #[0]
  let mut pos := 0
  let mut go := true
  while go do
    match nextRecord log pos with
    | .commit _ _ next =>
      ends := ends.push next;
      pos := next
    | .end =>
      go := false
  ok := ok && (← check (ends.size == total + 1 && pos == log.size) "log scan")
  let mut cuts : Array Nat := #[0, log.size, log.size - 1]
  let mut g := rng 7
  for _ in [0:14] do
    let (x, g') := g.below (log.size + 1)
    g := g'
    cuts := cuts.push x
  for _ in [0:4] do
    let (i, g') := g.below total
    g := g'
    cuts := cuts ++ #[ends[i + 1]! - 1, ends[i + 1]!, ends[i + 1]! + 1]
  let mut cutOk := 0
  for cut in cuts do
    let copy := work / "cut"
    if ← copy.pathExists then
      IO.FS.removeDirAll copy
    copyDir (work / "a") copy (some (logFile, cut))
    let (s, r) ← Store.open copy
    let complete := (ends.filter (· ≤ cut)).size - 1
    let good ←
      check (r.commits == complete && r.tornBytes == cut - ends[complete]!)
          s!"cut at {cut}: recovered {r.commits} commits, expected {complete}"
    let good := good && (← verify s!"cut at {cut}" s shard commits false cut)
    if good then
      cutOk := cutOk + 1
    ok := ok && good
    s.close
  IO.println
      s!"  {cutOk}/{cuts.size} cut points recovered the exact committed prefix with readable, identical roots"
  -- compaction while writing, then a restart
  let (s, _) ← Store.open (work / "b") { logLimit := logSize / 5 }
  let (commits2, _) ← corpusWrite s shard cases
  let gens ← s.generation
  s.close
  let (s, r) ← Store.open (work / "b") { logLimit := logSize / 5 }
  ok := ok && (← check (r.generation == gens && gens ≥ 3) s!"compacted {gens} times")
  ok := ok && (← verify s!"restart after {gens} compactions" s shard commits2 true 0)
  s.close
  IO.println s!"  {gens} compactions while writing; restart reads every root"
  IO.FS.removeDirAll work
  return ok

def main (args : List String) : IO UInt32 := do
  let mut ok := true
  ok := ok && (← basics)
  IO.println "basics: done"
  for seed in [0:6] do
    ok := ok && (← restart seed (1 <<< 30))
    ok := ok && (← restart seed 300)
  IO.println "restart, with and without compaction: done"
  for seed in [0:3] do
    ok := ok && (← tornLog seed)
  IO.println "log cut at every byte, flipped byte in every record: done"
  ok := ok && (← compactionCrash 5)
  IO.println "crash in compaction: done"
  ok := ok && (← ratioCompaction)
  IO.println "compaction by ratio of log to live data: done"
  for seed in [0:40] do
    ok := ok && (← FlatTests.model seed)
  IO.println "flat storage against a model of forked chains: done"
  if let some dir := args.head? then
    let count := (args[1]? >>= String.toNat?).getD 148
    IO.println s!"corpus store test on {dir}"
    ok := ok && (← corpusTests dir count)
  IO.println (if ok then "store tests passed" else "store tests FAILED")
  return if ok then 0 else 1
