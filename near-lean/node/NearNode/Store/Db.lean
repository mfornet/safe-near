import NearNode.Store.Tables

/-!
# A crash-safe key-value store in pure Lean

The store keeps every column in memory and makes it durable with a log and snapshots, using only
`IO.FS`:

* `log-G.bin` is append-only: one self-checking record per commit (`NearNode.Store.Format`).
* `snapshot-G.bin` is the whole content at some commit, with a checksum footer. It is written to
  `snapshot-G.bin.tmp`, flushed and renamed, so a snapshot that exists under its final name is
  complete.
* A *generation* `G` is a snapshot and the log of the commits after it. Compaction writes the
  snapshot of generation `G + 1` from memory, starts the empty `log-(G+1).bin` and removes the
  files of generation `G`.

**Recovery** (`Store.open`) takes the highest generation whose snapshot is complete (generation 0 has
none: it is the empty store, with `log-0.bin`) and replays its log record by record while the checksum holds and the sequence number is the next one. The first
record that is cut short, fails its checksum or breaks the sequence ends the log, and the file is
truncated there, so a commit is either replayed in full or not at all. Whatever else a crash left
behind (`.tmp` files, files of older generations, a missing new log) is removed or recreated.

**What a crash can do.** A commit is one `write` of one record followed by `flush`; the bytes are in
the operating system when `commit` returns, so a crash of the process loses nothing that returned.
A crash during the write leaves a partial record at the end, which recovery drops. A crash during
compaction leaves either the old generation whole (before the rename of the new snapshot) or the new
snapshot whole (after it), and the new snapshot holds every commit of the old log because it is
written from the tables after they applied it. A failed write poisons the handle (the file may end
in a partial record that later commits would hide), so nothing more is committed until the store is
reopened.

**What it cannot do.** Lean's `IO.FS` has no `fsync`: a power failure or operating system crash can
lose what only reached the page cache, and can reorder the rename before the data it names. With
`Options.sync` every commit and every snapshot is followed by the system `sync` command, which flushes
the page cache (`sync -f` of the store directory), at the price of a process per commit.
-/

namespace Near.Node.Store

structure Options where
  /-- Compact when the log grows beyond this many bytes. -/
  logLimit : Nat := 64 * 1024 * 1024
  /-- Compact by ratio as well: when the log is longer than `minLog` bytes and longer than `logPercent` percent of the
  last snapshot (the live data as of the last compaction or opening), so the files stay within a constant factor of
  the live data whatever its size. 0: only `logLimit` applies. -/
  minLog : Nat := 0
  logPercent : Nat := 100
  /-- Run `sync` after each commit and snapshot (see the module comment). -/
  sync : Bool := false

/-- What the node opens its store with: besides the 64 MiB cap, compaction when the log is above 4 MiB and as long as the last
snapshot, so that the files stay within a constant factor of the live data (the snapshot, a log of the same size at most,
and the next snapshot while it is written) however long the node runs. -/
def Options.node : Options :=
  { minLog := 4 * 1024 * 1024, logPercent := 100 }

/-- The state that changes with each commit. -/
structure Info where
  gen : Nat
  seq : UInt64
  log : IO.FS.Handle
  logSize : Nat
  /-- Bytes of the snapshot of this generation (0: generation 0 has none). -/
  snapSize : Nat := 0

structure Store where
  dir : System.FilePath
  opts : Options
  lock : IO.FS.Handle
  tables : IO.Ref Tables
  info : IO.Ref Info
  poisoned : IO.Ref Bool

/-- What `open` found. -/
structure Recovery where
  generation : Nat
  commits : Nat
  /-- Bytes of a torn tail removed from the log. -/
  tornBytes : Nat

namespace Store

private def snapshotPath (dir : System.FilePath) (g : Nat) : System.FilePath :=
  dir / s!"snapshot-{g}.bin"

private def logPath (dir : System.FilePath) (g : Nat) : System.FilePath :=
  dir / s!"log-{g}.bin"

private def flushSync (s : Store) (path : System.FilePath) : IO Unit := do
  if s.opts.sync then
    let out ← IO.Process.output { cmd := "sync", args := #["-f", path.toString] }
    if out.exitCode != 0 then
      let out ← IO.Process.output { cmd := "sync" }
      if out.exitCode != 0 then
        throw (IO.userError "sync failed")

-- Snapshots

private def snapshotMagic : ByteArray :=
  "NSNP".toUTF8

/-- Encode the entries of the tables in pieces of about 1 MiB, in the order of the file. -/
private def writeSnapshot (path : System.FilePath) (gen : Nat) (seq : UInt64) (t : Tables) :
    IO Unit := do
  let h ← IO.FS.Handle.mk path .write
  let mut crc : UInt32 := 0
  let mut count : UInt64 := 0
  let mut buf := le64 (le64 snapshotMagic gen.toUInt64) seq
  let put (buf : ByteArray) (b : ByteArray) : ByteArray := (le32 buf b.size).append b
  let spill (h : IO.FS.Handle) (crc : UInt32) (buf : ByteArray) : IO (UInt32 × ByteArray) := do
    if buf.size ≥ 1048576 then
      h.write buf
      return (crc32Update crc buf, ByteArray.empty)
    return (crc, buf)
  for c in Col.all do
    if !c.isRc then
      for (k, v) in t.plain[c.id.toNat]! do
        buf := put (put (buf.push 0 |>.push c.id) k) v
        count := count + 1
        (crc, buf) ← spill h crc buf
  for (k, (d, n)) in t.rc do
    buf := le64 (put (put (buf.push 1) k) d) (Int64.ofInt n).toUInt64
    count := count + 1
    (crc, buf) ← spill h crc buf
  h.write buf
  crc := crc32Update crc buf
  h.write (le32 (le64 (ByteArray.empty.push 0xFF) count) crc.toNat)
  h.flush

/-- Decode a complete snapshot; `none` if it is cut short or fails its checksum. -/
private def readSnapshot (path : System.FilePath) : IO (Option (Nat × UInt64 × Tables)) := do
  let d ← IO.FS.readBinFile path
  if d.size < 20 + 13 then
    return none
  let body := d.extract 0 (d.size - 13)
  let foot := d.extract (d.size - 13) d.size
  let parsed : Except String (Nat × UInt64 × Tables × UInt64) :=
    (do
          let magic ← take 4
          if magic != snapshotMagic then
            throw "bad magic"
          let gen ← u64
          let seq ← u64
          let mut t : Tables := {}
          let mut count : UInt64 := 0
          while (← get).pos < body.size do
            match ← u8 with
            | 0 =>
              let c ← col
              let k ← blob
              let v ← blob
              t := t.apply (.set c k v)
              count := count + 1
            | 1 =>
              let k ← blob
              let data ← blob
              let n ← u64
              t := { t with rc := t.rc.insert k (data, (Int64.ofUInt64 n).toInt) }
              count := count + 1
            | _ =>
              throw "bad entry"
          return (gen.toNat, seq, t, count) : P _).run'
      { data := body }
  let footer : Except String (UInt64 × UInt32) :=
    (do
          if (← u8) != 0xFF then
            throw "bad footer"
          let count ← u64
          let crc ← u32
          return (count, crc.toUInt32) : P _).run'
      { data := foot }
  match parsed, footer with
  | .ok (gen, seq, t, count), .ok (n, crc) =>
    if count == n && crc32 body == crc then
      return some (gen, seq, t)
    else
      return none
  | _, _ =>
    return none

-- Files

private def generations (dir : System.FilePath) (prefix_ : String) : IO (Array Nat) := do
  let mut out := #[]
  for e in ← dir.readDir do
    let name := e.fileName
    if name.startsWith prefix_ && name.endsWith ".bin" then
      let mid := (name.drop prefix_.length).dropEnd 4
      if let some g := mid.toString.toNat? then
        out := out.push g
  return out

private def truncateTo (path : System.FilePath) (len : Nat) : IO Unit := do
  let h ← IO.FS.Handle.mk path .readWrite
  let mut left := len
  while left > 0 do
    let chunk ← h.read (min left 1048576).toUSize
    if chunk.isEmpty then
      throw (IO.userError "log shorter than its valid prefix")
    left := left - chunk.size
  h.truncate
  h.flush

/-- Open (or create) the store in `dir`: take the lock, recover, and report what recovery did. -/
def «open» (dir : System.FilePath) (opts : Options := {}) : IO (Store × Recovery) := do
  IO.FS.createDirAll dir
  let lock ← IO.FS.Handle.mk (dir / "LOCK") .append
  if !(← lock.tryLock) then
    throw (IO.userError s!"store {dir} is in use")
  for e in ← dir.readDir do
    if e.fileName.endsWith ".tmp" then
      IO.FS.removeFile e.path
  let snaps := (← generations dir "snapshot-").qsort (· > ·)
  let mut base : Option (Nat × UInt64 × Tables) := none
  for g in snaps do
    if base.isNone then
      if let some r← readSnapshot (snapshotPath dir g) then
        if r.1 == g then
          base := some r
  -- generation 0 has no snapshot: it is the empty store, as long as its log was not removed
  if base.isNone && !snaps.isEmpty && !(← (logPath dir 0).pathExists) then
    throw (IO.userError s!"no complete snapshot in {dir}")
  let (gen, seq0, t0) := base.getD (0, 0, {})
  let mut t := t0
  let mut seq := seq0
  let mut pos := 0
  let mut commits := 0
  let mut torn := 0
  let lp := logPath dir gen
  let snapSize ←
    if base.isSome then
      pure (← (snapshotPath dir gen).metadata).byteSize.toNat
    else
      pure 0
  if ← lp.pathExists then
    let log ← IO.FS.readBinFile lp
    let mut go := true
    while go do
      match nextRecord log pos with
      | .commit s ops next =>
        if s == seq + 1 then
          t := ops.foldl Tables.apply t
          seq := s
          pos := next
          commits := commits + 1
        else
          go := false
      | .end =>
        go := false
    torn := log.size - pos
    if torn > 0 then
      truncateTo lp pos
  for g in snaps ++ (← generations dir "log-") do
    if g != gen then
      for p in [snapshotPath dir g, logPath dir g] do
        if ← p.pathExists then
          IO.FS.removeFile p
  let log ← IO.FS.Handle.mk lp .append
  let s : Store :=
    { dir, opts, lock, tables := ← IO.mkRef t, info := ← IO.mkRef ⟨gen, seq, log, pos, snapSize⟩,
      poisoned := ← IO.mkRef false }
  return (s, ⟨gen, commits, torn⟩)

/-- Read-only access to the content; do not keep it across a commit (it would force a copy). -/
def view (s : Store) : IO Tables :=
  s.tables.get

def get (s : Store) (c : Col) (k : ByteArray) : IO (Option ByteArray) := do
  return (← s.tables.get).get c k

/-- The number of the last commit. -/
def seq (s : Store) : IO UInt64 := do
  return (← s.info.get).seq

def generation (s : Store) : IO Nat := do
  return (← s.info.get).gen

/-- Where compaction stops, for tests that simulate a crash in the middle of it. -/
inductive Stage where
  /-- The snapshot is written to its `.tmp` file. -/
  | snapshotWritten
  /-- The snapshot is renamed to its final name; the old generation is still there. -/
  | snapshotPublished
  /-- The new log exists too. -/
  | logStarted
  /-- The old generation is removed. -/
  | done
  deriving BEq

/-- Write the snapshot of the next generation and switch to it, stopping after `stage`. -/
def compactUntil (s : Store) (stage : Stage) : IO Unit := do
  let m ← s.info.get
  let t ← s.tables.get
  let g := m.gen + 1
  let tmp := snapshotPath s.dir g |>.addExtension "tmp"
  writeSnapshot tmp g m.seq t
  flushSync s tmp
  if stage == .snapshotWritten then
    return
  IO.FS.rename tmp (snapshotPath s.dir g)
  flushSync s s.dir
  if stage == .snapshotPublished then
    return
  let lp := logPath s.dir g
  discard <| IO.FS.Handle.mk lp .write
  let log ← IO.FS.Handle.mk lp .append
  let snapSize := (← (snapshotPath s.dir g).metadata).byteSize.toNat
  s.info.set
      { m with
        gen := g, log, logSize := 0, snapSize }
  if stage == .logStarted then
    return
  for p in [snapshotPath s.dir m.gen, logPath s.dir m.gen] do
    if ← p.pathExists then
      IO.FS.removeFile p

def compact (s : Store) : IO Unit :=
  compactUntil s .done

/-- Commit a batch of operations atomically; returns its sequence number. -/
def commit (s : Store) (ops : Array Op) : IO UInt64 := do
  if ← s.poisoned.get then
    throw (IO.userError "a write failed; reopen the store")
  if !ops.all Tables.Op.valid then
    throw (IO.userError "operation not valid for its column")
  let m ← s.info.get
  let seq := m.seq + 1
  let entry := encodeCommit seq ops
  try
    m.log.write entry
    m.log.flush
    flushSync s (logPath s.dir m.gen)
  catch e =>
    s.poisoned.set true
    throw e
  s.tables.modify fun t => ops.foldl Tables.apply t
  s.info.set
      { m with
        seq, logSize := m.logSize + entry.size }
  let size := m.logSize + entry.size
  if
      size > s.opts.logLimit ||
        (s.opts.minLog > 0 && size > s.opts.minLog &&
          size * 100 > s.opts.logPercent * m.snapSize) then
    s.compact
  return seq

/-- Release the lock; the store must not be used afterwards. -/
def close (s : Store) : IO Unit := do
  (← s.info.get).log.flush
  s.lock.unlock

end Store

end Near.Node.Store
