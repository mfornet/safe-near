import NearNode.Trie

/-!
`node-state-roots DIR`: the state roots of the M3 corpus through the trie `Impl`.

`DIR` holds one `<chunk>.case` per corpus chunk (written by `tools/localnet/state_roots.py`):
the complete raw pre-state entries and their root, the `stateDiff` of the chunk and the post-state
root nearcore recorded, and optionally the complete post-state of the Lean runtime's replay. For
each chunk this checks that

1. the trie built from the pre-state entries has the recorded pre-state root,
2. the `stateDiff` applied with `Trie.update` gives the recorded post-state root, and the node
   store after the update is the store of the post-state entries built from scratch (every
   reference count),
3. the post-state of the Lean replay, built from scratch, has the post-state root, and applied as
   a diff to the pre-state trie through `update` it gives that root again,
4. on chunks small enough for the specification's list-based SHA-256, the specification's root of
   the pre-state and post-state is the same.

The case format is little-endian: `"NSR1"`, pre root (32), entries, diff (key, flag, value if the
flag is 1), post root (32), a flag, entries when the flag is 1; an entry list is a `u32` count of
`(u32 key length, key, u32 value length, value)`.
-/

open Near.Node Near.Node.Trie Near.Node.Borsh

private structure Reader where
  data : ByteArray
  pos : Nat := 0

private abbrev P :=
  StateT Reader (Except String)

private def take (n : Nat) : P ByteArray := do
  let r ← get
  if r.pos + n > r.data.size then
    throw "truncated case"
  set { r with pos := r.pos + n }
  return r.data.extract r.pos (r.pos + n)

private def u32 : P Nat := do
  let b ← take 4
  return (b.get! 0).toNat ||| (b.get! 1).toNat <<< 8 ||| (b.get! 2).toNat <<< 16 |||
      (b.get! 3).toNat <<< 24

private def blob : P ByteArray := do
  take (← u32)

private def entries : P (Array (ByteArray × ByteArray)) := do
  let n ← u32
  let mut out := Array.mkEmpty n
  for _ in [0:n] do
    let k ← blob
    let v ← blob
    out := out.push (k, v)
  return out

private structure Case where
  preRoot : CryptoHash
  pre : Array (ByteArray × ByteArray)
  diff : Array Change
  postRoot : CryptoHash
  replayed : Option (Array (ByteArray × ByteArray))

private def parseCase : P Case := do
  if (← take 4) != "NSR1".toUTF8 then
    throw "not a case file"
  let preRoot ← take 32
  let pre ← entries
  let n ← u32
  let mut diff := Array.mkEmpty n
  for _ in [0:n] do
    let k ← blob
    if (← take 1).get! 0 == 1 then
      diff := diff.push (k, some (← blob))
    else
      diff := diff.push (k, none)
  let postRoot ← take 32
  let replayed ←
    if (← take 1).get! 0 == 1 then
      some <$> entries
    else
      pure none
  return { preRoot := ⟨preRoot⟩, pre, diff, postRoot := ⟨postRoot⟩, replayed }

private def applyDiff (m : Std.HashMap ByteArray ByteArray) (diff : Array Change) :
    Std.HashMap ByteArray ByteArray :=
  diff.foldl
    (fun m (k, v) =>
      match v with
      | some v => m.insert k v
      | none => m.erase k)
    m

/-- The changes that turn the entries `a` into the entries `b`. -/
private def diffOf (a b : Array (ByteArray × ByteArray)) : Array Change :=
  Id.run do
    let am : Std.HashMap ByteArray ByteArray := a.foldl (fun m (k, v) => m.insert k v) {}
    let bm : Std.HashMap ByteArray ByteArray := b.foldl (fun m (k, v) => m.insert k v) {}
    let mut out : Array Change := #[]
    for (k, v) in b do
      if am.get? k != some v then
        out := out.push (k, some v)
    for (k, _) in a do
      if !bm.contains k then
        out := out.push (k, none)
    return out

private def storeEq (a b : MemStore) : Bool :=
  a.map.size == b.map.size &&
    a.map.fold
      (fun ok h (d, rc) => ok && (b.map.get? h |>.any fun (d', rc') => d == d' && rc == rc')) true

private structure Totals where
  chunks : Nat := 0
  pre : Nat := 0
  post : Nat := 0
  refcounts : Nat := 0
  replayed : Nat := 0
  replayedDiff : Nat := 0
  replayedCount : Nat := 0
  spec : Nat := 0
  specChecked : Nat := 0
  keys : Nat := 0
  seconds : Float := 0

private def specLimit : Nat :=
  150000

private def one (name : String) (c : Case) (t : Totals) : IO Totals := do
  let mut t := { t with chunks := t.chunks + 1 }
  let started ← IO.monoNanosNow
  let ok (what : String) (b : Bool) : IO Bool := do
    if !b then
      IO.eprintln s!"FAIL {name}: {what}"
    return b
  let built ← IO.ofExcept (fromEntries c.pre)
  let mut store ← IO.ofExcept ((MemStore.mk {}).apply built)
  if ← ok "pre-state root" (built.newRoot == c.preRoot) then
    t := { t with pre := t.pre + 1 }
  let upd ← IO.ofExcept (update store.source c.preRoot c.diff)
  let after ← IO.ofExcept (store.apply upd.changes)
  if ← ok "post-state root from the stateDiff" (upd.changes.newRoot == c.postRoot) then
    t := { t with post := t.post + 1 }
  let postEntries := (applyDiff (c.pre.foldl (fun m (k, v) => m.insert k v) {}) c.diff).toArray
  let scratch ← IO.ofExcept (fromEntries postEntries)
  let scratchStore ← IO.ofExcept ((MemStore.mk {}).apply scratch)
  if
      ←
        ok "reference counts after the update"
            (scratch.newRoot == c.postRoot && storeEq after scratchStore) then
    t := { t with refcounts := t.refcounts + 1 }
  if let some lean := c.replayed then
    t := { t with replayedCount := t.replayedCount + 1 }
    let b ← IO.ofExcept (fromEntries lean)
    if ← ok "post-state root of the Lean replay" (b.newRoot == c.postRoot) then
      t := { t with replayed := t.replayed + 1 }
    let u ← IO.ofExcept (update store.source c.preRoot (diffOf c.pre lean))
    if ← ok "Lean replay applied through update" (u.changes.newRoot == c.postRoot) then
      t := { t with replayedDiff := t.replayedDiff + 1 }
  let size := c.pre.foldl (fun n (k, v) => n + k.size + v.size) 0
  if size ≤ specLimit then
    t := { t with specChecked := t.specChecked + 1 }
    let a := specRoot c.pre.toList
    let b := specRoot postEntries.toList
    if
        ←
          ok "specification roots"
              (a.toOption.map (·.1) == some c.preRoot &&
                b.toOption.map (·.1) == some c.postRoot) then
      t := { t with spec := t.spec + 1 }
  let stopped ← IO.monoNanosNow
  return { t with
      keys := t.keys + c.pre.size + postEntries.size + c.diff.size,
      seconds := t.seconds + (stopped - started).toFloat / 1e9 }

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.head?.getD "state-roots-cases"
  let mut files := #[]
  for e in ← dir.readDir do
    if e.path.extension == some "case" then
      files := files.push e.path
  files := files.qsort fun a b => a.toString < b.toString
  let mut t : Totals := {}
  for f in files do
    let data ← IO.FS.readBinFile f
    let c ← IO.ofExcept ((parseCase.run { data }).map (·.1))
    t ← one (f.fileStem.getD "?") c t
  IO.println s!"chunks {t.chunks}"
  IO.println s!"  pre-state root from the raw entries     {t.pre}/{t.chunks}"
  IO.println s!"  post-state root from the stateDiff      {t.post}/{t.chunks}"
  IO.println s!"  reference counts equal a fresh build    {t.refcounts}/{t.chunks}"
  IO.println s!"  Lean replay post-state, built           {t.replayed}/{t.replayedCount}"
  IO.println s!"  Lean replay post-state, through update  {t.replayedDiff}/{t.replayedCount}"
  IO.println s!"  specification roots (chunks <= {specLimit} bytes)  {t.spec}/{t.specChecked}"
  IO.println s!"  {t.keys} key operations in {t.seconds} s"
  let good :=
    t.pre == t.chunks && t.post == t.chunks && t.refcounts == t.chunks &&
      t.replayed == t.replayedCount &&
      t.replayedDiff == t.replayedCount &&
      t.spec == t.specChecked
  return if good && t.chunks > 0 then 0 else 1
