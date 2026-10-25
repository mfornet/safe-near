import NearNode.Trie
import NodeTests.Rng

/-!
`node-trie-tests [CASES]`: differential tests of the trie `Impl` against `Spec`
(`NearInterface.TrieConstruction.build` on the complete entry set).

For seeded random entry sets and update batches the tests check that

* the root and the memory usage of an incremental update equal the `Spec`'s,
* the node store after any number of updates equals the store of the final entry set built
  from scratch, hash by hash with its reference count: the refcount deltas of `update` are exactly
  the difference of the two tries,
* lookups, `contains` and iteration (with every lower bound) agree with a sorted association list,
* an update run on the nodes recorded by a first run, and nothing else, gives the same changes
  (the stateless validation property of `Trie::recording_reads`).
-/

open Near.Node Near.Node.Trie Near.Node.Borsh

/-- A key over a small alphabet, so keys share prefixes and some are prefixes of others. -/
def genKey : R ByteArray := do
  let len ← below 7
  let mut k := ByteArray.empty
  for _ in [0:len] do
    k := k.push (UInt8.ofNat (← below 4) * 0x11 + (if (← below 3) == 0 then 1 else 0))
  return k

def genValue : R ByteArray := do
  let len ← below 4
  let big ← below 90
  let n := if len == 0 then 0 else if len == 1 then 1 else big
  let mut v := ByteArray.empty
  let tag ← below 6
  for i in [0:n] do
    v := v.push (UInt8.ofNat (tag * 7 + i % 5))
  return v

def genEntries (maxSize : Nat) : R (Array (ByteArray × ByteArray)) := do
  let n ← below (maxSize + 1)
  let mut m : Array (ByteArray × ByteArray) := #[]
  for _ in [0:n] do
    let k ← genKey
    let v ← genValue
    m := (m.filter fun e => e.1 != k).push (k, v)
  return m

/-- A batch: writes of new and existing keys, deletes of present and absent keys. -/
def genBatch (base : Array (ByteArray × ByteArray)) : R (Array Change) := do
  let n ← below 12
  let mut out : Array Change := #[]
  for _ in [0:n] do
    let kind ← below 4
    if kind == 0 && !base.isEmpty then
      out := out.push ((base[← below base.size]!).1, none)
    else if kind == 1 && !base.isEmpty then
      out := out.push ((base[← below base.size]!).1, some (← genValue))
    else if kind == 2 then
      out := out.push (← genKey, none)
    else
      out := out.push (← genKey, some (← genValue))
  return out

def applyModel (m : Array (ByteArray × ByteArray)) (cs : Array Change) :
    Array (ByteArray × ByteArray) :=
  cs.foldl
    (fun m (k, v) =>
      let m := m.filter fun e => e.1 != k
      match v with
      | some v => m.push (k, v)
      | none => m)
    m

def sorted (m : Array (ByteArray × ByteArray)) : Array (ByteArray × ByteArray) :=
  m.qsort fun a b => compareBytes a.1 b.1 == .lt

def storeEq (a b : MemStore) : Bool :=
  a.map.size == b.map.size &&
    a.map.fold (fun ok h (d, rc) => ok && (b.map.get? h == some (d, rc))) true

instance : BEq (ByteArray × Int) :=
  ⟨fun a b => a.1 == b.1 && a.2 == b.2⟩

def memoryOf (src : NodeSource) (root : CryptoHash) : Except String Nat :=
  if root == emptyRoot then .ok 0
  else
    match src.read root with
    | none => .error "root missing"
    | some b =>
      match Codec.decodeAll (α := RawTrieNodeWithSize) b with
      | .ok n => .ok n.memoryUsage.toNat
      | .error _ => .error "root undecodable"

def specOf (m : Array (ByteArray × ByteArray)) : Except String (CryptoHash × Nat) :=
  specRoot m.toList

structure Stats where
  cases : Nat := 0
  failures : Nat := 0

def fail (what : String) (seed : Nat) : IO Unit := do
  IO.eprintln s!"FAIL {what} (case {seed})"

def check (ok : Bool) (what : String) (seed : Nat) (s : Stats) : IO Stats := do
  if ok then
    return { s with cases := s.cases + 1 }
  fail what seed
  return { cases := s.cases + 1, failures := s.failures + 1 }

def runCase (seed : Nat) (s : Stats) : IO Stats := do
  let rng : Rng := ⟨(seed.toUInt64 + 1) * 0xD1B54A32D192ED03⟩
  let ((base, batches), _) :=
    (do
          let base ← genEntries 40
          let mut batches : Array (Array Change) := #[]
          let mut cur := base
          for _ in [0:3] do
            let b ← genBatch cur
            cur := applyModel cur b
            batches := batches.push b
          return (base, batches) : R _).run
      rng
  let mut s := s
  -- build from scratch against Spec
  let b0 ← IO.ofExcept (fromEntries base)
  let mut store ← IO.ofExcept ((MemStore.mk {}).apply b0)
  let mut root := b0.newRoot
  let mut model := base
  let some (specRoot0, mem0) := (specOf model).toOption | throw (IO.userError "spec failed")
  s ← check (root == specRoot0) "build root" seed s
  s ← check ((memoryOf store.source root).toOption == some mem0) "build memory" seed s
  -- lookups, contains and iteration
  let probe (st : MemStore) (root : CryptoHash) (model : Array (ByteArray × ByteArray))
    (s : Stats) : IO Stats := do
    let mut s := s
    for (k, v) in model do
      let r ← IO.ofExcept (get st.source root k)
      s ← check (r.1 == some v) "get present" seed s
      s ← check ((contains st.source root k).toOption == some true) "contains" seed s
    let rng2 : Rng := ⟨seed.toUInt64 * 77 + 5⟩
    let (absent, _) :=
      (do
            let mut out := #[]
            for _ in [0:6] do
              let k ← genKey
              if !(model.any fun e => e.1 == k) then
                out := out.push k
            return out : R _).run
        rng2
    for k in absent do
      let r ← IO.ofExcept (get st.source root k)
      s ← check r.1.isNone "get absent" seed s
    let want := sorted model
    let got ← IO.ofExcept (entries st.source root)
    s ←
      check
          (got.size == want.size &&
            (got.zip want).all fun (g, w) =>
              g.1 == w.1 && g.2 == ⟨(w.2.size.toUInt32), CryptoHash.hash w.2⟩)
          "iteration" seed s
    for lo in (absent.push ByteArray.empty).append (want.map (·.1)) do
      let g ← IO.ofExcept (foldFrom st.source root lo #[] fun acc k _ => (acc.push k, true))
      let w := (want.map (·.1)).filter fun k => compareBytes k lo != .lt
      s ← check (g == w) "iteration from a bound" seed s
    return s
  s ← probe store root model s
  -- updates
  for batch in batches do
    let rec1 ← IO.ofExcept (update store.source root batch (some {}))
    let ch := rec1.changes
    -- the update, replayed on the recorded nodes only, gives the same changes
    let stored : MemStore :=
      (rec1.recorded.getD {}).fold (fun (m : MemStore) h d => ⟨m.map.insert h (d, 1)⟩) ⟨{}⟩
    let again ← IO.ofExcept (update stored.source root batch)
    s ← check (again.changes == ch) "update on recorded nodes" seed s
    store ← IO.ofExcept (store.apply ch)
    root := ch.newRoot
    model := applyModel model batch
    let some (r', m') := (specOf model).toOption | throw (IO.userError "spec failed")
    s ← check (root == r') "update root" seed s
    s ← check ((memoryOf store.source root).toOption == some m') "update memory" seed s
    let scratch ← IO.ofExcept ((fromEntries model).bind fun c => (MemStore.mk {}).apply c)
    s ← check (storeEq store scratch) "refcounts equal a build from scratch" seed s
    s ← probe store root model s
  -- the node set is the Spec's
  let objs ← IO.ofExcept (specObjects model.toList)
  s ←
    check (objs.all fun (h, d) => (store.map.get? h).map (·.1) == some d) "spec objects stored" seed
        s
  return s

def main (args : List String) : IO UInt32 := do
  let cases := (args.head?.bind String.toNat?).getD 300
  let mut s : Stats := {}
  for i in [0:cases] do
    s ← runCase i s
  IO.println s!"trie differential tests: {cases} cases, {s.cases} checks, {s.failures} failures"
  return if s.failures == 0 then 0 else 1
