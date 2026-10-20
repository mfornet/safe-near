import NearVM.TrieConstruction

/-! TrieUpdate's prospective and committed ContractData overlays. Reads of
in-memory updates bypass trie accounting; rollback does not rewind the cache.
Storage primitives remain separate from VM host fees and receipt cache lifetime;
NearVM.Metered composes them at the optional VM external boundary. -/
namespace Near.TrieOverlay
open TrieAccounting TrieConstruction

abbrev Changes := List (Bytes × Option Bytes)

structure State where
  entries : List (Bytes × Bytes)
  base : Built
  prospective : Changes := []
  committed : Changes := []
  accounting : Accounting := {}

inductive Operation where
  | set (key value : Bytes)
  | remove (key : Bytes)
  | get (key : Bytes) (accountNodes dereference : Bool)
  | has (key : Bytes)
  | commit | rollback | checkpoint | resetCache
  deriving Repr

structure Observation where
  kind : String
  rawKey : Option Bytes := none
  reference : Option (String × ValueRef) := none
  value : Option Bytes := none
  present : Option Bool := none
  isLookup : Bool := false

/-- Native TrieKey::ContractData: column 9, validated account id, comma, raw key. -/
def contractKey (account key : Bytes) : Bytes := [9] ++ account ++ [44] ++ key

private def insert (changes : Changes) (key : Bytes) (value : Option Bytes) : Changes :=
  (key, value) :: changes.filter (·.1 != key)

private def applyChanges (entries : List (Bytes × Bytes)) (changes : Changes) : List (Bytes × Bytes) :=
  changes.foldl (fun entries (key, value) =>
    let remaining := entries.filter (·.1 != key)
    match value with
    | none => remaining
    | some value => (key, value) :: remaining) entries

def State.view (state : State) : List (Bytes × Bytes) :=
  applyChanges (applyChanges state.entries state.committed) state.prospective

private def overlay (state : State) (key : Bytes) : Option (Option Bytes) :=
  ((state.prospective.find? (·.1 == key)).map Prod.snd).orElse fun _ =>
    (state.committed.find? (·.1 == key)).map Prod.snd

/-- Stage a raw trie update without resetting access counters or the shared cache. -/
def State.set (state : State) (key value : Bytes) : State :=
  { state with prospective := insert state.prospective key (some value) }

def State.remove (state : State) (key : Bytes) : State :=
  { state with prospective := insert state.prospective key none }

def start (entries : List (Bytes × Bytes)) : Except String State := do
  return { entries, base := ← build entries }

/-- A reference keeps its origin: overlay bytes need no trie dereference, while
on-disk values retain their canonical reference and originating base root. -/
inductive ValuePointer where
  | memory (bytes : Bytes)
  | trie (root : Hash) (reference : ValueRef)
  deriving Repr

def ValuePointer.reference : ValuePointer → String × ValueRef
  | .memory bytes => ("memory", { hash := Sha256.hash bytes, length := bytes.length })
  | .trie _ reference => ("trie", reference)

/-- Find the old value without dereferencing it. In particular, this phase
does not warm the value hash when the subsequent byte charge would fail. -/
def getReference (state : State) (key : Bytes) (accountNodes : Bool) :
    Except String (State × Option ValuePointer) := do
  match overlay state key with
  | some none => return (state, none)
  | some (some value) => return (state, some (.memory value))
  | none =>
    let result ← lookup state.base.witness state.base.root state.accounting {
      key, accountNodes, dereference := false, resetCache := false }
    -- `lookup` reports a fresh query. The external backend retains cumulative
    -- counters so a later VM call can subtract its own starting snapshot.
    let accounting := { result.state with
      disk := state.accounting.disk + result.state.disk
      mem := state.accounting.mem + result.state.mem
      events := state.accounting.events ++ result.state.events }
    return ({ state with accounting }, result.reference.map (.trie state.base.root))

/-- Consume a reference after any intervening gas charge. A mismatched base is
rejected instead of dereferencing against an unrelated checkpoint. -/
def dereference (state : State) : ValuePointer → Except String (State × Bytes)
  | .memory bytes => .ok (state, bytes)
  | .trie root reference => do
    unless root == state.base.root do throw "trie reference belongs to a different base"
    let (bytes, accounting) ← TrieAccounting.dereference state.base.witness reference state.accounting
    return ({ state with accounting }, bytes)

theorem dereference_memory (state : State) (bytes : Bytes) :
    dereference state (.memory bytes) = .ok (state, bytes) := rfl

theorem dereference_wrong_root (state : State) (root : Hash) (reference : ValueRef)
    (h : root ≠ state.base.root) :
    dereference state (.trie root reference) = .error "trie reference belongs to a different base" := by
  simp [dereference, h, bind, Except.bind]
  rfl

private def read (state : State) (key : Bytes) (accountNodes readValue : Bool) :
    Except String (State × Option (String × ValueRef) × Option Bytes) := do
  let (state, pointer) ← getReference state key accountNodes
  match pointer with
  | none => return (state, none, none)
  | some pointer =>
    if readValue then
      let (state, bytes) ← dereference state pointer
      return (state, some pointer.reference, some bytes)
    else return (state, some pointer.reference, none)

/-- Each operation reports fresh counters/events while retaining the hash cache.
A checkpoint publishes only committed updates and preserves the cache explicitly. -/
def step (account : Bytes) (operation : Operation) (before : State) : Except String (State × Observation) := do
  let state := { before with accounting := { seen := before.accounting.seen } }
  match operation with
  | .set key value =>
    let key := contractKey account key
    if key.length ≥ 2 ^ 32 || value.length ≥ 2 ^ 32 then throw "trie key or value exceeds u32"
    return ({ state with prospective := insert state.prospective key (some value) }, { kind := "set", rawKey := some key })
  | .remove key =>
    let key := contractKey account key
    return ({ state with prospective := insert state.prospective key none }, { kind := "remove", rawKey := some key })
  | .get key accountNodes dereference =>
    let key := contractKey account key
    let (state, reference, value) ← read state key accountNodes dereference
    return (state, { kind := "get", rawKey := some key, reference, value, isLookup := true })
  | .has key =>
    let key := contractKey account key
    let (state, reference, _) ← read state key false false
    return (state, { kind := "has", rawKey := some key, present := some reference.isSome })
  | .commit =>
    let committed := state.prospective.foldl (fun changes (key, value) => insert changes key value) state.committed
    return ({ state with committed, prospective := [] }, { kind := "commit" })
  | .rollback => return ({ state with prospective := [] }, { kind := "rollback" })
  | .resetCache => return ({ state with accounting := {} }, { kind := "resetCache" })
  | .checkpoint =>
    unless state.prospective.isEmpty do throw "cannot checkpoint prospective changes"
    let entries := applyChanges state.entries state.committed
    let base ← build entries
    return ({ state with entries, base, committed := [] }, { kind := "checkpoint" })

/-- Storage rollback discards prospective writes, but cannot erase persistent
updates or rewind trie accesses already observed during the attempt. -/
theorem rollback_keeps_base_committed_cache (account : Bytes) (before : State) :
    (step account .rollback before).map (fun (after, _) =>
      (after.base.root, after.committed, after.accounting.seen)) =
      .ok (before.base.root, before.committed, before.accounting.seen) := rfl

theorem commit_keeps_base_cache_and_clears_prospective (account : Bytes) (before : State) :
    (step account .commit before).map (fun (after, _) =>
      (after.base.root, after.accounting.seen, after.prospective)) =
      .ok (before.base.root, before.accounting.seen, []) := rfl

end Near.TrieOverlay
