import Lean.Data.Json
import Lean.Elab.Tactic.Omega

/-!
Canonical on-disk NEAR trie lookup and hash-keyed accounting-cache semantics.
This consumes a Borsh witness, not native gas counts or native lookup paths.
Callers establish hash-to-byte bindings; trie-replay checks them with pure SHA256
or constructs objects directly. Updates, flat storage, memtries and receipt-wide
cache integration are separate work.
-/
namespace Near.TrieAccounting

abbrev Bytes := List UInt8
abbrev Hash := Bytes
abbrev Witness := List (Hash × Bytes)

structure ValueRef where
  hash : Hash
  length : Nat
  deriving Repr, BEq

inductive Node where
  | leaf (path : List Nat) (value : ValueRef)
  | extension (path : List Nat) (child : Hash)
  | branch (value : Option ValueRef) (children : List (Nat × Hash))
  deriving Repr

abbrev Parser := StateT Bytes (Except String)

private def readBytes (count : Nat) : Parser Bytes := do
  let bytes ← get
  if bytes.length < count then throw "truncated trie node"
  set (bytes.drop count)
  return bytes.take count

private def readNat (count : Nat) : Parser Nat := do
  return (← readBytes count).foldr (fun byte rest => byte.toNat + 256 * rest) 0

private def readRef : Parser ValueRef := do
  let length ← readNat 4
  return { length, hash := ← readBytes 32 }

def nibbles (bytes : Bytes) : List Nat :=
  bytes.flatMap fun byte => [byte.toNat / 16, byte.toNat % 16]

/-- Strict canonical hex-prefix encoding: leaf flag and padding must agree. -/
def decodePath (leaf : Bool) (bytes : Bytes) : Except String (List Nat) := do
  let first :: rest := bytes | throw "empty compact trie path"
  let flag := first.toNat / 16
  if flag ≥ 4 || (flag ≥ 2) != leaf then throw "invalid compact trie path flag"
  if flag % 2 == 0 then
    if first.toNat % 16 != 0 then throw "invalid compact trie path padding"
    return nibbles rest
  else return first.toNat % 16 :: nibbles rest

private def readPath (leaf : Bool) : Parser (List Nat) := do
  let count ← readNat 4
  let bytes ← readBytes count
  match decodePath leaf bytes with
  | .ok path => pure path
  | .error error => throw error

private def readChildren : Parser (List (Nat × Hash)) := do
  let mask ← readNat 2
  let mut children := []
  for nibble in [0:16] do
    if mask / 2 ^ nibble % 2 == 1 then
      children := children ++ [(nibble, ← readBytes 32)]
  return children

/-- Decode RawTrieNodeWithSize, including the trailing u64 subtree memory size.
Opaque values are decoded only when reached as nodes, never by guessing roles. -/
def decodeNode (bytes : Bytes) : Except String Node := do
  let parser : Parser Node := do
    let tag ← readNat 1
    let node : Node ← match tag with
      | 0 => do
        let path ← readPath true
        let value ← readRef
        pure (.leaf path value)
      | 1 => do pure (.branch none (← readChildren))
      | 2 => do
        let value ← readRef
        pure (.branch (some value) (← readChildren))
      | 3 => do
        let path ← readPath false
        if path.isEmpty then throw "empty trie extension"
        pure (.extension path (← readBytes 32))
      | _ => throw "unknown trie node variant"
    let _ ← readNat 8
    return node
  let (node, remaining) ← parser.run bytes
  unless remaining.isEmpty do throw "trailing trie node bytes"
  return node

structure Event where
  hash : Hash
  kind : String
  cached : Bool
  deriving Repr, BEq

structure Accounting where
  seen : List Hash := []
  disk : Nat := 0
  mem : Nat := 0
  events : List Event := []
  deriving Repr

def Accounting.touch (state : Accounting) (hash : Hash) (kind : String) : Accounting :=
  let cached := state.seen.contains hash
  { seen := if cached then state.seen else hash :: state.seen
    disk := state.disk + if cached then 0 else 1
    mem := state.mem + if cached then 1 else 0
    events := state.events ++ [{ hash, kind, cached }] }

theorem Accounting.touch_total (state : Accounting) (hash : Hash) (kind : String) :
    (state.touch hash kind).disk + (state.touch hash kind).mem = state.disk + state.mem + 1 := by
  dsimp only [touch]
  split <;> simp_all <;> omega

theorem Accounting.touch_events (state : Accounting) (hash : Hash) (kind : String) :
    (state.touch hash kind).events.length = state.events.length + 1 := by
  simp [touch]

private def fetch (witness : Witness) (hash : Hash) : Except String Bytes :=
  match witness.find? (·.1 == hash) with
  | some (_, bytes) => .ok bytes
  | none => .error "missing trie witness object"

private def walk (witness : Witness) (accountNodes : Bool) : Nat → List Hash → Hash → List Nat → Accounting →
    Except String (Option ValueRef × Accounting)
  | 0, _, _, _, _ => .error "trie witness traversal exhausted"
  | fuel + 1, ancestors, hash, key, state => do
    if hash == List.replicate 32 0 then return (none, state)
    if ancestors.contains hash then throw "cyclic trie witness"
    let bytes ← fetch witness hash
    let state := if accountNodes then state.touch hash "node" else state
    match ← decodeNode bytes with
    | .leaf path value => return (if path == key then some value else none, state)
    | .extension path child =>
      if path.isPrefixOf key then walk witness accountNodes fuel (hash :: ancestors) child (key.drop path.length) state
      else return (none, state)
    | .branch value children =>
      match key with
      | [] => return (value, state)
      | nibble :: rest =>
        match children.find? (·.1 == nibble) with
        | none => return (none, state)
        | some (_, child) => walk witness accountNodes fuel (hash :: ancestors) child rest state

structure Query where
  key : Bytes
  accountNodes : Bool
  dereference : Bool
  resetCache : Bool
  deriving Repr

structure Result where
  reference : Option ValueRef
  value : Option Bytes
  state : Accounting
  deriving Repr

/-- Value dereference is a separate accounted phase. RuntimeExt can exhaust
gas on the old-value byte charge after finding a reference, before this read. -/
def dereference (witness : Witness) (reference : ValueRef) (state : Accounting) :
    Except String (Bytes × Accounting) := do
  let bytes ← fetch witness reference.hash
  if bytes.length != reference.length then throw "trie value length mismatch"
  return (bytes, state.touch reference.hash "value")

/-- One successful on-disk dereference records exactly one access, whether its
hash is fresh or already cached (including aliases with previously read nodes). -/
theorem dereference_success_total (witness : Witness) (reference : ValueRef)
    (before after : Accounting) (bytes : Bytes)
    (h : dereference witness reference before = .ok (bytes, after)) :
    after.disk + after.mem = before.disk + before.mem + 1 := by
  cases hf : fetch witness reference.hash with
  | error error => simp [dereference, hf, bind, Except.bind] at h
  | ok payload =>
    by_cases hl : payload.length = reference.length
    · simp [dereference, hf, hl, bind, Except.bind] at h
      rcases h with ⟨rfl, rfl⟩
      exact Accounting.touch_total before reference.hash "value"
    · simp [dereference, hf, hl, bind, Except.bind] at h

/-- Lookups retain the cache across queries but report per-query counters/events. -/
def lookup (witness : Witness) (root : Hash) (previous : Accounting) (query : Query) : Except String Result := do
  let state : Accounting := { seen := if query.resetCache then [] else previous.seen }
  let (reference, state) ← walk witness query.accountNodes (witness.length + 1) [] root (nibbles query.key) state
  match reference with
  | some reference =>
    if query.dereference then
      let (bytes, state) ← dereference witness reference state
      return { reference := some reference, value := some bytes, state }
    else return { reference := some reference, value := none, state }
  | none => return { reference := none, value := none, state }

end Near.TrieAccounting
