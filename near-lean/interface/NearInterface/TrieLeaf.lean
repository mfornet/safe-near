import NearInterface.TrieSerialization

/-!
# Singleton leaf lookup through the actual trie reader

The zero-root sentinel and byte widths remain explicit. Hash binding premises
state which payload a witness search returns; they impose no hash injectivity.
-/
namespace Near.TrieLeaf
open TrieAccounting TrieConstruction TrieSerialization

local macro "trie_reader" name:ident : term => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  pure (Lean.mkIdent actual)

local macro "unfold_trie_reader" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))

/-- The runtime's first-match witness fetch. -/
def fetchObject : Witness → Hash → Except String Bytes := trie_reader fetch
/-- The runtime's bounded traversal, with its ancestor-cycle check. -/
def walkObjects : Witness → Bool → Nat → List Hash → Hash → List Nat → Accounting →
    Except String (Option ValueRef × Accounting) := trie_reader walk

/-- A binding is about the actual first match, including any hash aliases. -/
theorem fetchObject_binding (witness : Witness) (hash : Hash) (bytes : Bytes)
    (h : (witness.find? (·.1 == hash)).map Prod.snd = some bytes) :
    fetchObject witness hash = .ok bytes := by
  unfold fetchObject
  unfold_trie_reader fetch
  cases hf : witness.find? (·.1 == hash) with
  | none => simp [hf] at h
  | some pair =>
      cases pair
      simp only [hf, Option.map_some, Option.some.injEq] at h
      simp [h]

/-- A leaf terminates immediately, with exactly the optional node touch. -/
theorem walkObjects_leaf (witness : Witness) (root : Hash) (bytes : Bytes)
    (path key : List Nat) (reference : ValueRef) (state : Accounting)
    (accountNodes : Bool) (fuel : Nat)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.leaf path reference)) :
    walkObjects witness accountNodes (fuel + 1) [] root key state =
      .ok (if path == key then some reference else none,
        if accountNodes then state.touch root "node" else state) := by
  unfold walkObjects
  unfold_trie_reader walk
  unfold fetchObject at hfetch
  simp only [beq_eq_false_iff_ne.mpr hroot, Bool.false_eq_true, ↓reduceIte,
    List.contains_nil, bind, Except.bind, hfetch, hdecode, pure, Except.pure]

/-- Dereferencing a correctly bound value returns the exact bytes and one touch. -/
theorem dereference_binding (witness : Witness) (reference : ValueRef)
    (bytes : Bytes) (state : Accounting)
    (hfetch : fetchObject witness reference.hash = .ok bytes)
    (hlength : bytes.length = reference.length) :
    dereference witness reference state = .ok (bytes, state.touch reference.hash "value") := by
  unfold fetchObject at hfetch
  simp [dereference, hfetch, hlength, bind, Except.bind]
  rfl

/-- Each query starts fresh counters/events, retaining or resetting only cache. -/
def queryStart (previous : Accounting) (query : Query) : Accounting :=
  { seen := if query.resetCache then [] else previous.seen }

def leafState (root : Hash) (previous : Accounting) (query : Query) : Accounting :=
  if query.accountNodes then (queryStart previous query).touch root "node"
  else queryStart previous query

/-- Reference-only lookup is exact even when node accounting is disabled. -/
theorem lookup_leaf_reference (witness : Witness) (root : Hash) (bytes : Bytes)
    (path : List Nat) (reference : ValueRef) (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.leaf path reference))
    (hmode : query.dereference = false) :
    lookup witness root previous query =
      .ok {
        reference := if path == nibbles query.key then some reference else none
        value := none
        state := leafState root previous query } := by
  have hw := walkObjects_leaf witness root bytes path (nibbles query.key) reference
    (queryStart previous query) query.accountNodes witness.length hroot hfetch hdecode
  unfold walkObjects queryStart at hw
  simp only [lookup, hw, bind, Except.bind]
  split <;> simp_all [leafState, queryStart, pure, Except.pure]

/-- A present leaf and its separately bound value give exact dereferencing lookup. -/
theorem lookup_leaf_value (witness : Witness) (root : Hash) (bytes value : Bytes)
    (reference : ValueRef) (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.leaf (nibbles query.key) reference))
    (hvalue : fetchObject witness reference.hash = .ok value)
    (hlength : value.length = reference.length)
    (hmode : query.dereference = true) :
    lookup witness root previous query =
      .ok {
        reference := some reference
        value := some value
        state := (leafState root previous query).touch reference.hash "value" } := by
  have hw := walkObjects_leaf witness root bytes (nibbles query.key) (nibbles query.key) reference
    (queryStart previous query) query.accountNodes witness.length hroot hfetch hdecode
  unfold walkObjects queryStart at hw
  have hd := dereference_binding witness reference value (leafState root previous query) hvalue hlength
  simp only [beq_self_eq_true, ↓reduceIte] at hw
  simp only [lookup, hw, bind, Except.bind, hmode, ↓reduceIte]
  change (do let (bytes, state) ← dereference witness reference (leafState root previous query)
             pure ({ reference := some reference, value := some bytes, state } : Result)) = _
  rw [hd]
  rfl

/-- The exact memory charge and serialized bytes of the singleton constructor. -/
def singletonUsage (key value : Bytes) : Nat :=
  100 + 2 * (encodePath true (nibbles key)).length + value.length

def singletonBytes (key value : Bytes) : Bytes :=
  [0] ++ vectorBytes (encodePath true (nibbles key)) ++ valueRefBytes value ++
    littleEndian 8 (singletonUsage key value)

def singletonRoot (key value : Bytes) : Hash := Sha256.hash (singletonBytes key value)

def singletonReference (value : Bytes) : ValueRef :=
  { hash := Sha256.hash value, length := value.length }

/-- First-match deduplication used by the actual constructor. Equal hashes are
allowed only when their payloads agree; this is a binding condition, not a
cryptographic injectivity assertion. -/
def singletonWitness (key value : Bytes) : Witness :=
  let root := singletonRoot key value
  let node := singletonBytes key value
  if root == Sha256.hash value then [(root, node)]
  else [(root, node), (Sha256.hash value, value)]

def singletonBuilt (key value : Bytes) : Built :=
  { root := singletonRoot key value
    memoryUsage := singletonUsage key value
    witness := singletonWitness key value }

/-- The serialized node parser is discharged, with all three widths explicit. -/
theorem singletonBytes_decode (key value : Bytes)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64) :
    decodeNode (singletonBytes key value) =
      .ok (.leaf (nibbles key) (singletonReference value)) :=
  decodeNode_leaf_nibbles key value (singletonUsage key value) hkey hvalue husage

/-- The root object is the first record independently of hash aliasing. -/
theorem singleton_fetch_node (key value : Bytes) :
    fetchObject (singletonWitness key value) (singletonRoot key value) =
      .ok (singletonBytes key value) := by
  apply fetchObject_binding
  unfold singletonWitness
  dsimp only
  split <;> simp

/-- Successful collision checking suffices for exact value retrieval, including
an alias whose bytes agree with the node object. -/
theorem singleton_fetch_value (key value : Bytes)
    (hbinding : singletonRoot key value = Sha256.hash value → singletonBytes key value = value) :
    fetchObject (singletonWitness key value) (Sha256.hash value) = .ok value := by
  apply fetchObject_binding
  unfold singletonWitness
  dsimp only
  split
  · rename_i h
    have heq := eq_of_beq h
    simp [heq, hbinding heq]
  · rename_i h
    simp [h]

/-- Actual canonical singleton lookup returns its exact reference and cache state. -/
theorem singleton_lookup_reference (key value : Bytes) (previous : Accounting) (query : Query)
    (hquery : query.key = key) (hmode : query.dereference = false)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64)
    (hroot : singletonRoot key value ≠ List.replicate 32 0) :
    lookup (singletonWitness key value) (singletonRoot key value) previous query =
      .ok {
        reference := some (singletonReference value)
        value := none
        state := leafState (singletonRoot key value) previous query } := by
  have h := lookup_leaf_reference (singletonWitness key value) (singletonRoot key value)
    (singletonBytes key value) (nibbles key) (singletonReference value) previous query hroot
    (singleton_fetch_node key value) (singletonBytes_decode key value hkey hvalue husage) hmode
  simpa [hquery] using h

/-- Exact byte lookup, with a local binding premise matching collision checking. -/
theorem singleton_lookup_value (key value : Bytes) (previous : Accounting) (query : Query)
    (hquery : query.key = key) (hmode : query.dereference = true)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64)
    (hroot : singletonRoot key value ≠ List.replicate 32 0)
    (hbinding : singletonRoot key value = Sha256.hash value → singletonBytes key value = value) :
    lookup (singletonWitness key value) (singletonRoot key value) previous query =
      .ok {
        reference := some (singletonReference value)
        value := some value
        state := (leafState (singletonRoot key value) previous query).touch (Sha256.hash value) "value" } := by
  apply lookup_leaf_value _ _ (singletonBytes key value) _ _ _ _ hroot
    (singleton_fetch_node key value)
  · simpa [hquery] using singletonBytes_decode key value hkey hvalue husage
  · exact singleton_fetch_value key value hbinding
  · rfl
  · exact hmode

local macro "trie_constructor" name:ident : term => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") name.getId.toString
  pure (Lean.mkIdent actual)

local macro "unfold_trie_constructor" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual))

private theorem construct_singleton (key value : Bytes) (fuel : Nat)
    (hkey : key.length + 1 < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64) :
    (trie_constructor construct) (fuel + 1) [(nibbles key, value)] =
      .ok { root := singletonRoot key value
            memoryUsage := singletonUsage key value
            witness := [(singletonRoot key value, singletonBytes key value), (Sha256.hash value, value)] } := by
  have hp : (encodePath true (nibbles key)).length < 2 ^ 32 := by
    simpa [encodePath_nibbles_length] using hkey
  unfold_trie_constructor construct
  simp only [show ¬ (encodePath true (nibbles key)).length ≥ 2 ^ 32 from Nat.not_le.mpr hp,
    ↓reduceIte]
  unfold_trie_constructor finish
  change (if singletonUsage key value ≥ 2 ^ 64 then _ else _) = _
  simp only [show ¬ singletonUsage key value ≥ 2 ^ 64 from Nat.not_le.mpr husage, ↓reduceIte]
  rfl

/-- The singleton object definitions are the actual builder output, conditional
only on its width and collision checks. -/
theorem build_singleton (key value : Bytes)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64)
    (hbinding : singletonRoot key value = Sha256.hash value → singletonBytes key value = value) :
    build [(key, value)] = .ok (singletonBuilt key value) := by
  have hk : ¬ key.length ≥ 2 ^ 32 := by omega
  have hv : ¬ value.length ≥ 2 ^ 32 := Nat.not_le.mpr hvalue
  unfold build
  simp only [List.map_cons, List.map_nil, List.eraseDups_cons,
    Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil,
    List.any_cons, List.any_nil, hk, hv,
    decide_false, Bool.or_false, List.foldl_cons, List.foldl_nil]
  rw [construct_singleton key value _ hkey husage]
  simp only [bind, Except.bind]
  by_cases heq : singletonRoot key value = Sha256.hash value
  · have hb := hbinding heq
    simp [heq, hb, singletonBuilt, singletonWitness, bind, Except.bind, pure, Except.pure]
  · simp [heq, singletonBuilt, singletonWitness, bind, Except.bind, pure, Except.pure]

/-- A successful actual build supplies the hash binding check itself. Widths
remain explicit here; no semantic assumption about SHA-256 is required. -/
theorem build_singleton_success (key value : Bytes) (built : Built)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64)
    (hbuild : build [(key, value)] = .ok built) :
    built = singletonBuilt key value ∧
      (singletonRoot key value = Sha256.hash value → singletonBytes key value = value) := by
  by_cases hb : singletonRoot key value = Sha256.hash value → singletonBytes key value = value
  · rw [build_singleton key value hkey hvalue husage hb] at hbuild
    exact ⟨(Except.ok.inj hbuild).symm, hb⟩
  · have heq : singletonRoot key value = Sha256.hash value := by
      exact Classical.byContradiction (fun h => hb (fun he => False.elim (h he)))
    have hne : singletonBytes key value ≠ value := fun h => hb (fun _ => h)
    have hk : ¬ key.length ≥ 2 ^ 32 := by omega
    have hv : ¬ value.length ≥ 2 ^ 32 := Nat.not_le.mpr hvalue
    unfold build at hbuild
    simp only [List.map_cons, List.map_nil, List.eraseDups_cons,
      Bool.false_eq_true, ↓reduceIte, List.length_cons, List.length_nil,
      List.any_cons, List.any_nil, hk, hv, decide_false, Bool.or_false,
      List.foldl_cons, List.foldl_nil] at hbuild
    rw [construct_singleton key value _ hkey husage] at hbuild
    simp [heq, hne, bind, Except.bind, pure, Except.pure] at hbuild

/-- Exact dereferencing lookup for an actual successful singleton build. Its
collision check discharges the value binding; only the sentinel stays external. -/
theorem built_lookup_value (key value : Bytes) (built : Built)
    (previous : Accounting) (query : Query)
    (hbuild : build [(key, value)] = .ok built)
    (hquery : query.key = key) (hmode : query.dereference = true)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64)
    (hroot : built.root ≠ List.replicate 32 0) :
    lookup built.witness built.root previous query =
      .ok {
        reference := some (singletonReference value)
        value := some value
        state := (leafState built.root previous query).touch (Sha256.hash value) "value" } := by
  obtain ⟨rfl, hbinding⟩ := build_singleton_success key value built hkey hvalue husage hbuild
  exact singleton_lookup_value key value previous query hquery hmode hkey hvalue husage hroot hbinding

/-- Reference-only lookup needs no separate value read or binding assumption. -/
theorem built_lookup_reference (key value : Bytes) (built : Built)
    (previous : Accounting) (query : Query)
    (hbuild : build [(key, value)] = .ok built)
    (hquery : query.key = key) (hmode : query.dereference = false)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64)
    (hroot : built.root ≠ List.replicate 32 0) :
    lookup built.witness built.root previous query =
      .ok {
        reference := some (singletonReference value)
        value := none
        state := leafState built.root previous query } := by
  obtain ⟨rfl, _⟩ := build_singleton_success key value built hkey hvalue husage hbuild
  exact singleton_lookup_reference key value previous query hquery hmode hkey hvalue husage hroot

/-- A nonmatching leaf does not dereference any value, in either query mode. -/
theorem lookup_leaf_absent (witness : Witness) (root : Hash) (bytes : Bytes)
    (path : List Nat) (reference : ValueRef) (previous : Accounting) (query : Query)
    (hroot : root ≠ List.replicate 32 0)
    (hfetch : fetchObject witness root = .ok bytes)
    (hdecode : decodeNode bytes = .ok (.leaf path reference))
    (hmiss : path ≠ nibbles query.key) :
    lookup witness root previous query =
      .ok { reference := none, value := none, state := leafState root previous query } := by
  have hw := walkObjects_leaf witness root bytes path (nibbles query.key) reference
    (queryStart previous query) query.accountNodes witness.length hroot hfetch hdecode
  unfold walkObjects queryStart at hw
  simp only [beq_eq_false_iff_ne.mpr hmiss, Bool.false_eq_true, ↓reduceIte] at hw
  simp only [lookup, hw, bind, Except.bind, pure, Except.pure]
  rfl

/-- Node accounting contributes exactly one access, regardless of cache hits. -/
theorem leafState_total (root : Hash) (previous : Accounting) (query : Query) :
    (leafState root previous query).disk + (leafState root previous query).mem =
      if query.accountNodes then 1 else 0 := by
  unfold leafState
  split
  · rw [Accounting.touch_total]; rfl
  · rfl

theorem leafState_events (root : Hash) (previous : Accounting) (query : Query) :
    (leafState root previous query).events.length = if query.accountNodes then 1 else 0 := by
  unfold leafState
  split
  · rw [Accounting.touch_events]; rfl
  · rfl

/-- Dereferencing adds exactly one access even if the value aliases a node hash. -/
theorem leafValue_total (root : Hash) (valueHash : Hash) (previous : Accounting) (query : Query) :
    ((leafState root previous query).touch valueHash "value").disk +
      ((leafState root previous query).touch valueHash "value").mem =
      (if query.accountNodes then 1 else 0) + 1 := by
  rw [Accounting.touch_total, leafState_total]

theorem leafValue_events (root : Hash) (valueHash : Hash) (previous : Accounting) (query : Query) :
    ((leafState root previous query).touch valueHash "value").events.length =
      (if query.accountNodes then 1 else 0) + 1 := by
  rw [Accounting.touch_events, leafState_events]

/-- Byte keys are recovered uniquely from their high/low nibble pairs. -/
theorem nibbles_injective (left right : Bytes) (h : nibbles left = nibbles right) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all [nibbles]
  | cons a rest ih =>
    cases right with
    | nil => simp [nibbles] at h
    | cons b tail =>
      have hs : a.toNat / 16 = b.toNat / 16 ∧ a.toNat % 16 = b.toNat % 16 ∧
          nibbles rest = nibbles tail := by simpa [nibbles] using h
      have hab : a = b := UInt8.toNat_inj.mp (by omega)
      cases hab
      rw [ih tail hs.2.2]

/-- A distinct raw key misses the singleton, including dereferencing queries. -/
theorem built_lookup_absent (key value : Bytes) (built : Built)
    (previous : Accounting) (query : Query)
    (hbuild : build [(key, value)] = .ok built)
    (hquery : query.key ≠ key)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64)
    (hroot : built.root ≠ List.replicate 32 0) :
    lookup built.witness built.root previous query =
      .ok { reference := none, value := none, state := leafState built.root previous query } := by
  obtain ⟨rfl, _⟩ := build_singleton_success key value built hkey hvalue husage hbuild
  apply lookup_leaf_absent _ _ (singletonBytes key value) _ (singletonReference value)
    _ _ hroot (singleton_fetch_node key value) (singletonBytes_decode key value hkey hvalue husage)
  exact fun h => hquery (nibbles_injective key query.key h).symm

/-- A reference returned by the singleton has an independently proved exact
on-disk dereference, allowing callers to charge between the two phases. -/
theorem built_dereference_value (key value : Bytes) (built : Built) (state : Accounting)
    (hbuild : build [(key, value)] = .ok built)
    (hkey : key.length + 1 < 2 ^ 32) (hvalue : value.length < 2 ^ 32)
    (husage : singletonUsage key value < 2 ^ 64) :
    dereference built.witness (singletonReference value) state =
      .ok (value, state.touch (Sha256.hash value) "value") := by
  obtain ⟨rfl, hb⟩ := build_singleton_success key value built hkey hvalue husage hbuild
  exact dereference_binding _ _ _ _ (singleton_fetch_value key value hb) rfl

end Near.TrieLeaf
