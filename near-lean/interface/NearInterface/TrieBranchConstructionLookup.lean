import NearInterface.TrieConstructionBranch
import NearInterface.TrieBranchLookup

/-!
# Constructed branches feed the actual trie lookup

The root object is first in the constructor's witness, so its fetch binding is
proved without hash injectivity. Child semantics are recursive walk equations
in that full witness, at the exact fuel/ancestor/cache state. Transferring child
semantics from isolated child witnesses through witness merging remains a
separate obligation; it is not assumed as a complete parent lookup equation.
-/
namespace Near.TrieBranchConstructionLookup
open TrieAccounting TrieConstruction TrieSerialization TrieBitmap TrieLeaf TrieBranchLookup
open TrieConstructionBranch

/-- Proof-facing packaging of the actual branch serialization accumulators. -/
def digits (entries : List (List Nat × Bytes)) : List Nat :=
  (List.range 16).filter (groupActive entries)

def references (entries : List (List Nat × Bytes)) (child : Nat → Built) : List (Nat × Hash) :=
  (digits entries).map fun digit => (digit, (child digit).root)

def usage (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) : Nat :=
  50 + ((digits entries).map fun digit => (child digit).memoryUsage).sum +
    match value with | none => 0 | some bytes => 50 + bytes.length

def nodeBytes (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) : Bytes :=
  (match value with | none => [1] | some bytes => [2] ++ valueRefBytes bytes) ++
    littleEndian 2 (maskOf (groupActive entries) 16) ++
    (digits entries).flatMap (fun digit => (child digit).root) ++ littleEndian 8 (usage entries child value)

def branchBuilt (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) : Built :=
  let bytes := nodeBytes entries child value
  { root := Sha256.hash bytes, memoryUsage := usage entries child value,
    witness := (Sha256.hash bytes, bytes) ::
      ((match value with | none => [] | some bytes => [(Sha256.hash bytes, bytes)]) ++
        (digits entries).flatMap (fun digit => (child digit).witness)) }

def valueReference (value : Option Bytes) : Option ValueRef :=
  value.map fun bytes => { length := bytes.length, hash := Sha256.hash bytes }

theorem nodeBytes_decode (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes)
    (hwidth : ∀ digit ∈ List.range 16, groupActive entries digit = true → (child digit).root.length = 32)
    (hvalue : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32)
    (husage : usage entries child value < 2 ^ 64) :
    decodeNode (nodeBytes entries child value) = .ok (.branch (valueReference value) (references entries child)) := by
  cases value with
  | none =>
    exact decodeNode_active_branch (groupActive entries) (fun digit => (child digit).root)
      (usage entries child none) hwidth husage
  | some bytes =>
    exact decodeNode_active_branch_value bytes (groupActive entries) (fun digit => (child digit).root)
      (usage entries child (some bytes)) (hvalue bytes rfl) hwidth husage

/-- All root aliases are harmless for fetching the first, root-node object. -/
theorem branch_fetch_root (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) :
    fetchObject (branchBuilt entries child value).witness (branchBuilt entries child value).root =
      .ok (nodeBytes entries child value) := by
  apply fetchObject_binding
  simp [branchBuilt]

/-- Local child construction results determine the actual parent's Built value. -/
theorem construct_branch_built (fuel : Nat) (first second : List Nat × Bytes)
    (rest : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes)
    (hshared : (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 = [])
    (hvalue : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd = value)
    (hchild : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      childAction fuel (first :: second :: rest) digit = .ok (child digit))
    (hwidth : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      (child digit).root.length = 32)
    (hvalueRoom : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32)
    (husage : usage (first :: second :: rest) child value < 2 ^ 64) :
    construct (fuel + 1) (first :: second :: rest) = .ok (branchBuilt (first :: second :: rest) child value) := by
  cases value with
  | none =>
    have h := construct_branch_no_value fuel first second rest child hshared hvalue hchild hwidth
      (by simpa [usage, digits] using husage)
    simpa [branchBuilt, nodeBytes, usage, digits, List.append_assoc] using h.1
  | some bytes =>
    have h := construct_branch_value fuel first second rest child bytes hshared hvalue hchild hwidth
      (hvalueRoom bytes rfl) (by simpa [usage, digits, Nat.add_assoc] using husage)
    simpa [branchBuilt, nodeBytes, usage, digits, List.append_assoc, Nat.add_assoc] using h.1

/-- Repeated digits do not affect first-match selection when every occurrence
uses the same root function. No list uniqueness premise is needed here. -/
theorem find_mapped_digits (selected : List Nat) (child : Nat → Built) (digit : Nat) :
    (selected.map fun i => (i, (child i).root)).find? (fun pair => pair.1 == digit) =
      if digit ∈ selected then some (digit, (child digit).root) else none := by
  induction selected with
  | nil => simp
  | cons i selected ih =>
    by_cases he : i = digit
    · subst i
      simp
    · simp [he, Ne.symm he, ih]

theorem references_find (entries : List (List Nat × Bytes)) (child : Nat → Built) (digit : Nat) :
    (references entries child).find? (fun pair => pair.1 == digit) =
      if digit < 16 ∧ groupActive entries digit = true then some (digit, (child digit).root) else none := by
  rw [references, find_mapped_digits]
  simp [digits]

/-- Actual lookup through a constructed branch, with only the selected child's
recursive walk as a semantic premise. Root fetching and decoding are derived. -/
theorem branch_lookup_child_reference (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (digit : Nat) (tail : List Nat) (previous after : Accounting)
    (query : Query) (reference : Option ValueRef)
    (hwidth : ∀ digit ∈ List.range 16, groupActive entries digit = true → (child digit).root.length = 32)
    (hvalueRoom : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32)
    (husage : usage entries child value < 2 ^ 64)
    (hroot : (branchBuilt entries child value).root ≠ List.replicate 32 0)
    (hkey : nibbles query.key = digit :: tail)
    (hdigit : digit < 16) (hactive : groupActive entries digit = true)
    (hchild : walkObjects (branchBuilt entries child value).witness query.accountNodes
      (branchBuilt entries child value).witness.length [(branchBuilt entries child value).root]
      (child digit).root tail
      (if query.accountNodes then (queryStart previous query).touch (branchBuilt entries child value).root "node"
        else queryStart previous query) = .ok (reference, after))
    (hmode : query.dereference = false) :
    lookup (branchBuilt entries child value).witness (branchBuilt entries child value).root previous query =
      .ok { reference, value := none, state := after } := by
  apply lookup_branch_child_reference _ _ _ (nodeBytes entries child value) (valueReference value)
    reference (references entries child) digit tail previous after query hroot
    (branch_fetch_root entries child value) (nodeBytes_decode entries child value hwidth hvalueRoom husage)
    hkey _ hchild hmode
  simp only [references_find, hdigit, hactive, and_self, ↓reduceIte]

/-- A constructed branch without a selected digit terminates with absence,
without requiring any recursive child semantics. -/
theorem branch_lookup_miss (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (digit : Nat) (tail : List Nat) (previous : Accounting) (query : Query)
    (hwidth : ∀ digit ∈ List.range 16, groupActive entries digit = true → (child digit).root.length = 32)
    (hvalueRoom : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32)
    (husage : usage entries child value < 2 ^ 64)
    (hroot : (branchBuilt entries child value).root ≠ List.replicate 32 0)
    (hkey : nibbles query.key = digit :: tail)
    (hmiss : ¬ (digit < 16 ∧ groupActive entries digit = true)) :
    lookup (branchBuilt entries child value).witness (branchBuilt entries child value).root previous query =
      .ok {
        reference := none, value := none,
        state := if query.accountNodes then (queryStart previous query).touch (branchBuilt entries child value).root "node"
          else queryStart previous query } := by
  apply lookup_branch_miss _ _ (nodeBytes entries child value) (valueReference value)
    (references entries child) digit tail previous query hroot
    (branch_fetch_root entries child value) (nodeBytes_decode entries child value hwidth hvalueRoom husage) hkey
  simp only [references_find, hmiss, ↓reduceIte]

/-- The branch's own value follows the root in the raw witness. An alias with
the root is allowed exactly when their payloads agree; no hash injectivity is
assumed and child-witness aliases occur later than this value object. -/
theorem branch_fetch_value (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Bytes)
    (hbinding : (branchBuilt entries child (some value)).root = Sha256.hash value →
      nodeBytes entries child (some value) = value) :
    fetchObject (branchBuilt entries child (some value)).witness (Sha256.hash value) = .ok value := by
  apply fetchObject_binding
  by_cases he : (branchBuilt entries child (some value)).root = Sha256.hash value
  · have hb := hbinding he
    simp only [branchBuilt] at he
    simp [branchBuilt, hb]
  · change Sha256.hash (nodeBytes entries child (some value)) ≠ Sha256.hash value at he
    simp [branchBuilt, he]

/-- Root-terminal value lookup is fully discharged from serialization and a
local root/value alias binding, with no recursive child semantic premise. -/
theorem branch_lookup_own_value (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Bytes) (previous : Accounting) (query : Query)
    (hwidth : ∀ digit ∈ List.range 16, groupActive entries digit = true → (child digit).root.length = 32)
    (hvalueRoom : value.length < 2 ^ 32) (husage : usage entries child (some value) < 2 ^ 64)
    (hroot : (branchBuilt entries child (some value)).root ≠ List.replicate 32 0)
    (hbinding : (branchBuilt entries child (some value)).root = Sha256.hash value →
      nodeBytes entries child (some value) = value)
    (hkey : nibbles query.key = []) (hmode : query.dereference = true) :
    lookup (branchBuilt entries child (some value)).witness (branchBuilt entries child (some value)).root previous query =
      .ok {
        reference := some { length := value.length, hash := Sha256.hash value }, value := some value,
        state := (if query.accountNodes then
          (queryStart previous query).touch (branchBuilt entries child (some value)).root "node"
          else queryStart previous query).touch (Sha256.hash value) "value" } := by
  exact lookup_branch_empty_value _ _ (nodeBytes entries child (some value)) value
    { length := value.length, hash := Sha256.hash value } (references entries child) previous query hroot
    (branch_fetch_root entries child (some value))
    (nodeBytes_decode entries child (some value) hwidth (fun _ he => by cases he; exact hvalueRoom) husage)
    hkey (branch_fetch_value entries child value hbinding) rfl hmode

/-- The actual parent constructor and actual lookup compose from local child
construction results and the selected child's recursive walk semantics. -/
theorem construct_lookup_child_reference (fuel : Nat) (first second : List Nat × Bytes)
    (rest : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes)
    (digit : Nat) (tail : List Nat) (previous after : Accounting) (query : Query) (reference : Option ValueRef)
    (hshared : (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 = [])
    (hvalue : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd = value)
    (hconstruct : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      childAction fuel (first :: second :: rest) digit = .ok (child digit))
    (hwidth : ∀ digit ∈ List.range 16, groupActive (first :: second :: rest) digit = true →
      (child digit).root.length = 32)
    (hvalueRoom : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32)
    (husage : usage (first :: second :: rest) child value < 2 ^ 64)
    (hroot : (branchBuilt (first :: second :: rest) child value).root ≠ List.replicate 32 0)
    (hkey : nibbles query.key = digit :: tail)
    (hdigit : digit < 16) (hactive : groupActive (first :: second :: rest) digit = true)
    (hchild : walkObjects (branchBuilt (first :: second :: rest) child value).witness query.accountNodes
      (branchBuilt (first :: second :: rest) child value).witness.length
      [(branchBuilt (first :: second :: rest) child value).root] (child digit).root tail
      (if query.accountNodes then
        (queryStart previous query).touch (branchBuilt (first :: second :: rest) child value).root "node"
        else queryStart previous query) = .ok (reference, after))
    (hmode : query.dereference = false) :
    construct (fuel + 1) (first :: second :: rest) = .ok (branchBuilt (first :: second :: rest) child value) ∧
    lookup (branchBuilt (first :: second :: rest) child value).witness
      (branchBuilt (first :: second :: rest) child value).root previous query =
        .ok { reference, value := none, state := after } :=
  ⟨construct_branch_built fuel first second rest child value hshared hvalue hconstruct hwidth hvalueRoom husage,
    branch_lookup_child_reference (first :: second :: rest) child value digit tail previous after query reference
      hwidth hvalueRoom husage hroot hkey hdigit hactive hchild hmode⟩

end Near.TrieBranchConstructionLookup
