import NearInterface.TrieBranchConstructionLookup
import NearInterface.TrieBranchLookup
import NearInterface.TrieExtension

/-!
# Witness merging preserves successful traversal

Successful first-match fetch bindings are preserved explicitly. Appending
ancestor hashes is safe only when those additional ancestors cannot be fetched
from the source witness. These are sufficient alias conditions, not claims of
hash injectivity or automatic properties of canonical witness merging.
-/
namespace Near.TrieWitnessTransfer
open TrieAccounting TrieLeaf

local macro "unfold_trie_reader" name:ident : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") name.getId.toString
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- Every successful source fetch returns the same bytes in the target. -/
def FetchRefines (source target : Witness) : Prop :=
  ∀ hash bytes, fetchObject source hash = .ok bytes → fetchObject target hash = .ok bytes

/-- Additional ancestors must not alias any fetchable source object. This
conservative condition also excludes unused value-object aliases. -/
def Avoids (source : Witness) (forbidden : List Hash) : Prop :=
  ∀ hash bytes, fetchObject source hash = .ok bytes → hash ∉ forbidden

/-- A successful actual walk transfers to the enlarged witness with arbitrary
extra fuel and safe additional ancestors. The recursive result and complete
accounting state are identical. -/
theorem walk_transfer (source target : Witness) (hfetches : FetchRefines source target)
    (forbidden : List Hash) (havoid : Avoids source forbidden)
    (accountNodes : Bool) (fuel extra : Nat) (ancestors : List Hash) (root : Hash)
    (key : List Nat) (state after : Accounting) (reference : Option ValueRef)
    (hwalk : walkObjects source accountNodes fuel ancestors root key state = .ok (reference, after)) :
    walkObjects target accountNodes (fuel + extra) (ancestors ++ forbidden) root key state =
      .ok (reference, after) := by
  induction fuel generalizing ancestors root key state after reference with
  | zero =>
    unfold walkObjects at hwalk
    unfold_trie_reader walk
    cases hwalk
  | succ fuel ih =>
    rw [Nat.succ_add]
    unfold walkObjects at hwalk ⊢
    unfold_trie_reader walk
    by_cases hz : root == List.replicate 32 0
    · simp only [hz, ↓reduceIte, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hwalk ⊢
      exact hwalk
    · simp only [hz, Bool.false_eq_true, ↓reduceIte] at hwalk ⊢
      cases hc : ancestors.contains root with
      | true =>
        simp only [hc, ↓reduceIte] at hwalk
        cases hwalk
      | false =>
        simp only [hc, Bool.false_eq_true, ↓reduceIte] at hwalk
        cases hf : fetchObject source root with
        | error error =>
          unfold fetchObject at hf
          simp [hf, bind, Except.bind] at hwalk
        | ok bytes =>
          have htarget := hfetches root bytes hf
          have ha := havoid root bytes hf
          have hanc : (ancestors ++ forbidden).contains root = false := by
            have hs : root ∉ ancestors := by simpa using hc
            simp [hs, ha]
          unfold fetchObject at hf htarget
          simp only [hf, bind, Except.bind] at hwalk
          simp only [hanc, Bool.false_eq_true, ↓reduceIte, htarget, bind, Except.bind]
          cases hd : decodeNode bytes with
          | error error => simp [hd] at hwalk
          | ok node =>
            simp only [hd] at hwalk ⊢
            cases node with
            | leaf path value => exact hwalk
            | extension path child =>
              cases hp : path.isPrefixOf key with
              | false =>
                simp only [hp, Bool.false_eq_true, ↓reduceIte] at hwalk ⊢
                exact hwalk
              | true =>
                simp only [hp, ↓reduceIte] at hwalk ⊢
                exact ih (root :: ancestors) child (key.drop path.length) _ after reference hwalk
            | branch value children =>
              cases key with
              | nil => exact hwalk
              | cons digit rest =>
                cases hs : children.find? (·.1 == digit) with
                | none => simp only [hs] at hwalk ⊢; exact hwalk
                | some pair =>
                  obtain ⟨selected, child⟩ := pair
                  simp only [hs] at hwalk ⊢
                  exact ih (root :: ancestors) child rest _ after reference hwalk

/-- Prefix lookup takes precedence; an absent front delegates to the tail. -/
theorem fetch_append (front tail : Witness) (hash : Hash) :
    fetchObject (front ++ tail) hash =
      match (front.find? (fun pair => pair.1 == hash)).map Prod.snd with
      | some bytes => .ok bytes
      | none => fetchObject tail hash := by
  unfold fetchObject
  unfold_trie_reader fetch
  simp only [List.find?_append]
  cases hf : front.find? (fun pair => pair.1 == hash) <;> simp

/-- Successful source bindings cannot be changed by appending later objects. -/
theorem fetch_suffix (source suffix : Witness) : FetchRefines source (source ++ suffix) := by
  intro hash bytes hf
  unfold fetchObject at hf ⊢
  unfold_trie_reader fetch
  cases hs : source.find? (fun pair => pair.1 == hash) with
  | none => simp [hs] at hf
  | some pair =>
    simp only [hs] at hf
    cases hf
    simp [List.find?_append, hs]

/-- Earlier aliases are allowed when their bytes equal the source's actual
first-match binding. This imposes no conditions on irrelevant suffix aliases. -/
def CompatiblePrefix (front source : Witness) : Prop :=
  ∀ hash before bytes, (hash, before) ∈ front → fetchObject source hash = .ok bytes → before = bytes

theorem fetch_merge (front source suffix : Witness) (hcompat : CompatiblePrefix front source) :
    FetchRefines source (front ++ source ++ suffix) := by
  intro hash bytes hf
  rw [List.append_assoc, fetch_append]
  cases hp : front.find? (fun pair => pair.1 == hash) with
  | none =>
    simp only [Option.map_none]
    exact fetch_suffix source suffix hash bytes hf
  | some pair =>
    obtain ⟨found, payload⟩ := pair
    have hm := List.mem_of_find?_eq_some hp
    have he := List.find?_some hp
    have hfound : found = hash := by simpa using he
    subst found
    have hb := hcompat hash payload bytes hm hf
    simp only [Option.map_some, hb]

/-- A key-support exclusion is a convenient sufficient ancestor-safety fact. -/
theorem avoids_of_keys (source : Witness) (forbidden : List Hash)
    (hkeys : ∀ hash ∈ forbidden, hash ∉ source.map Prod.fst) : Avoids source forbidden := by
  intro hash bytes hf hforbidden
  apply hkeys hash hforbidden
  unfold fetchObject at hf
  unfold_trie_reader fetch
  cases hs : source.find? (fun pair => pair.1 == hash) with
  | none => simp [hs] at hf
  | some pair =>
    obtain ⟨found, payload⟩ := pair
    have hm := List.mem_of_find?_eq_some hs
    have he := List.find?_some hs
    have hfound : found = hash := by simpa using he
    subst found
    exact List.mem_map.mpr ⟨(hash, payload), hm, rfl⟩

/-- Transfer isolated successful child traversal into a merged parent witness.
A nonempty front supplies the extra unit of fuel consumed at the parent;
compatible front aliases preserve bytes, and the new parent ancestor must
not alias a fetchable child object. The full accounting result is unchanged. -/
theorem walk_child_merge (front source suffix : Witness)
    (hprefix : 0 < front.length) (hcompat : CompatiblePrefix front source)
    (parent root : Hash) (havoid : Avoids source [parent]) (accountNodes : Bool)
    (key : List Nat) (state after : Accounting) (reference : Option ValueRef)
    (hwalk : walkObjects source accountNodes (source.length + 1) [] root key state = .ok (reference, after)) :
    walkObjects (front ++ source ++ suffix) accountNodes (front ++ source ++ suffix).length
      [parent] root key state = .ok (reference, after) := by
  have hlen : source.length + 1 ≤ (front ++ source ++ suffix).length := by
    simp only [List.length_append]
    omega
  have h := walk_transfer source (front ++ source ++ suffix) (fetch_merge front source suffix hcompat)
    [parent] havoid accountNodes (source.length + 1)
    ((front ++ source ++ suffix).length - (source.length + 1)) [] root key state after reference hwalk
  have hfuel : source.length + 1 + ((front ++ source ++ suffix).length - (source.length + 1)) =
      (front ++ source ++ suffix).length := by omega
  simpa only [hfuel, List.nil_append] using h

/-- An active child's entire raw witness is a contiguous segment of the
parent's raw witness, with at least the parent root object preceding it. -/
theorem branch_child_segment (entries : List (List Nat × Bytes)) (child : Nat → TrieConstruction.Built)
    (value : Option Bytes) (digit : Nat)
    (hactive : digit ∈ TrieBranchConstructionLookup.digits entries) :
    ∃ front suffix, (TrieBranchConstructionLookup.branchBuilt entries child value).witness =
      front ++ (child digit).witness ++ suffix ∧ 0 < front.length := by
  obtain ⟨left, right, hsplit⟩ := List.mem_iff_append.mp hactive
  let parent := TrieBranchConstructionLookup.branchBuilt entries child value
  let front := (parent.root, TrieBranchConstructionLookup.nodeBytes entries child value) ::
    ((match value with | none => [] | some bytes => [(Sha256.hash bytes, bytes)]) ++
      left.flatMap (fun i => (child i).witness))
  refine ⟨front, right.flatMap (fun i => (child i).witness), ?_, by simp [front]⟩
  simp only [TrieBranchConstructionLookup.branchBuilt]
  rw [hsplit, List.flatMap_append, List.flatMap_cons]
  simp only [front, parent, TrieBranchConstructionLookup.branchBuilt, List.cons_append, List.append_assoc]
  rfl

/-- Compatibility with the complete merged object list implies compatibility
with its earlier segment. This is implied by a consistent global hash binding,
but is stated explicitly rather than assuming cryptographic injectivity. -/
def CompatibleObjects (merged source : Witness) : Prop :=
  ∀ hash stored bytes, (hash, stored) ∈ merged → fetchObject source hash = .ok bytes → stored = bytes

/-- Isolated child semantics transfer into the actual raw branch witness.
The parent hash exclusion is conservative; it is not silently derived from
construction or from hash width alone. -/
theorem branch_child_walk (entries : List (List Nat × Bytes)) (child : Nat → TrieConstruction.Built)
    (value : Option Bytes) (digit : Nat) (accountNodes : Bool) (key : List Nat)
    (state after : Accounting) (reference : Option ValueRef)
    (hactive : digit ∈ TrieBranchConstructionLookup.digits entries)
    (hcompat : CompatibleObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness
      (child digit).witness)
    (hancestor : (TrieBranchConstructionLookup.branchBuilt entries child value).root ∉
      (child digit).witness.map Prod.fst)
    (hchild : walkObjects (child digit).witness accountNodes ((child digit).witness.length + 1) []
      (child digit).root key state = .ok (reference, after)) :
    walkObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness accountNodes
      (TrieBranchConstructionLookup.branchBuilt entries child value).witness.length
      [(TrieBranchConstructionLookup.branchBuilt entries child value).root]
      (child digit).root key state = .ok (reference, after) := by
  obtain ⟨front, suffix, hsegment, hpositive⟩ := branch_child_segment entries child value digit hactive
  have hc : CompatiblePrefix front (child digit).witness := by
    intro hash stored bytes hm hf
    apply hcompat hash stored bytes _ hf
    rw [hsegment]
    exact List.mem_append_left _ (List.mem_append_left _ hm)
  have ha : Avoids (child digit).witness [(TrieBranchConstructionLookup.branchBuilt entries child value).root] :=
    avoids_of_keys _ _ (by intro hash hm; simpa only [List.mem_singleton.mp hm] using hancestor)
  have ht := walk_child_merge front (child digit).witness suffix hpositive hc
    (TrieBranchConstructionLookup.branchBuilt entries child value).root (child digit).root ha
    accountNodes key state after reference hchild
  simpa only [← hsegment] using ht

/-- Lookup through the constructed parent now needs only an isolated child
walk. The former full-parent-witness callback is discharged by actual witness
segment transfer, fuel monotonicity and explicit binding/ancestor conditions. -/
theorem branch_lookup_isolated_child (entries : List (List Nat × Bytes)) (child : Nat → TrieConstruction.Built)
    (value : Option Bytes) (digit : Nat) (tail : List Nat) (previous after : Accounting)
    (query : Query) (reference : Option ValueRef)
    (hwidth : ∀ digit ∈ List.range 16, TrieBitmap.groupActive entries digit = true → (child digit).root.length = 32)
    (hvalueRoom : ∀ bytes, value = some bytes → bytes.length < 2 ^ 32)
    (husage : TrieBranchConstructionLookup.usage entries child value < 2 ^ 64)
    (hroot : (TrieBranchConstructionLookup.branchBuilt entries child value).root ≠ List.replicate 32 0)
    (hkey : nibbles query.key = digit :: tail)
    (hdigit : digit < 16) (hactive : TrieBitmap.groupActive entries digit = true)
    (hcompat : CompatibleObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness
      (child digit).witness)
    (hancestor : (TrieBranchConstructionLookup.branchBuilt entries child value).root ∉
      (child digit).witness.map Prod.fst)
    (hchild : walkObjects (child digit).witness query.accountNodes ((child digit).witness.length + 1) []
      (child digit).root tail
      (if query.accountNodes then
        (queryStart previous query).touch (TrieBranchConstructionLookup.branchBuilt entries child value).root "node"
        else queryStart previous query) = .ok (reference, after))
    (hmode : query.dereference = false) :
    lookup (TrieBranchConstructionLookup.branchBuilt entries child value).witness
      (TrieBranchConstructionLookup.branchBuilt entries child value).root previous query =
      .ok { reference, value := none, state := after } := by
  apply TrieBranchConstructionLookup.branch_lookup_child_reference entries child value digit tail previous after
    query reference hwidth hvalueRoom husage hroot hkey hdigit hactive _ hmode
  apply branch_child_walk entries child value digit query.accountNodes tail _ after reference
    _ hcompat hancestor hchild
  simp [TrieBranchConstructionLookup.digits, hdigit, hactive]

/-- Ordinary object-map consistency; equal hashes may repeat only with equal
bytes. This is a concrete binding property, not a cryptographic axiom. -/
def Consistent (witness : Witness) : Prop :=
  ∀ hash first second, (hash, first) ∈ witness → (hash, second) ∈ witness → first = second

theorem fetch_mem (witness : Witness) (hash : Hash) (bytes : Bytes)
    (hfetch : fetchObject witness hash = .ok bytes) : (hash, bytes) ∈ witness := by
  unfold fetchObject at hfetch
  unfold_trie_reader fetch
  cases hf : witness.find? (fun pair => pair.1 == hash) with
  | none => simp [hf] at hfetch
  | some pair =>
    obtain ⟨found, payload⟩ := pair
    have hm := List.mem_of_find?_eq_some hf
    have he := List.find?_some hf
    have hfound : found = hash := by simpa using he
    subst found
    simp only [hf, Except.ok.injEq] at hfetch
    subst payload
    exact hm

theorem compatible_of_consistent (merged source : Witness) (hconsistent : Consistent merged)
    (hsubset : ∀ object ∈ source, object ∈ merged) : CompatibleObjects merged source := by
  intro hash stored bytes hm hf
  exact hconsistent hash stored bytes hm (hsubset (hash, bytes) (fetch_mem source hash bytes hf))

/-- The real branch-witness concatenation supplies source inclusion, so a
single consistent merged hash map discharges every earlier-alias obligation. -/
theorem branch_compatible (entries : List (List Nat × Bytes)) (child : Nat → TrieConstruction.Built)
    (value : Option Bytes) (digit : Nat)
    (hactive : digit ∈ TrieBranchConstructionLookup.digits entries)
    (hconsistent : Consistent (TrieBranchConstructionLookup.branchBuilt entries child value).witness) :
    CompatibleObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness (child digit).witness := by
  apply compatible_of_consistent _ _ hconsistent
  obtain ⟨front, suffix, hsegment, _⟩ := branch_child_segment entries child value digit hactive
  intro object hm
  rw [hsegment]
  exact List.mem_append_left _ (List.mem_append_right _ hm)

end Near.TrieWitnessTransfer
