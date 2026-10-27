import NearInterface.TrieEntryLookup

/-! Exact value dereferencing for the actual public trie construction. -/
namespace Near.TrieEntryDereference
open TrieAccounting TrieConstruction TrieSerialization TrieConstructionBranch
open TrieBranchConstructionLookup TrieConstructionRanks TrieRankedLookup TrieReadableConstruction
open TrieEntryLookup TrieLeaf TrieWitnessTransfer

local macro "unfold_construct" : tactic => do
  let actual := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieConstruction 0) "Near") "TrieConstruction") "construct"
  `(tactic| unfold $(Lean.mkIdent actual) at *)

/-- Successful recursive construction retains the value selected by independent
first-match input lookup. Later duplicate-key values are not required to remain. -/
theorem construct_value_retained (fuel : Nat) (entries : List (List Nat × Bytes)) (built : Built)
    (hv : ValidEntries entries) (hr : construct fuel entries = .ok built)
    (key : List Nat) (value : Bytes) (hvalue : entryValue entries key = some value) :
    (Sha256.hash value, value) ∈ built.witness := by
  induction fuel generalizing entries built key value with
  | zero =>
    unfold construct at hr
    unfold_construct
    cases hr
  | succ fuel ih =>
    cases entries with
    | nil => cases hvalue
    | cons first rest =>
      cases rest with
      | nil =>
        obtain ⟨path, before⟩ := first
        change (if (encodePath true path).length ≥ 2 ^ 32 then
          .error "trie compact path exceeds u32" else
          finish ([0] ++ vectorBytes (encodePath true path) ++ valueRefBytes before)
            (100 + 2 * (encodePath true path).length + before.length) [(Sha256.hash before, before)]) = .ok built at hr
        split at hr
        · cases hr
        · have hm := entryValue_mem [(path, before)] key value hvalue
          have he := List.mem_singleton.mp hm
          have hval : value = before := congrArg Prod.snd he
          subst value
          exact finish_objects_subset _ _ _ _ hr _ List.mem_cons_self
      | cons second rest =>
        rw [construct_many] at hr
        dsimp only at hr
        split at hr
        · cases hc : construct fuel ((first :: second :: rest).map fun (key, value) =>
              (key.drop ((second :: rest).foldl (fun path entry => commonPath path entry.1) first.1).length, value)) with
          | error error => simp only [hc, bind, Except.bind] at hr; cases hr
          | ok child =>
            simp only [hc, bind, Except.bind] at hr
            split at hr
            · change Except.error _ = Except.ok _ at hr; cases hr
            · have hp := sharedPath_front (second :: rest) first.1
              have hall : ∀ entry ∈ first :: second :: rest,
                  (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 <+: entry.1 := by
                intro entry hm
                rcases List.mem_cons.mp hm with he | hm
                · subst entry; exact hp.1
                · exact hp.2 entry hm
              have hk : (second :: rest).foldl (fun path entry => commonPath path entry.1) first.1 <+: key :=
                hall (key, value) (entryValue_mem _ key value hvalue)
              have hd := entryValue_drop (first :: second :: rest) _ key hall hk
              rw [hvalue] at hd
              have hm := ih _ child (dropped_valid _ _ hv) hc _ value hd
              exact finish_objects_subset _ _ _ _ hr _ hm
        · cases hl : branchLoop fuel (first :: second :: rest) with
          | error error => simp only [hl, bind, Except.bind] at hr; cases hr
          | ok acc =>
            obtain ⟨child, hchild⟩ := branchLoop_children fuel (first :: second :: rest) acc hl
            have he := branchLoop_contract fuel (first :: second :: rest) child hchild
            rw [hl] at he
            have heq := Except.ok.inj he
            subst acc
            simp only [hl, bind, Except.bind] at hr
            cases key with
            | nil =>
              have hfind : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd = some value :=
                (entryValue_empty _).trans hvalue
              rw [hfind] at hr
              exact finish_objects_subset _ _ _ _ hr _ List.mem_cons_self
            | cons digit tail =>
              have hm : digit ∈ digits (first :: second :: rest) := by
                by_cases hm : digit ∈ digits (first :: second :: rest)
                · exact hm
                · have hn := entryValue_unselected _ digit tail hv hm
                  rw [hvalue] at hn
                  cases hn
              have hdigit : digit ∈ List.range 16 ∧ TrieBitmap.groupActive (first :: second :: rest) digit = true := by
                simpa only [digits, List.mem_filter] using hm
              have hg := entryValue_group (first :: second :: rest) digit tail
              rw [hvalue] at hg
              have hretained := ih _ (child digit) (group_valid _ digit hv) (hchild digit hdigit.1 hdigit.2) tail value hg
              have hw : (Sha256.hash value, value) ∈
                  (digits (first :: second :: rest)).flatMap (fun digit => (child digit).witness) :=
                List.mem_flatMap.mpr ⟨digit, hm, hretained⟩
              cases hfind : ((first :: second :: rest).find? (fun entry => entry.1.isEmpty)).map Prod.snd with
              | none =>
                rw [hfind] at hr
                exact finish_objects_subset _ _ _ _ hr _ hw
              | some before =>
                rw [hfind] at hr
                exact finish_objects_subset _ _ _ _ hr _ (List.mem_cons_of_mem _ hw)

/-- The public collision-checking loop retains the selected original bytes. -/
theorem build_value_retained (entries : List (Bytes × Bytes)) (built raw : Built)
    (hb : build entries = .ok built)
    (hc : construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw)
    (key : Bytes) (value : Bytes)
    (hvalue : (entries.find? (fun entry => entry.1 == key)).map Prod.snd = some value) :
    (Sha256.hash value, value) ∈ built.witness := by
  have hv : entryValue (entries.map fun (path, value) => (nibbles path, value)) (nibbles key) = some value := by
    rw [entryValue_nibbles]
    exact hvalue
  have hm := construct_value_retained _ _ raw (build_inputs_valid entries built hb) hc _ value hv
  have hcheck := (TrieConstructionInvariant.build_raw_checked entries built raw hb hc).1
  have hs := TrieConstructionInvariant.checkObjects_ok raw.witness [] built.witness
    (by intro _ _ _ h; cases h) hcheck
  exact hs.2 _ (by simpa only [List.nil_append] using hm)

/-- Consistent repeated object bindings preserve an existing member's bytes
under the actual first-match fetch operation. -/
theorem fetch_consistent_member (witness : Witness) (hc : Consistent witness) (hash : Hash) (bytes : Bytes)
    (hm : (hash, bytes) ∈ witness) : fetchObject witness hash = .ok bytes := by
  apply fetchObject_binding
  cases hf : witness.find? (·.1 == hash) with
  | none =>
    have h := List.find?_eq_none.mp hf (hash, bytes) hm
    simp at h
  | some pair =>
    have hm' := List.mem_of_find?_eq_some hf
    have he : pair.1 = hash := by simpa using List.find?_some hf
    have hb : pair.2 = bytes := hc hash _ _ (by simpa only [← he] using hm') hm
    simp [hb]

/-- Exact value fetching follows actual build's retained object and collision
validation. No reserved-zero premise is needed for value-object fetching. -/
theorem build_value_fetch (entries : List (Bytes × Bytes)) (built raw : Built)
    (hb : build entries = .ok built)
    (hc : construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw)
    (key : Bytes) (value : Bytes)
    (hvalue : (entries.find? (fun entry => entry.1 == key)).map Prod.snd = some value) :
    fetchObject built.witness (Sha256.hash value) = .ok value := by
  exact fetch_consistent_member built.witness (TrieConstructionInvariant.build_consistent entries built hb).1
    _ _ (build_value_retained entries built raw hb hc key value hvalue)

/-- Recover the actual walk from a reference-only lookup, before its optional
value dereference. This helper is applied below to a proved public result. -/
theorem reference_lookup_walk (witness : Witness) (root : Hash) (previous : Accounting) (query : Query)
    (reference : Option ValueRef) (after : Accounting)
    (hr : lookup witness root previous { query with dereference := false } = .ok {
      reference, value := none, state := after }) :
    walkObjects witness query.accountNodes (witness.length + 1) [] root (nibbles query.key)
      (queryStart previous query) = .ok (reference, after) := by
  cases hw : walkObjects witness query.accountNodes (witness.length + 1) [] root (nibbles query.key)
      (queryStart previous query) with
  | error error =>
    unfold walkObjects queryStart at hw
    simp only [lookup, hw, bind, Except.bind] at hr
    cases hr
  | ok pair =>
    obtain ⟨found, state⟩ := pair
    have ht := hw
    unfold walkObjects queryStart at ht
    simp only [lookup, ht, bind, Except.bind] at hr
    cases found with
    | none =>
      simp only [pure, Except.pure] at hr
      have he := Except.ok.inj hr
      have hreference := congrArg Result.reference he
      have hstate := congrArg Result.state he
      cases hreference
      cases hstate
      rfl
    | some found =>
      simp only [Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at hr
      have he := Except.ok.inj hr
      have hreference := congrArg Result.reference he
      have hstate := congrArg Result.state he
      cases hreference
      cases hstate
      rfl

/-- The actual final value touch, kept independent of proof hypotheses. -/
def dereferencedState (value : Option Bytes) (before : Accounting) : Accounting :=
  match value with | none => before | some bytes => before.touch (Sha256.hash bytes) "value"

/-- Turning on dereferencing returns exactly the selected bytes and performs
one actual value touch when present. Absence performs no value fetch or touch. -/
theorem lookup_dereference_from_walk (witness : Witness) (root : Hash) (previous : Accounting) (query : Query)
    (value : Option Bytes) (before : Accounting)
    (hw : walkObjects witness query.accountNodes (witness.length + 1) [] root (nibbles query.key)
      (queryStart previous query) = .ok (value.map referenceOf, before))
    (hf : ∀ bytes, value = some bytes → fetchObject witness (Sha256.hash bytes) = .ok bytes)
    (hmode : query.dereference = true) :
    lookup witness root previous query = .ok {
      reference := value.map referenceOf, value,
      state := dereferencedState value before } := by
  unfold walkObjects queryStart at hw
  simp only [lookup, hw, bind, Except.bind]
  cases value with
  | none => rfl
  | some bytes =>
    have hd := dereference_binding witness (referenceOf bytes) bytes before (hf bytes rfl) rfl
    simp only [Option.map_some, hmode, ↓reduceIte]
    change (do let (bytes, state) ← dereference witness (referenceOf bytes) before
               pure ({ reference := some (referenceOf _), value := some bytes, state } : Result)) = _
    rw [hd]
    rfl

/-- Full actual public lookup returns the original first-match value bytes.
Construction, retained objects, collision validation, recursive traversal and
default-fuel compaction are derived; only node-zero exclusion stays explicit. -/
theorem build_lookup_bytes (entries : List (Bytes × Bytes)) (built raw : Built)
    (hb : build entries = .ok built)
    (hc : construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw)
    (hz : ∀ root rank, NodeOccurs raw root rank → root ≠ List.replicate 32 0)
    (previous : Accounting) (query : Query) (hmode : query.dereference = true) :
    ∃ after, lookup built.witness built.root previous query = .ok {
      reference := (entries.find? (fun entry => entry.1 == query.key)).map (fun entry => referenceOf entry.2),
      value := (entries.find? (fun entry => entry.1 == query.key)).map Prod.snd, state := after } := by
  let value := (entries.find? (fun entry => entry.1 == query.key)).map Prod.snd
  obtain ⟨before, hr⟩ := build_reference_bytes entries built raw hb hc hz previous
    { query with dereference := false } rfl
  have href : lookup built.witness built.root previous { query with dereference := false } =
      .ok { reference := value.map referenceOf, value := none, state := before } := by
    simpa only [value, Option.map_map, Function.comp_def] using hr
  have hw := reference_lookup_walk built.witness built.root previous query (value.map referenceOf) before href
  have hf : ∀ bytes, value = some bytes → fetchObject built.witness (Sha256.hash bytes) = .ok bytes := by
    intro bytes hv
    exact build_value_fetch entries built raw hb hc query.key bytes hv
  have hd := lookup_dereference_from_walk built.witness built.root previous query value before hw hf hmode
  refine ⟨dereferencedState value before, ?_⟩
  simpa only [value, Option.map_map, Function.comp_def] using hd

/-- Public construction exposes its actual raw result; full lookup requires
only the separate nonzero-node predicate for that actual result. -/
theorem build_lookup_bytes_exists (entries : List (Bytes × Bytes)) (built : Built)
    (hb : build entries = .ok built) :
    ∃ raw, construct (TrieConstructionInvariant.constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧
      ∀ previous query, query.dereference = true →
        (∀ root rank, NodeOccurs raw root rank → root ≠ List.replicate 32 0) →
        ∃ after, lookup built.witness built.root previous query = .ok {
          reference := (entries.find? (fun entry => entry.1 == query.key)).map (fun entry => referenceOf entry.2),
          value := (entries.find? (fun entry => entry.1 == query.key)).map Prod.snd, state := after } := by
  obtain ⟨raw, hc, _, _, _⟩ := TrieConstructionInvariant.build_checked entries built hb
  exact ⟨raw, hc, fun previous query hm hz => build_lookup_bytes entries built raw hb hc hz previous query hm⟩

end Near.TrieEntryDereference
