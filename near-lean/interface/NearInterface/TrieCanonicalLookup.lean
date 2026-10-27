import NearInterface.TrieEntryDereference
import NearInterface.TrieOverlayLookup

/-! Canonical trie construction closes overlay base lookup and dereferencing.
The sole additional canonical-node condition is reserved-zero exclusion. -/
namespace Near.TrieOverlay
open TrieAccounting TrieConstruction TrieConstructionBranch TrieConstructionRanks
open TrieEntryLookup TrieEntryDereference TrieLeaf

/-- The actual raw construction result has no real node at the reserved empty
root. This is node-only evidence, with no restriction on value-object hashes. -/
def State.NonzeroNodes (state : State) : Prop :=
  ∃ raw, construct (TrieConstructionInvariant.constructionDepth state.entries)
    (state.entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧
    ∀ root rank, NodeOccurs raw root rank → root ≠ List.replicate 32 0

/-- Canonical construction determines the complete actual reference-only base
result, including absence. No base-lookup callback is assumed. -/
theorem baseLookup_canonical (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hnodes : state.NonzeroNodes) :
    ∃ accounting, baseLookup state key accountNodes = .ok {
      reference := (Lookup.first state.entries key).map referenceOf, value := none, state := accounting } := by
  obtain ⟨raw, hc, hz⟩ := hnodes
  obtain ⟨accounting, hr⟩ := build_reference_bytes state.entries state.base raw hcanonical hc hz
    state.accounting { key, accountNodes, dereference := false, resetCache := false } rfl
  refine ⟨accounting, ?_⟩
  simpa only [baseLookup, Lookup.first, Option.map_map, Function.comp_def] using hr

/-- Canonical construction retains and validates the exact first-match base
value. Value fetching needs no node-zero condition or overlay uniqueness. -/
theorem base_fetch_canonical (state : State) (key value : Bytes)
    (hcanonical : build state.entries = .ok state.base)
    (hvalue : Lookup.first state.entries key = some value) :
    fetchObject state.base.witness (Sha256.hash value) = .ok value := by
  obtain ⟨raw, hc, _, _, _⟩ := TrieConstructionInvariant.build_checked state.entries state.base hcanonical
  exact build_value_fetch state.entries state.base raw hcanonical hc key value hvalue

/-- An on-disk pointer obtained for the current canonical base dereferences to
its original value with one exact value touch; the rest of the state is kept. -/
theorem dereference_canonical_value (state : State) (key value : Bytes)
    (hcanonical : build state.entries = .ok state.base)
    (hvalue : Lookup.first state.entries key = some value) :
    dereference state (.trie state.base.root (referenceOf value)) =
      .ok ({ state with accounting := state.accounting.touch (Sha256.hash value) "value" }, value) := by
  have hd := dereference_binding state.base.witness (referenceOf value) value state.accounting
    (base_fetch_canonical state key value hcanonical hvalue) rfl
  simp only [dereference, beq_self_eq_true, ↓reduceIte,
    pure, Except.pure, bind, Except.bind, hd]
  rfl

/-- Actual canonical reference lookup is failure-free for every overlay query,
and its presence agrees with the materialized view. -/
theorem getReference_canonical (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hunique : state.UniqueChanges)
    (hnodes : state.NonzeroNodes) :
    ∃ after pointer, getReference state key accountNodes = .ok (after, pointer) ∧
      after.base = state.base ∧ after.view = state.view ∧
      pointer.isSome = (Lookup.first state.view key).isSome := by
  cases hs : selected state key with
  | some value =>
    cases value with
    | none =>
      have ht := getReference_selected_tombstone state key accountNodes hunique hs
      exact ⟨state, none, ht.1, rfl, rfl, by simp only [ht.2]; rfl⟩
    | some value =>
      have ht := getReference_selected_value state key accountNodes hunique value hs
      exact ⟨state, some (.memory value), ht.1, rfl, rfl, by simp only [ht.2]; rfl⟩
  | none =>
    obtain ⟨accounting, hb⟩ := baseLookup_canonical state key accountNodes hcanonical hnodes
    let result : TrieAccounting.Result := {
      reference := (Lookup.first state.entries key).map referenceOf, value := none, state := accounting }
    refine ⟨lookedState state result, result.reference.map (.trie state.base.root), ?_, rfl, rfl, ?_⟩
    · rw [getReference_eq, hs]
      simp only [hb, bind, Except.bind, pure, Except.pure]
      rfl
    · rw [view_unselected state key hunique hs]
      cases hv : Lookup.first state.entries key <;> simp [result, hv]

/-- The previous presence theorem's base callback is discharged from canonical
construction, retaining its convenient successful-operation API. -/
theorem getReference_presence_canonical (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hunique : state.UniqueChanges)
    (hnodes : state.NonzeroNodes) (after : State) (pointer : Option ValuePointer)
    (hget : getReference state key accountNodes = .ok (after, pointer)) :
    pointer.isSome = (Lookup.first state.view key).isSome := by
  obtain ⟨actual, found, hr, _, _, hp⟩ := getReference_canonical state key accountNodes hcanonical hunique hnodes
  rw [hget] at hr
  cases Except.ok.inj hr
  exact hp

/-- Every returned canonical pointer, including a memory overlay hit, can be
consumed without failure and yields exactly the materialized view's bytes. -/
theorem getReference_dereference_canonical (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hunique : state.UniqueChanges)
    (hnodes : state.NonzeroNodes) (after : State) (pointer : ValuePointer)
    (hget : getReference state key accountNodes = .ok (after, some pointer)) :
    ∃ value finished, Lookup.first state.view key = some value ∧
      dereference after pointer = .ok (finished, value) ∧ finished.base = state.base := by
  rw [getReference_eq] at hget
  cases hs : selected state key with
  | some value =>
    cases value with
    | none => rw [hs] at hget; cases hget
    | some value =>
      rw [hs] at hget
      cases Except.ok.inj hget
      exact ⟨value, state, view_selected state key hunique (some value) hs, rfl, rfl⟩
  | none =>
    rw [hs] at hget
    obtain ⟨accounting, hb⟩ := baseLookup_canonical state key accountNodes hcanonical hnodes
    simp only [hb, bind, Except.bind, pure, Except.pure] at hget
    cases hv : Lookup.first state.entries key with
    | none => simp only [hv, Option.map_none] at hget; cases hget
    | some value =>
      simp only [hv, Option.map_some] at hget
      cases Except.ok.inj hget
      let result : TrieAccounting.Result := {
        reference := some (referenceOf value), value := none, state := accounting }
      have hc : build (lookedState state result).entries = .ok (lookedState state result).base := hcanonical
      have hd := dereference_canonical_value (lookedState state result) key value hc hv
      refine ⟨value, _, ?_, hd, rfl⟩
      rw [view_unselected state key hunique hs, hv]

/-- Complete failure-free read contract for any prospective/committed/base
selection. The returned bytes are fixed by the original materialized view;
there is no assumed successful getReference or dereference outcome. -/
theorem canonical_read (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hunique : state.UniqueChanges)
    (hnodes : state.NonzeroNodes) :
    match Lookup.first state.view key with
    | none => ∃ after, getReference state key accountNodes = .ok (after, none) ∧ after.base = state.base
    | some value => ∃ after pointer finished,
        getReference state key accountNodes = .ok (after, some pointer) ∧
        dereference after pointer = .ok (finished, value) ∧ finished.base = state.base := by
  obtain ⟨after, pointer, hget, hbase, _, hpresence⟩ := getReference_canonical state key accountNodes
    hcanonical hunique hnodes
  cases hv : Lookup.first state.view key with
  | none =>
    rw [hv] at hpresence
    cases pointer with
    | none => exact ⟨after, hget, hbase⟩
    | some pointer => cases hpresence
  | some value =>
    rw [hv] at hpresence
    cases pointer with
    | none => cases hpresence
    | some pointer =>
      obtain ⟨actual, finished, hview, hd, hb⟩ := getReference_dereference_canonical state key accountNodes
        hcanonical hunique hnodes after pointer hget
      rw [hv] at hview
      cases Option.some.inj hview
      exact ⟨after, pointer, finished, hget, hd, hb⟩

end Near.TrieOverlay
