import NearInterface.TrieWitnessTransfer

/-!
# Successful construction validates witness bindings

The public builder checks every repeated object hash before deduplicating.
Successful checking therefore supplies binding consistency without assuming
hash injectivity. This does not show that a node hash is nonzero or that a
parent hash is absent from its child's node support.
-/
namespace Near.TrieConstructionInvariant
open TrieAccounting TrieConstruction TrieWitnessTransfer

/-- The actual public builder's object-checking loop body. -/
def checkStep (object : Hash × Bytes) (unique : Witness) : Except String (ForInStep Witness) := do
  match unique.find? (·.1 == object.1) with
  | none => return .yield (unique ++ [object])
  | some (_, previous) =>
    if previous != object.2 then throw "trie object hash collision"
    return .yield unique

/-- The collision check and deduplication performed after recursive construction. -/
def checkObjects (objects unique : Witness) : Except String Witness :=
  forIn objects unique checkStep

private theorem found_binding (unique : Witness) (hash : Hash) (pair : Hash × Bytes)
    (hf : unique.find? (·.1 == hash) = some pair) : pair ∈ unique ∧ pair.1 = hash := by
  exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

private theorem absent_key (unique : Witness) (hash : Hash)
    (hf : unique.find? (·.1 == hash) = none) :
    ∀ bytes, (hash, bytes) ∉ unique := by
  intro bytes hm
  have ht := List.find?_eq_none.mp hf (hash, bytes) hm
  simp at ht

/-- A successful insertion preserves consistency and retains both the prior
objects and the newly checked object. -/
theorem checkStep_ok (object : Hash × Bytes) (unique after : Witness)
    (hc : Consistent unique) (hr : checkStep object unique = .ok (.yield after)) :
    Consistent after ∧ (∀ pair ∈ unique, pair ∈ after) ∧ object ∈ after := by
  obtain ⟨hash, bytes⟩ := object
  unfold checkStep at hr
  cases hf : unique.find? (·.1 == hash) with
  | none =>
    simp only [hf, pure, Except.pure, Except.ok.injEq, ForInStep.yield.injEq] at hr
    subst after
    refine ⟨?_, fun pair hm => List.mem_append_left _ hm, by simp⟩
    intro key first second hfirst hsecond
    have ha := absent_key unique hash hf
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq] at hfirst hsecond
    rcases hfirst with hm | ⟨he, hb⟩
    · rcases hsecond with hn | ⟨he, hb⟩
      · exact hc key first second hm hn
      · subst key; exact False.elim (ha first hm)
    · subst key
      rcases hsecond with hn | ⟨_, hs⟩
      · exact False.elim (ha second hn)
      · exact hb.trans hs.symm
  | some pair =>
    obtain ⟨found, previous⟩ := pair
    have hb := found_binding unique hash (found, previous) hf
    have he : found = hash := hb.2
    subst found
    simp only [hf] at hr
    by_cases heq : previous = bytes
    · subst previous
      simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure,
        Except.ok.injEq, ForInStep.yield.injEq] at hr
      subst after
      exact ⟨hc, fun pair hm => hm, hb.1⟩
    · simp only [show (previous != bytes) = true by simp [heq], ↓reduceIte] at hr
      change Except.error _ = Except.ok _ at hr
      cases hr

/-- Success of the whole real loop forces all original object bindings to
coexist in one consistent output. Thus conflicting aliases cannot be hidden
by dropping later duplicates. -/
theorem checkObjects_ok (objects unique after : Witness)
    (hc : Consistent unique) (hr : checkObjects objects unique = .ok after) :
    Consistent after ∧ (∀ pair ∈ unique ++ objects, pair ∈ after) := by
  induction objects generalizing unique with
  | nil =>
    simp only [checkObjects, List.forIn_nil, pure, Except.pure, Except.ok.injEq] at hr
    subst after
    exact ⟨hc, by simp⟩
  | cons object objects ih =>
    unfold checkObjects at hr
    rw [List.forIn_cons] at hr
    cases hs : checkStep object unique with
    | error error => simp [hs, bind, Except.bind] at hr
    | ok step =>
      cases step with
      | done done =>
        unfold checkStep at hs
        split at hs
        · simp [pure, Except.pure] at hs
        · split at hs
          · change Except.error _ = Except.ok _ at hs
            cases hs
          · change (Except.ok (ForInStep.yield unique) : Except String _) = Except.ok (ForInStep.done done) at hs
            cases hs
      | yield next =>
        simp only [hs, bind, Except.bind] at hr
        have hnext := checkStep_ok object unique next hc hs
        have ht := ih next hnext.1 hr
        refine ⟨ht.1, ?_⟩
        intro pair hm
        simp only [List.mem_append, List.mem_cons] at hm
        rcases hm with hm | he | hm
        · exact ht.2 pair (List.mem_append_left _ (hnext.2.1 pair hm))
        · subst pair; exact ht.2 object (List.mem_append_left _ hnext.2.2)
        · exact ht.2 pair (List.mem_append_right _ hm)

/-- Successful collision checking validates the original raw witness itself. -/
theorem checkObjects_consistent (objects after : Witness)
    (hr : checkObjects objects [] = .ok after) :
    Consistent objects ∧ Consistent after ∧ FetchRefines objects after := by
  have ht := checkObjects_ok objects [] after (by intro _ _ _ h; cases h) hr
  have hsub : ∀ pair ∈ objects, pair ∈ after := by simpa using ht.2
  refine ⟨?_, ht.1, ?_⟩
  · intro hash first second hf hs
    exact ht.1 hash first second (hsub _ hf) (hsub _ hs)
  · intro hash bytes hf
    apply TrieLeaf.fetchObject_binding
    have hm := hsub _ (fetch_mem objects hash bytes hf)
    have hfind : ∃ pair, after.find? (·.1 == hash) = some pair := by
      cases he : after.find? (·.1 == hash) with
      | none => exact False.elim (absent_key after hash he bytes hm)
      | some pair => exact ⟨pair, rfl⟩
    obtain ⟨pair, hp⟩ := hfind
    have hb := found_binding after hash pair hp
    have he : pair = (hash, bytes) := by
      apply Prod.ext hb.2
      exact ht.1 hash pair.2 bytes (by simpa only [← hb.2] using hb.1) hm
    simp only [hp, he, Option.map_some]

/-- The depth and nibble conversion used by the actual public builder. -/
def constructionDepth (entries : List (Bytes × Bytes)) : Nat :=
  (entries.map fun (key, value) => (nibbles key, value)).foldl
    (fun n entry => max n entry.1.length) 0 + 1

/-- Successful public construction exposes its actual raw recursive result and
its successful collision check. No recursive lookup callback is assumed. -/
theorem build_checked (entries : List (Bytes × Bytes)) (built : Built)
    (hbuild : build entries = .ok built) :
    ∃ raw, TrieConstructionBranch.construct (constructionDepth entries)
        (entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧
      checkObjects raw.witness [] = .ok built.witness ∧
      built.root = raw.root ∧ built.memoryUsage = raw.memoryUsage := by
  change (if (entries.map Prod.fst).eraseDups.length != (entries.map Prod.fst).length then
      .error "duplicate trie entry"
    else if entries.any (fun (key, value) => key.length ≥ 2 ^ 32 || value.length ≥ 2 ^ 32) then
      .error "trie key or value exceeds u32"
    else do
      let raw ← TrieConstructionBranch.construct (constructionDepth entries)
        (entries.map fun (key, value) => (nibbles key, value))
      let unique ← checkObjects raw.witness []
      pure { raw with witness := unique }) = .ok built at hbuild
  split at hbuild
  · cases hbuild
  · split at hbuild
    · cases hbuild
    · cases hc : TrieConstructionBranch.construct (constructionDepth entries)
          (entries.map fun (key, value) => (nibbles key, value)) with
      | error error => simp only [hc, bind, Except.bind] at hbuild; cases hbuild
      | ok raw =>
        simp only [hc, bind, Except.bind] at hbuild
        cases hu : checkObjects raw.witness [] with
        | error error => simp [hu] at hbuild
        | ok unique =>
          simp only [hu, pure, Except.pure, Except.ok.injEq] at hbuild
          subst built
          exact ⟨raw, rfl, hu, rfl, rfl⟩

/-- Actual successful build validates both its raw construction witness and
its public deduplicated witness, preserving all original first-match fetches. -/
theorem build_consistent (entries : List (Bytes × Bytes)) (built : Built)
    (hbuild : build entries = .ok built) :
    Consistent built.witness ∧ ∃ raw,
      TrieConstructionBranch.construct (constructionDepth entries)
        (entries.map fun (key, value) => (nibbles key, value)) = .ok raw ∧
      Consistent raw.witness ∧ FetchRefines raw.witness built.witness ∧
      built.root = raw.root ∧ built.memoryUsage = raw.memoryUsage := by
  obtain ⟨raw, hc, hr, hroot, husage⟩ := build_checked entries built hbuild
  have ht := checkObjects_consistent raw.witness built.witness hr
  exact ⟨ht.2.1, raw, hc, ht.1, ht.2.2, hroot, husage⟩

/-- Every isolated child of a successfully checked raw branch automatically
has compatible bindings in the full branch witness. The constructor's own
collision validation discharges the former alias-consistency premise. -/
theorem checked_branch_compatible (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (after : Witness) (digit : Nat)
    (hcheck : checkObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness [] = .ok after)
    (hactive : digit ∈ TrieBranchConstructionLookup.digits entries) :
    CompatibleObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness
      (child digit).witness := by
  exact branch_compatible entries child value digit hactive (checkObjects_consistent _ _ hcheck).1

/-- Once checking succeeds, only ancestor separation remains for transfer of
an isolated child walk; hash-binding compatibility is derived by the loop. -/
theorem checked_branch_child_walk (entries : List (List Nat × Bytes)) (child : Nat → Built)
    (value : Option Bytes) (checked : Witness) (digit : Nat) (accountNodes : Bool) (key : List Nat)
    (state after : Accounting) (reference : Option ValueRef)
    (hcheck : checkObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness [] = .ok checked)
    (hactive : digit ∈ TrieBranchConstructionLookup.digits entries)
    (hancestor : (TrieBranchConstructionLookup.branchBuilt entries child value).root ∉
      (child digit).witness.map Prod.fst)
    (hchild : TrieLeaf.walkObjects (child digit).witness accountNodes ((child digit).witness.length + 1) []
      (child digit).root key state = .ok (reference, after)) :
    TrieLeaf.walkObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness accountNodes
      (TrieBranchConstructionLookup.branchBuilt entries child value).witness.length
      [(TrieBranchConstructionLookup.branchBuilt entries child value).root]
      (child digit).root key state = .ok (reference, after) := by
  exact branch_child_walk entries child value digit accountNodes key state after reference hactive
    (checked_branch_compatible entries child value checked digit hcheck hactive) hancestor hchild

/-- An independently established actual recursive construction equation can
be connected directly to public build, without exposing a checker premise. -/
theorem build_raw_checked (entries : List (Bytes × Bytes)) (built raw : Built)
    (hbuild : build entries = .ok built)
    (hconstruct : TrieConstructionBranch.construct (constructionDepth entries)
      (entries.map fun (key, value) => (nibbles key, value)) = .ok raw) :
    checkObjects raw.witness [] = .ok built.witness ∧ Consistent raw.witness ∧
      FetchRefines raw.witness built.witness := by
  obtain ⟨other, hc, hr, _, _⟩ := build_checked entries built hbuild
  rw [hconstruct] at hc
  cases Except.ok.inj hc
  have ht := checkObjects_consistent raw.witness built.witness hr
  exact ⟨hr, ht.1, ht.2.2⟩

/-- Public build success plus the local actual branch-construction equation
entails every selected child's binding compatibility, with no cryptographic
premise and no complete lookup premise. -/
theorem build_branch_compatible (rawEntries : List (Bytes × Bytes)) (built : Built)
    (entries : List (List Nat × Bytes)) (child : Nat → Built) (value : Option Bytes) (digit : Nat)
    (hbuild : build rawEntries = .ok built)
    (hconstruct : TrieConstructionBranch.construct (constructionDepth rawEntries)
      (rawEntries.map fun (key, bytes) => (nibbles key, bytes)) =
        .ok (TrieBranchConstructionLookup.branchBuilt entries child value))
    (hactive : digit ∈ TrieBranchConstructionLookup.digits entries) :
    CompatibleObjects (TrieBranchConstructionLookup.branchBuilt entries child value).witness
      (child digit).witness := by
  exact branch_compatible entries child value digit hactive
    (build_raw_checked rawEntries built _ hbuild hconstruct).2.1

end Near.TrieConstructionInvariant
