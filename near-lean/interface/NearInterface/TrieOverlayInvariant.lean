import NearInterface.TrieOverlay

/-!
# The reachable overlay-key invariant

TrieUpdate's maps are represented as lists, but actual constructors retain at
most one update per key in each overlay. Prospective and committed overlays may
share a key: the prospective update then deliberately takes precedence.
-/
namespace Near.TrieOverlay
open TrieAccounting TrieConstruction

/-- No key occurs twice within either overlay. Cross-overlay overlap is valid. -/
def State.UniqueChanges (state : State) : Prop :=
  (state.prospective.map Prod.fst).Nodup ∧ (state.committed.map Prod.fst).Nodup

private def override (changes : Changes) (key : Bytes) (value : Option Bytes) : Changes :=
  (key, value) :: changes.filter (·.1 != key)

private theorem override_unique (changes : Changes) (key : Bytes) (value : Option Bytes)
    (h : (changes.map Prod.fst).Nodup) : ((override changes key value).map Prod.fst).Nodup := by
  simp only [override, List.map_cons, List.nodup_cons]
  constructor
  · intro hmem
    obtain ⟨⟨oldkey, oldvalue⟩, hfilter, heq⟩ := List.mem_map.mp hmem
    have hne := (List.mem_filter.mp hfilter).2
    simp_all
  · exact List.Pairwise.sublist (List.Sublist.map Prod.fst List.filter_sublist) h

private theorem fold_override_unique (changes updates : Changes)
    (h : (changes.map Prod.fst).Nodup) :
    ((updates.foldl (fun acc (key, value) => override acc key value) changes).map Prod.fst).Nodup := by
  induction updates generalizing changes with
  | nil => exact h
  | cons update updates ih =>
    exact ih _ (override_unique changes update.1 update.2 h)

theorem State.UniqueChanges.set {state : State} (h : state.UniqueChanges) (key value : Bytes) :
    (state.set key value).UniqueChanges := by
  refine ⟨?_, h.2⟩
  exact override_unique state.prospective key (some value) h.1

theorem State.UniqueChanges.remove {state : State} (h : state.UniqueChanges) (key : Bytes) :
    (state.remove key).UniqueChanges := by
  refine ⟨?_, h.2⟩
  exact override_unique state.prospective key none h.1

/-- Runtime receipt commit uses this same fold directly, rather than `step`. -/
theorem State.UniqueChanges.commit {state : State} (h : state.UniqueChanges) :
    ({ state with
      committed := state.prospective.foldl (fun changes (key, value) =>
        (key, value) :: changes.filter (·.1 != key)) state.committed
      prospective := [] } : State).UniqueChanges := by
  exact ⟨List.Pairwise.nil, fold_override_unique state.committed state.prospective h.2⟩

theorem State.UniqueChanges.rollback {state : State} (h : state.UniqueChanges) :
    ({ state with prospective := [] } : State).UniqueChanges := ⟨List.Pairwise.nil, h.2⟩

theorem State.UniqueChanges.withAccounting {state : State} (h : state.UniqueChanges)
    (accounting : TrieAccounting.Accounting) :
    ({ state with accounting } : State).UniqueChanges := h

/-- The sole allocating constructor begins with two empty maps. -/
theorem start_unique (entries : List (Bytes × Bytes)) {state : State}
    (hstart : start entries = .ok state) : state.UniqueChanges := by
  unfold start at hstart
  cases hb : TrieConstruction.build entries with
  | error error => simp only [hb, bind, Except.bind] at hstart; contradiction
  | ok base =>
    simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hstart
    subst state
    exact ⟨List.Pairwise.nil, List.Pairwise.nil⟩

/-- Reference lookup changes accounting only, on both overlay hits and trie reads. -/
theorem getReference_unique {before after : State} (h : before.UniqueChanges)
    (key : Bytes) (accountNodes : Bool) (pointer : Option ValuePointer)
    (hget : getReference before key accountNodes = .ok (after, pointer)) : after.UniqueChanges := by
  unfold getReference at hget
  split at hget
  · cases hget; exact h
  · cases hget; exact h
  · simp only [bind, Except.bind] at hget
    split at hget
    · contradiction
    · cases hget; exact h

/-- Dereferencing preserves both overlays, including when the pointer is on disk. -/
theorem dereference_unique {before after : State} (h : before.UniqueChanges)
    (pointer : ValuePointer) (bytes : Bytes)
    (hread : dereference before pointer = .ok (after, bytes)) : after.UniqueChanges := by
  cases pointer with
  | memory value => cases hread; exact h
  | trie root reference =>
    unfold dereference at hread
    simp only [bind, Except.bind] at hread
    split at hread
    · simp only [pure, Except.pure] at hread
      split at hread
      · contradiction
      · cases hread; exact h
    · contradiction

/-- A proof-local expansion of the private lookup helper in `step`. -/
private def readForInvariant (state : State) (key : Bytes) (accountNodes readValue : Bool) :
    Except String (State × Option (String × ValueRef) × Option Bytes) := do
  let (state, pointer) ← getReference state key accountNodes
  match pointer with
  | none => return (state, none, none)
  | some pointer =>
    if readValue then
      let (state, bytes) ← dereference state pointer
      return (state, some pointer.reference, some bytes)
    else return (state, some pointer.reference, none)

private theorem read_unique {before after : State} (h : before.UniqueChanges)
    (key : Bytes) (accountNodes readValue : Bool) (reference : Option (String × ValueRef))
    (value : Option Bytes)
    (hread : readForInvariant before key accountNodes readValue = .ok (after, reference, value)) :
    after.UniqueChanges := by
  cases hg : getReference before key accountNodes with
  | error error => simp only [readForInvariant, hg, bind, Except.bind] at hread; contradiction
  | ok result =>
    obtain ⟨looked, pointer⟩ := result
    have hu := getReference_unique h key accountNodes pointer hg
    cases pointer with
    | none =>
      simp only [readForInvariant, hg, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hread
      cases hread
      exact hu
    | some pointer =>
      cases readValue with
      | false =>
        simp only [readForInvariant, hg, bind, Except.bind, Bool.false_eq_true, ↓reduceIte,
          pure, Except.pure, Except.ok.injEq] at hread
        cases hread
        exact hu
      | true =>
        cases hd : dereference looked pointer with
        | error error =>
          simp only [readForInvariant, hg, bind, Except.bind, ↓reduceIte, hd] at hread
          contradiction
        | ok result =>
          obtain ⟨readState, bytes⟩ := result
          simp only [readForInvariant, hg, bind, Except.bind, ↓reduceIte, hd,
            pure, Except.pure, Except.ok.injEq] at hread
          cases hread
          exact dereference_unique hu pointer bytes hd

/-- Every successful public operation preserves the map representation
invariant, including commit, rollback, reads, checkpoint and cache reset. -/
theorem step_unique (account : Bytes) (operation : Operation) {before after : State}
    (h : before.UniqueChanges) (observation : Observation)
    (hstep : step account operation before = .ok (after, observation)) : after.UniqueChanges := by
  let current : State := { before with accounting := { seen := before.accounting.seen } }
  have hc : current.UniqueChanges := h
  cases operation with
  | set key value =>
    unfold step at hstep
    simp only [bind, Except.bind, pure, Except.pure] at hstep
    split at hstep
    · contradiction
    · cases hstep
      exact hc.set (contractKey account key) value
  | remove key =>
    cases hstep
    exact hc.remove (contractKey account key)
  | get key accountNodes readValue =>
    change (readForInvariant current (contractKey account key) accountNodes readValue).bind
      (fun (state, reference, value) => .ok
        (state, { kind := "get"
                  rawKey := some (contractKey account key)
                  reference := reference
                  value := value
                  isLookup := true })) = .ok (after, observation) at hstep
    cases hr : readForInvariant current (contractKey account key) accountNodes readValue with
    | error error => simp only [hr, Except.bind] at hstep; contradiction
    | ok result =>
      obtain ⟨state, reference, value⟩ := result
      simp only [hr, Except.bind, Except.ok.injEq] at hstep
      cases hstep
      exact read_unique hc _ _ _ _ _ hr
  | has key =>
    change (readForInvariant current (contractKey account key) false false).bind
      (fun (state, reference, _) => .ok
        (state, { kind := "has"
                  rawKey := some (contractKey account key)
                  present := some reference.isSome })) =
      .ok (after, observation) at hstep
    cases hr : readForInvariant current (contractKey account key) false false with
    | error error => simp only [hr, Except.bind] at hstep; contradiction
    | ok result =>
      obtain ⟨state, reference, value⟩ := result
      simp only [hr, Except.bind, Except.ok.injEq] at hstep
      cases hstep
      exact read_unique hc _ _ _ _ _ hr
  | commit => cases hstep; exact hc.commit
  | rollback => cases hstep; exact hc.rollback
  | resetCache => cases hstep; exact h
  | checkpoint =>
    unfold step at hstep
    simp only [bind, Except.bind] at hstep
    split at hstep
    · split at hstep
      · contradiction
      · cases hstep
        exact ⟨h.1, List.Pairwise.nil⟩
    · contradiction

end Near.TrieOverlay
