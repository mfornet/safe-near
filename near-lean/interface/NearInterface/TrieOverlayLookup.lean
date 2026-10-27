import NearInterface.TrieOverlayInvariant

/-!
# Overlay lookup agrees with the materialized view

The list fold used by `State.view` agrees with first-match lookup when each
overlay has unique keys. This file separates that map-representation fact
from canonical on-disk trie correctness: no-overlay reads retain an explicit
premise about the underlying `TrieAccounting.lookup` primitive.
-/
namespace Near.TrieOverlay
open TrieAccounting TrieConstruction

namespace Lookup
variable {K V : Type} [BEq K] [LawfulBEq K]

/-- First-match association-list lookup, matching the runtime's overlay search. -/
def first (entries : List (K × V)) (key : K) : Option V :=
  (entries.find? (·.1 == key)).map Prod.snd

/-- Install or remove one cell, retaining all unrelated records. -/
def update (entries : List (K × V)) (key : K) (value : Option V) : List (K × V) :=
  let remaining := entries.filter (·.1 != key)
  match value with
  | none => remaining
  | some value => (key, value) :: remaining

/-- The materialization fold used by the trie view. -/
def apply (entries : List (K × V)) (changes : List (K × Option V)) : List (K × V) :=
  changes.foldl (fun entries (key, value) => update entries key value) entries

theorem first_cons (key : K) (value : V) (entries : List (K × V)) (query : K) :
    first ((key, value) :: entries) query = if key == query then some value else first entries query := by
  simp only [first, List.find?_cons]
  split <;> simp_all

theorem first_filter (entries : List (K × V)) (key query : K) :
    first (entries.filter (·.1 != key)) query =
      if key == query then none else first entries query := by
  classical
  induction entries with
  | nil => simp [first]
  | cons entry entries ih =>
      obtain ⟨old, value⟩ := entry
      by_cases hd : old = key <;> by_cases hq : old = query <;> by_cases he : key = query
      all_goals simp_all [first, beq_iff_eq]

theorem first_update (entries : List (K × V)) (key query : K) (value : Option V) :
    first (update entries key value) query =
      if key == query then value else first entries query := by
  cases he : (key == query) <;> cases value <;> simp [update, first_cons, first_filter, he]

theorem first_none (entries : List (K × V)) (query : K)
    (h : query ∉ entries.map Prod.fst) : first entries query = none := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
      obtain ⟨key, value⟩ := entry
      simp only [List.map_cons, List.mem_cons, not_or] at h
      have hfalse : (key == query) = false := beq_eq_false_iff_ne.mpr (Ne.symm h.1)
      simp only [first_cons, hfalse, Bool.false_eq_true, ↓reduceIte, ih h.2]

/-- With unique update keys, last-wins materialization and first-match overlay
selection coincide. Base records need not be unique for this lookup fact. -/
theorem first_apply (entries : List (K × V)) (changes : List (K × Option V))
    (query : K) (h : (changes.map Prod.fst).Nodup) :
    first (apply entries changes) query =
      match first changes query with
      | some value => value
      | none => first entries query := by
  classical
  induction changes generalizing entries with
  | nil => rfl
  | cons change changes ih =>
      obtain ⟨key, value⟩ := change
      simp only [List.map_cons, List.nodup_cons] at h
      change first (apply (update entries key value) changes) query = _
      rw [ih _ h.2]
      by_cases heq : key = query
      · subst query
        rw [first_none changes key h.1]
        simp [first_cons, first_update]
      · simp [first_cons, first_update, heq]

end Lookup

/-- Overlay selection keeps the prospective map's precedence. A tombstone
is `some none`, distinct from absence from both overlays. -/
def selected (state : State) (key : Bytes) : Option (Option Bytes) :=
  (Lookup.first state.prospective key).orElse fun _ => Lookup.first state.committed key

-- The concrete fold's generated pair matcher is not definitionally equal
-- to the generic one until its argument is split. Unfold just this transparent
-- helper, then prove the fold functions equal by extensionality.
local macro "unfold_materialize" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieOverlay 0) "Near") "TrieOverlay") "applyChanges"
  `(tactic| unfold $(Lean.mkIdent name))

private theorem view_apply (state : State) :
    state.view = Lookup.apply (Lookup.apply state.entries state.committed) state.prospective := by
  unfold State.view
  unfold_materialize
  unfold Lookup.apply
  congr 1
  · funext entries change
    obtain ⟨key, value⟩ := change
    cases value <;> simp [Lookup.update]
  · congr 1
    funext entries change
    obtain ⟨key, value⟩ := change
    cases value <;> simp [Lookup.update]

/-- Unique keys in each overlay suffice; a key may occur in both overlays. -/
theorem view_lookup (state : State) (key : Bytes) (h : state.UniqueChanges) :
    Lookup.first state.view key =
      match selected state key with
      | some value => value
      | none => Lookup.first state.entries key := by
  rw [view_apply]
  rw [Lookup.first_apply _ _ _ h.1, Lookup.first_apply _ _ _ h.2]
  unfold selected
  cases Lookup.first state.prospective key <;> cases Lookup.first state.committed key <;> rfl

/-- A selected update, including a tombstone, determines the view's value. -/
theorem view_selected (state : State) (key : Bytes) (h : state.UniqueChanges)
    (value : Option Bytes) (hselected : selected state key = some value) :
    Lookup.first state.view key = value := by
  rw [view_lookup state key h, hselected]

/-- With no overlay hit, the materialized view retains the base association
list's lookup. Agreement with the on-disk trie is a separate obligation. -/
theorem view_unselected (state : State) (key : Bytes) (h : state.UniqueChanges)
    (hselected : selected state key = none) :
    Lookup.first state.view key = Lookup.first state.entries key := by
  rw [view_lookup state key h, hselected]

/-- The exact on-disk primitive called when neither overlay contains the key. -/
def baseLookup (state : State) (key : Bytes) (accountNodes : Bool) : Except String TrieAccounting.Result :=
  TrieAccounting.lookup state.base.witness state.base.root state.accounting
    { key, accountNodes, dereference := false, resetCache := false }

/-- Reference lookup carries forward cumulative accounting and cache warming. -/
def lookedState (state : State) (result : TrieAccounting.Result) : State :=
  { state with accounting := { result.state with
    disk := state.accounting.disk + result.state.disk,
    mem := state.accounting.mem + result.state.mem,
    events := state.accounting.events ++ result.state.events } }

/-- Expose the actual reference lookup through the public overlay selection.
No correctness assumption about canonical on-disk data is built into this equation. -/
theorem getReference_eq (state : State) (key : Bytes) (accountNodes : Bool) :
    getReference state key accountNodes =
      match selected state key with
      | some none => .ok (state, none)
      | some (some value) => .ok (state, some (.memory value))
      | none => do
        let result ← baseLookup state key accountNodes
        return (lookedState state result, result.reference.map (.trie state.base.root)) := by
  rfl

/-- An in-memory overlay hit returns exactly the bytes retained by the view. -/
theorem getReference_selected_value (state : State) (key : Bytes) (accountNodes : Bool)
    (h : state.UniqueChanges) (value : Bytes) (hselected : selected state key = some (some value)) :
    getReference state key accountNodes = .ok (state, some (.memory value)) ∧
      Lookup.first state.view key = some value := by
  refine ⟨?_, view_selected state key h (some value) hselected⟩
  rw [getReference_eq, hselected]

/-- A tombstone removes the base cell and does not dereference the disk trie. -/
theorem getReference_selected_tombstone (state : State) (key : Bytes) (accountNodes : Bool)
    (h : state.UniqueChanges) (hselected : selected state key = some none) :
    getReference state key accountNodes = .ok (state, none) ∧ Lookup.first state.view key = none := by
  refine ⟨?_, view_selected state key h none hselected⟩
  rw [getReference_eq, hselected]

/-- No-overlay reference lookup delegates precisely to the base primitive.
Only accounting changes; the view lookup is still the base-list lookup. -/
theorem getReference_unselected (state : State) (key : Bytes) (accountNodes : Bool)
    (h : state.UniqueChanges) (hselected : selected state key = none)
    (result : TrieAccounting.Result) (hbase : baseLookup state key accountNodes = .ok result) :
    getReference state key accountNodes =
      .ok (lookedState state result, result.reference.map (.trie state.base.root)) ∧
      Lookup.first state.view key = Lookup.first state.entries key := by
  refine ⟨?_, view_unselected state key h hselected⟩
  rw [getReference_eq, hselected]
  simp only [hbase, bind, Except.bind, pure, Except.pure]

/-- Presence agreement needed by the VM storage adapter. The sole on-disk
premise is about the base lookup's reference presence, not a host execution.
Successful overlay hits need no such premise. -/
theorem getReference_presence (state : State) (key : Bytes) (accountNodes : Bool)
    (h : state.UniqueChanges)
    (hbase : ∀ result, baseLookup state key accountNodes = .ok result →
      result.reference.isSome = (Lookup.first state.entries key).isSome)
    (after : State) (pointer : Option ValuePointer)
    (hget : getReference state key accountNodes = .ok (after, pointer)) :
    pointer.isSome = (Lookup.first state.view key).isSome := by
  rw [getReference_eq] at hget
  cases hselected : selected state key with
  | none =>
      rw [hselected] at hget
      cases hb : baseLookup state key accountNodes with
      | error error => simp only [hb, bind, Except.bind] at hget; contradiction
      | ok result =>
          simp only [hb, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at hget
          cases hget
          rw [view_unselected state key h hselected]
          simpa using hbase result hb
  | some value =>
      cases value with
      | none =>
          rw [hselected] at hget
          cases hget
          rw [view_selected state key h none hselected]
          rfl
      | some value =>
          rw [hselected] at hget
          cases hget
          rw [view_selected state key h (some value) hselected]
          rfl

/-- A successful memory reference agrees on the exact bytes, without any
premise about the on-disk trie: memory references arise only from overlays. -/
theorem getReference_memory_value (state : State) (key : Bytes) (accountNodes : Bool)
    (h : state.UniqueChanges) (after : State) (value : Bytes)
    (hget : getReference state key accountNodes = .ok (after, some (.memory value))) :
    Lookup.first state.view key = some value := by
  rw [getReference_eq] at hget
  cases hselected : selected state key with
  | none =>
      rw [hselected] at hget
      cases hb : baseLookup state key accountNodes with
      | error error => simp only [hb, bind, Except.bind] at hget; contradiction
      | ok result =>
          simp only [hb, bind, Except.bind, pure, Except.pure] at hget
          cases href : result.reference <;> simp only [href, Option.map_none, Option.map_some] at hget <;> cases hget
  | some selectedValue =>
      cases selectedValue with
      | none => rw [hselected] at hget; cases hget
      | some selectedValue =>
          rw [hselected] at hget
          cases hget
          exact view_selected state key h _ hselected

end Near.TrieOverlay
