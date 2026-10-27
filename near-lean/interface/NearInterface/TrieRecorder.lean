import NearInterface.TrieAccounting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Pure recorded-storage upper-bound accounting

This isolated model transcribes the accounting rules at the pinned nearcore
commit `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`:
* `core/store/src/trie/trie_recording.rs:115–158`:
  https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/core/store/src/trie/trie_recording.rs#L115
* Contract-data removals call the recorder even for an already absent key:
  https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/core/store/src/trie/update.rs#L169
* The receipt baseline is captured before its actions at protocol 86:
  https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/runtime/runtime/src/lib.rs#L838

This file proves arithmetic, not fidelity of the current runtime oracle.
It models sequential successful `usize` arithmetic using naturals. Relating a
native run requires each intermediate upper bound to fit `usize`, valid
hash/object bindings, matching recorder events, and the native receipt-start
snapshot. `delta` agrees with native checked subtraction only when `Valid`
holds. Native reference counts do not affect this upper bound. Test-only
`record_unaccounted` and concurrent observations are outside this model.
-/
namespace Near.TrieRecorder
open TrieAccounting

/-- A finite hash map: each recorded hash selects exactly its first object. -/
structure State where
  recorded : Finset Hash := ∅
  objects : Hash → Bytes := fun _ => []
  removals : Nat := 0
  codeBytes : Nat := 0
  baseline : Nat := 0

def State.objectBytes (state : State) : Nat := ∑ hash ∈ state.recorded, (state.objects hash).length

def State.upperBound (state : State) : Nat := state.objectBytes + 2000 * state.removals + state.codeBytes

def State.Valid (state : State) : Prop := state.baseline ≤ state.upperBound

def State.delta (state : State) : Nat := state.upperBound - state.baseline

/-- Repeated hashes retain the first object, even if supplied different bytes. -/
def State.record (state : State) (hash : Hash) (bytes : Bytes) : State :=
  if hash ∈ state.recorded then state else
    { state with
      recorded := insert hash state.recorded
      objects := fun query => if query = hash then bytes else state.objects query }

def State.remove (state : State) : State := { state with removals := state.removals + 1 }

def State.code (state : State) (length : Nat) : State := { state with codeBytes := state.codeBytes + length }

def State.snapshot (state : State) : State := { state with baseline := state.upperBound }

theorem record_hit (state : State) (hash : Hash) (bytes : Bytes) (h : hash ∈ state.recorded) :
    state.record hash bytes = state := by simp [State.record, h]

theorem record_mem (state : State) (hash : Hash) (bytes : Bytes) :
    hash ∈ (state.record hash bytes).recorded := by
  by_cases h : hash ∈ state.recorded <;> simp [State.record, h]

theorem record_idempotent (state : State) (hash : Hash) (first second : Bytes) :
    (state.record hash first).record hash second = state.record hash first :=
  record_hit _ hash second (record_mem state hash first)

theorem record_object_fresh (state : State) (hash : Hash) (bytes : Bytes)
    (h : hash ∉ state.recorded) : (state.record hash bytes).objects hash = bytes := by
  simp [State.record, h]

theorem record_fresh_objectBytes (state : State) (hash : Hash) (bytes : Bytes)
    (h : hash ∉ state.recorded) : (state.record hash bytes).objectBytes = state.objectBytes + bytes.length := by
  have hs : (∑ query ∈ state.recorded,
      (if query = hash then bytes else state.objects query).length) = state.objectBytes := by
    apply Finset.sum_congr rfl
    intro query hq
    have hn : query ≠ hash := fun he => h (he ▸ hq)
    simp [hn]
  simp only [State.record, h, ↓reduceIte, State.objectBytes, Finset.sum_insert h, ↓reduceIte]
  rw [hs]
  change bytes.length + state.objectBytes = state.objectBytes + bytes.length
  omega

theorem record_upperBound (state : State) (hash : Hash) (bytes : Bytes) :
    (state.record hash bytes).upperBound = state.upperBound +
      if hash ∈ state.recorded then 0 else bytes.length := by
  by_cases h : hash ∈ state.recorded
  · simp [record_hit state hash bytes h, h]
  · have hs := record_fresh_objectBytes state hash bytes h
    simp only [State.upperBound]
    rw [hs]
    simp [State.record, h]
    omega

theorem record_mono (state : State) (hash : Hash) (bytes : Bytes) :
    state.upperBound ≤ (state.record hash bytes).upperBound := by
  rw [record_upperBound]
  omega

theorem remove_upperBound (state : State) : state.remove.upperBound = state.upperBound + 2000 := by
  simp only [State.upperBound, State.remove, State.objectBytes]
  omega

theorem remove_twice_upperBound (state : State) :
    state.remove.remove.upperBound = state.upperBound + 4000 := by
  rw [remove_upperBound, remove_upperBound]

theorem code_upperBound (state : State) (length : Nat) :
    (state.code length).upperBound = state.upperBound + length := by
  simp only [State.upperBound, State.code, State.objectBytes]
  omega

theorem snapshot_upperBound (state : State) : state.snapshot.upperBound = state.upperBound := rfl

theorem snapshot_valid (state : State) : state.snapshot.Valid := Nat.le_refl _

theorem snapshot_delta (state : State) : state.snapshot.delta = 0 := by
  simp [State.delta, State.snapshot, State.upperBound, State.objectBytes]

/-- Receipt deltas retain additive growth once the snapshot precedes the
current upper bound. This is the condition native checked subtraction needs. -/
theorem delta_growth (before after : State) (cost : Nat) (hvalid : before.Valid)
    (hbase : after.baseline = before.baseline)
    (hgrowth : after.upperBound = before.upperBound + cost) :
    after.delta = before.delta + cost := by
  simp only [State.Valid] at hvalid
  simp only [State.delta, hbase, hgrowth]
  omega

theorem delta_growth_bound (before after : State) (budget : Nat) (hvalid : before.Valid)
    (hbase : after.baseline = before.baseline)
    (hgrowth : after.upperBound ≤ before.upperBound + budget) :
    after.delta ≤ before.delta + budget := by
  simp only [State.Valid] at hvalid
  simp only [State.delta, hbase]
  omega

/-- Upper-bound accounting events; no caller-operation simulation is assumed. -/
inductive Event where
  | record (hash : Hash) (bytes : Bytes)
  | remove
  | code (length : Nat)

def Event.cost : Event → Nat
  | .record _ bytes => bytes.length
  | .remove => 2000
  | .code length => length

def State.step (state : State) : Event → State
  | .record hash bytes => state.record hash bytes
  | .remove => state.remove
  | .code length => state.code length

def State.run (state : State) (events : List Event) : State := events.foldl State.step state

theorem step_baseline (state : State) (event : Event) :
    (state.step event).baseline = state.baseline := by
  cases event with
  | record hash bytes =>
    by_cases h : hash ∈ state.recorded <;> simp [State.step, State.record, h]
  | remove => rfl
  | code length => rfl

theorem step_growth (state : State) (event : Event) :
    state.upperBound ≤ (state.step event).upperBound ∧
      (state.step event).upperBound ≤ state.upperBound + event.cost := by
  cases event with
  | record hash bytes =>
    simp only [State.step, Event.cost, record_upperBound]
    split <;> omega
  | remove => simp only [State.step, Event.cost, remove_upperBound]; omega
  | code length => simp only [State.step, Event.cost, code_upperBound]; omega

theorem step_valid (state : State) (event : Event) (h : state.Valid) : (state.step event).Valid := by
  change (state.step event).baseline ≤ (state.step event).upperBound
  rw [step_baseline]
  exact h.trans (step_growth state event).1

theorem run_baseline (state : State) (events : List Event) :
    (state.run events).baseline = state.baseline := by
  induction events generalizing state with
  | nil => rfl
  | cons event events ih =>
    change ((state.step event).run events).baseline = state.baseline
    rw [ih, step_baseline]

theorem run_growth (state : State) (events : List Event) :
    state.upperBound ≤ (state.run events).upperBound ∧
      (state.run events).upperBound ≤ state.upperBound + (events.map Event.cost).sum := by
  induction events generalizing state with
  | nil => exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  | cons event events ih =>
    have hs := step_growth state event
    have ht := ih (state.step event)
    change state.upperBound ≤ ((state.step event).run events).upperBound ∧
      ((state.step event).run events).upperBound ≤ state.upperBound + ((event :: events).map Event.cost).sum
    simp only [List.map_cons, List.sum_cons]
    exact ⟨hs.1.trans ht.1, by omega⟩

theorem run_valid (state : State) (events : List Event) (h : state.Valid) : (state.run events).Valid := by
  change (state.run events).baseline ≤ (state.run events).upperBound
  rw [run_baseline]
  exact h.trans (run_growth state events).1

/-- Deduplication only reduces the event budget, never increases it. -/
theorem run_delta_bound (state : State) (events : List Event) (h : state.Valid) :
    (state.run events).delta ≤ state.delta + (events.map Event.cost).sum :=
  delta_growth_bound state _ _ h (run_baseline state events) (run_growth state events).2

/-- A receipt whose modeled event budget fits the limit has a fitting delta;
this theorem still requires an independent runtime-to-event fidelity proof. -/
theorem snapshot_run_delta_bound (state : State) (events : List Event) :
    (state.snapshot.run events).delta ≤ (events.map Event.cost).sum := by
  have h := run_delta_bound state.snapshot events (snapshot_valid state)
  simpa only [snapshot_delta, Nat.zero_add] using h

end Near.TrieRecorder
