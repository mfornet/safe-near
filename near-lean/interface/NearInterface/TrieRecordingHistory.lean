import NearInterface.TrieOverlayInvariant
import NearInterface.TrieRecorder

/-!
# Why recorded proof size needs history

Repeated removal is idempotent in the current overlay state, while the pinned
native recorder charges each contract-data removal. A function of that overlay
state alone cannot represent the native removal counter for every trace.
-/
namespace Near.TrieOverlay
open TrieAccounting

/-- A canonical empty base with a single already removed key. -/
def tombstoned (key : Bytes) : State :=
  { entries := [], base := { root := List.replicate 32 0, memoryUsage := 0, witness := [] },
    prospective := [(key, none)] }

local macro "unfold_history_insert" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieOverlay 0) "Near") "TrieOverlay") "insert"
  `(tactic| unfold $(Lean.mkIdent name))

theorem tombstoned_canonical (key : Bytes) :
    TrieConstruction.build (tombstoned key).entries = .ok (tombstoned key).base := rfl

theorem tombstoned_unique (key : Bytes) : (tombstoned key).UniqueChanges := by
  simp [State.UniqueChanges, tombstoned]

/-- The existing overlay deliberately forgets repeated removals of one key. -/
theorem tombstoned_remove (key : Bytes) : (tombstoned key).remove key = tombstoned key := by
  unfold State.remove
  unfold_history_insert
  simp [tombstoned]

/-- This remains impossible even on a canonical unique-overlay input. An
explicit recorder state or event history is necessary to count every removal. -/
theorem no_state_only_removal_counter (key : Bytes) :
    ¬ ∃ size : State → Nat, ∀ state,
      size (state.remove key) = size state + 2000 := by
  rintro ⟨size, hsize⟩
  have h := hsize (tombstoned key)
  rw [tombstoned_remove] at h
  omega

end Near.TrieOverlay
