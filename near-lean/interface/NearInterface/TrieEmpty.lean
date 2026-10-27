import NearInterface.TrieOverlayLookup

/-!
# Exact empty-base trie lookup

The canonical empty base uses the reserved zero root. Its lookup never fetches
a witness object, independently of prior cache/accounting state. This closes
the base primitive for genuinely empty bases without a cryptographic premise.
-/
namespace Near.TrieOverlay
open TrieAccounting TrieConstruction

def emptyBase : Built := { root := List.replicate 32 0, memoryUsage := 0, witness := [] }

theorem build_empty : TrieConstruction.build [] = .ok emptyBase := by rfl

local macro "unfold_empty_walk" : tactic => do
  let name := Lean.Name.str (Lean.Name.str (Lean.Name.str
    (Lean.Name.num `_private.NearInterface.TrieAccounting 0) "Near") "TrieAccounting") "walk"
  `(tactic| unfold $(Lean.mkIdent name))

/-- The empty root is checked before any witness read or node-accounting touch. -/
theorem lookup_empty_root (witness : Witness) (previous : Accounting) (query : Query) :
    TrieAccounting.lookup witness (List.replicate 32 0) previous query =
      .ok {
        reference := none
        value := none
        state := { seen := if query.resetCache then [] else previous.seen } } := by
  unfold TrieAccounting.lookup
  unfold_empty_walk
  simp [bind, Except.bind, pure, Except.pure]

/-- Canonical construction forces the exact empty base when entries are empty. -/
theorem base_empty_of_canonical (state : State)
    (hentries : state.entries = [])
    (hcanonical : TrieConstruction.build state.entries = .ok state.base) : state.base = emptyBase := by
  rw [hentries, build_empty] at hcanonical
  exact (Except.ok.inj hcanonical).symm

/-- With no in-memory update, the genuine empty base returns no reference and
retains the complete state, including cumulative accounting and cache. -/
theorem getReference_empty_unselected (state : State) (key : Bytes) (accountNodes : Bool)
    (hbase : state.base = emptyBase) (hselected : selected state key = none) :
    getReference state key accountNodes = .ok (state, none) := by
  rw [getReference_eq, hselected]
  simp only [baseLookup, hbase, emptyBase, lookup_empty_root]
  change Except.ok (lookedState state {
    reference := none
    value := none
    state := { seen := state.accounting.seen } }, none) = .ok (state, none)
  simp [lookedState]

end Near.TrieOverlay
