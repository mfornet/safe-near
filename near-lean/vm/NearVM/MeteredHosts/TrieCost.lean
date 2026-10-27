import NearVM.MeteredHosts.StorageMetered
import NearInterface.TrieWalkCost
import NearInterface.TrieOverlayLookup

/-!
# Original-key bounds for actual external trie charges

Successful reference lookup has a key-length bound independent of the trie
contents and cache. A later value dereference adds at most one touch. These
bounds cover the actual cumulative counters used by storage metering; they do
not assert that malformed tries succeed or prove storage-value agreement.
-/
namespace Wasm.Near.MeteredHosts.StorageMetered
open _root_.Near _root_.Near.TrieAccounting _root_.Near.TrieOverlay

/-- Total new counter events billed between two external-boundary snapshots. -/
def trieTouches (before after : TrieOverlay.State) : Nat :=
  (after.accounting.disk - before.accounting.disk) +
    (after.accounting.mem - before.accounting.mem)

/-- The reference-only primitive never reads value bytes. -/
theorem lookup_reference_value_none (witness : Witness) (root : Hash) (previous : Accounting)
    (query : Query) (result : Result) (hmode : query.dereference = false)
    (h : lookup witness root previous query = .ok result) : result.value = none := by
  cases hw : TrieLeaf.walkObjects witness query.accountNodes (witness.length + 1) [] root
      (nibbles query.key) (TrieLeaf.queryStart previous query) with
  | error error =>
    unfold TrieLeaf.walkObjects TrieLeaf.queryStart at hw
    simp [lookup, hw, bind, Except.bind] at h
  | ok pair =>
    obtain ⟨reference, after⟩ := pair
    unfold TrieLeaf.walkObjects TrieLeaf.queryStart at hw
    simp only [lookup, hw, bind, Except.bind] at h
    cases reference <;> simp [hmode, pure, Except.pure] at h <;> subst result <;> rfl

/-- A conservative node bound valid for either accountNodes setting. -/
theorem getReference_touches_le (before after : TrieOverlay.State) (key : Bytes)
    (accountNodes : Bool) (pointer : Option ValuePointer)
    (h : getReference before key accountNodes = .ok (after, pointer)) :
    before.accounting.disk ≤ after.accounting.disk ∧
    before.accounting.mem ≤ after.accounting.mem ∧
    trieTouches before after ≤ 2 * key.length + 1 := by
  rw [getReference_eq] at h
  cases hs : selected before key with
  | some value =>
    cases value <;> simp [hs, Except.ok.injEq, Prod.mk.injEq] at h <;>
      obtain ⟨rfl, _⟩ := h <;> simp [trieTouches]
  | none =>
    cases hl : baseLookup before key accountNodes with
    | error error => simp [hs, hl, bind, Except.bind] at h
    | ok result =>
      simp only [hs, hl, bind, Except.bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      have hb := TrieWalkCost.lookup_total_events_unconditional before.base.witness before.base.root
        before.accounting { key, accountNodes, dereference := false, resetCache := false } result hl
      simp only [trieTouches, lookedState]
      constructor
      · omega
      constructor
      · omega
      have hn : TrieWalkCost.nodeBound
          { key, accountNodes, dereference := false, resetCache := false } ≤ 2 * key.length + 1 := by
        cases accountNodes <;> simp [TrieWalkCost.nodeBound]
      have hv := lookup_reference_value_none before.base.witness before.base.root before.accounting
        { key, accountNodes, dereference := false, resetCache := false } result rfl hl
      rw [hv] at hb
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] at hb
      omega

/-- In-memory values touch no objects; successful on-disk values add at
most one counter event, retaining the preexisting cache and counters. -/
theorem dereference_touches_le (before after : TrieOverlay.State) (pointer : ValuePointer)
    (bytes : Bytes) (h : TrieOverlay.dereference before pointer = .ok (after, bytes)) :
    before.accounting.disk ≤ after.accounting.disk ∧
    before.accounting.mem ≤ after.accounting.mem ∧ trieTouches before after ≤ 1 := by
  cases pointer with
  | memory value =>
    simp only [TrieOverlay.dereference, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    simp [trieTouches]
  | trie root reference =>
    unfold TrieOverlay.dereference at h
    by_cases he : root = before.base.root
    · simp only [he, BEq.rfl, ↓reduceIte, pure,
        Except.pure, bind, Except.bind] at h
      cases hr : TrieAccounting.dereference before.base.witness reference before.accounting with
      | error error => simp [hr] at h
      | ok result =>
        obtain ⟨value, counters⟩ := result
        simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        have hb := TrieWalkCost.dereference_accesses before.base.witness reference
          before.accounting counters value hr
        obtain ⟨hd, hm, ht, _⟩ := hb
        simp only [trieTouches]
        exact ⟨hd, hm, by omega⟩
    · simp [he, bind, Except.bind] at h

/-- Reference lookup followed by a value read has an original-key bound,
including cumulative accounting across both phases. -/
theorem lookup_dereference_touches_le (before middle after : TrieOverlay.State) (key : Bytes)
    (accountNodes : Bool) (pointer : ValuePointer) (bytes : Bytes)
    (hlookup : getReference before key accountNodes = .ok (middle, some pointer))
    (hread : TrieOverlay.dereference middle pointer = .ok (after, bytes)) :
    trieTouches before after ≤ 2 * key.length + 2 := by
  obtain ⟨hd, hm, hb⟩ := getReference_touches_le before middle key accountNodes (some pointer) hlookup
  obtain ⟨hd', hm', hb'⟩ := dereference_touches_le middle after pointer bytes hread
  unfold trieTouches at *
  omega

/-- The disk/cached split is bounded by the larger of its two original prices. -/
theorem trieCharges_le (costs : ExtCosts) (before after : TrieOverlay.State) (bound : Nat)
    (h : trieTouches before after ≤ bound) :
    burnSum costs (trieCharges before after) ≤
      max (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node") * bound := by
  have hd := Nat.le_max_left (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node")
  have hm := Nat.le_max_right (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node")
  have hfirst := Nat.mul_le_mul_right (after.accounting.disk - before.accounting.disk) hd
  have hsecond := Nat.mul_le_mul_right (after.accounting.mem - before.accounting.mem) hm
  have hsum := Nat.add_le_add hfirst hsecond
  rw [← Nat.mul_add] at hsum
  have hex : burnSum costs (trieCharges before after) ≤
      max (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node") * trieTouches before after := by
    simpa [burnSum, burnCost, trieCharges, trieTouches] using hsum
  exact Nat.le_trans hex (Nat.mul_le_mul_left (max (costs.cost "touching_trie_node")
    (costs.cost "read_cached_trie_node")) h)

/-- Key length and original prices bound the actual successful lookup charge. -/
theorem getReference_charge_le (costs : ExtCosts) (before after : TrieOverlay.State) (key : Bytes)
    (accountNodes : Bool) (pointer : Option ValuePointer)
    (h : getReference before key accountNodes = .ok (after, pointer)) :
    burnSum costs (trieCharges before after) ≤
      max (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node") * (2 * key.length + 1) :=
  trieCharges_le costs before after _ (getReference_touches_le before after key accountNodes pointer h).2.2

/-- Both successful external phases fit a cost formula using only the key
length and original cost table. No measured cost or trie size appears. -/
theorem lookup_dereference_charge_le (costs : ExtCosts)
    (before middle after : TrieOverlay.State) (key : Bytes) (accountNodes : Bool)
    (pointer : ValuePointer) (bytes : Bytes)
    (hlookup : getReference before key accountNodes = .ok (middle, some pointer))
    (hread : TrieOverlay.dereference middle pointer = .ok (after, bytes)) :
    burnSum costs (trieCharges before after) ≤
      max (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node") * (2 * key.length + 2) :=
  trieCharges_le costs before after _
    (lookup_dereference_touches_le before middle after key accountNodes pointer bytes hlookup hread)

end Wasm.Near.MeteredHosts.StorageMetered
