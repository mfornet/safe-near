import NearInterface.TrieCanonicalLookup
import NearInterface.TrieWalkCost

/-! Cumulative access bounds for actual canonical overlay reads. -/
namespace Near.TrieOverlay.Cost
open TrieAccounting TrieConstruction TrieOverlay TrieWalkCost

/-- A bound for the complete raw trie key passed to the primitive. -/
def nodeBound (key : Bytes) (accountNodes : Bool) : Nat :=
  if accountNodes then 2 * key.length + 1 else 0

/-- Either overlay, including a tombstone, bypasses all base-node accounting. -/
def referenceBound (state : State) (key : Bytes) (accountNodes : Bool) : Nat :=
  if (selected state key).isSome then 0 else nodeBound key accountNodes

/-- Memory pointers incur no value touch; on-disk pointers incur one. -/
def pointerBound : ValuePointer → Nat
  | .memory _ => 0
  | .trie _ _ => 1

/-- The additional value cost for a present key, according to overlay origin. -/
def valueBound (state : State) (key : Bytes) : Nat :=
  if (selected state key).isSome then 0 else 1

/-- A complete read pays a value touch only for a present on-disk value. -/
def readBound (state : State) (key : Bytes) (accountNodes : Bool) : Nat :=
  referenceBound state key accountNodes +
    if (Lookup.first state.view key).isSome then valueBound state key else 0

/-- Per-query bounds lift through the actual cumulative accounting update. -/
theorem lookedState_accesses (state : State) (key : Bytes) (accountNodes : Bool)
    (result : TrieAccounting.Result) (hlookup : baseLookup state key accountNodes = .ok result)
    (hvalue : result.value = none) :
    Accesses state.accounting (lookedState state result).accounting (nodeBound key accountNodes) := by
  have hb := lookup_total_events_unconditional state.base.witness state.base.root state.accounting
    { key, accountNodes, dereference := false, resetCache := false } result hlookup
  simp only [TrieWalkCost.nodeBound, hvalue, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    Nat.add_zero] at hb
  change result.state.disk + result.state.mem ≤ nodeBound key accountNodes ∧
    result.state.events.length ≤ nodeBound key accountNodes at hb
  constructor
  · change state.accounting.disk ≤ state.accounting.disk + result.state.disk
    omega
  · change state.accounting.mem ≤ state.accounting.mem + result.state.mem
    omega
  · change state.accounting.disk + result.state.disk + (state.accounting.mem + result.state.mem) ≤ _
    omega
  · change (state.accounting.events ++ result.state.events).length ≤ _
    rw [List.length_append]
    omega

/-- The cost of actual successful reference lookup, with its canonical base
success proved rather than supplied as a base-lookup callback. -/
theorem getReference_accesses (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hnodes : state.NonzeroNodes)
    (after : State) (pointer : Option ValuePointer)
    (hget : getReference state key accountNodes = .ok (after, pointer)) :
    Accesses state.accounting after.accounting (referenceBound state key accountNodes) := by
  rw [getReference_eq] at hget
  cases hs : selected state key with
  | some value =>
    cases value <;> rw [hs] at hget <;> cases Except.ok.inj hget
    all_goals simpa only [referenceBound, hs, Option.isSome_some, ↓reduceIte] using Accesses.refl state.accounting
  | none =>
    rw [hs] at hget
    obtain ⟨accounting, hb⟩ := baseLookup_canonical state key accountNodes hcanonical hnodes
    simp only [hb, bind, Except.bind, pure, Except.pure] at hget
    cases Except.ok.inj hget
    simpa only [referenceBound, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] using
      lookedState_accesses state key accountNodes _ hb rfl

/-- Failure-free actual canonical getReference, presence agreement and its
full cumulative node-accounting bound from original state hypotheses. -/
theorem getReference_canonical_bounded (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hunique : state.UniqueChanges)
    (hnodes : state.NonzeroNodes) :
    ∃ after pointer, getReference state key accountNodes = .ok (after, pointer) ∧
      after.base = state.base ∧ after.view = state.view ∧
      pointer.isSome = (Lookup.first state.view key).isSome ∧
      Accesses state.accounting after.accounting (referenceBound state key accountNodes) := by
  obtain ⟨after, pointer, hg, hb, hv, hp⟩ := getReference_canonical state key accountNodes hcanonical hunique hnodes
  exact ⟨after, pointer, hg, hb, hv, hp, getReference_accesses state key accountNodes hcanonical hnodes after pointer hg⟩

/-- Any actual successful dereference records precisely its pointer-origin
upper bound. This supporting lemma requires no canonicality assumption. -/
theorem dereference_accesses (state after : State) (pointer : ValuePointer) (value : Bytes)
    (hd : dereference state pointer = .ok (after, value)) :
    Accesses state.accounting after.accounting (pointerBound pointer) := by
  cases pointer with
  | memory bytes =>
    cases Except.ok.inj hd
    exact Accesses.refl _
  | trie root reference =>
    by_cases hr : root = state.base.root
    · subst root
      simp only [dereference, beq_self_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at hd
      cases ha : TrieAccounting.dereference state.base.witness reference state.accounting with
      | error error => simp only [ha] at hd; cases hd
      | ok pair =>
        obtain ⟨bytes, accounting⟩ := pair
        simp only [ha] at hd
        cases Except.ok.inj hd
        exact TrieWalkCost.dereference_accesses _ _ _ _ _ ha
    · rw [dereference_wrong_root state root reference hr] at hd
      cases hd

/-- A returned pointer's origin agrees with the actual overlay selection. -/
theorem pointerBound_of_getReference (state : State) (key : Bytes) (accountNodes : Bool)
    (after : State) (pointer : ValuePointer)
    (hget : getReference state key accountNodes = .ok (after, some pointer)) :
    pointerBound pointer = valueBound state key := by
  rw [getReference_eq] at hget
  cases hs : selected state key with
  | some value =>
    cases value with
    | none => rw [hs] at hget; cases hget
    | some value =>
      rw [hs] at hget
      cases Except.ok.inj hget
      simp only [pointerBound, valueBound, hs, Option.isSome_some, ↓reduceIte]
  | none =>
    rw [hs] at hget
    cases hb : baseLookup state key accountNodes with
    | error error => simp only [hb, bind, Except.bind] at hget; cases hget
    | ok result =>
      simp only [hb, bind, Except.bind, pure, Except.pure] at hget
      cases href : result.reference with
      | none => simp only [href, Option.map_none] at hget; cases hget
      | some reference =>
        simp only [href, Option.map_some] at hget
        cases Except.ok.inj hget
        simp only [pointerBound, valueBound, hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]

/-- A complete canonical read, including absent and memory-overlay cases,
derives actual success and a cumulative original-key node/value bound. -/
theorem canonical_read_bounded (state : State) (key : Bytes) (accountNodes : Bool)
    (hcanonical : build state.entries = .ok state.base) (hunique : state.UniqueChanges)
    (hnodes : state.NonzeroNodes) :
    match Lookup.first state.view key with
    | none => ∃ after, getReference state key accountNodes = .ok (after, none) ∧
        Accesses state.accounting after.accounting (readBound state key accountNodes)
    | some value => ∃ after pointer finished,
        getReference state key accountNodes = .ok (after, some pointer) ∧
        dereference after pointer = .ok (finished, value) ∧
        Accesses state.accounting after.accounting (referenceBound state key accountNodes) ∧
        Accesses after.accounting finished.accounting (valueBound state key) ∧
        Accesses state.accounting finished.accounting (readBound state key accountNodes) := by
  have hr := canonical_read state key accountNodes hcanonical hunique hnodes
  cases hv : Lookup.first state.view key with
  | none =>
    rw [hv] at hr
    obtain ⟨after, hg, _⟩ := hr
    refine ⟨after, hg, ?_⟩
    simpa only [readBound, hv, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, Nat.add_zero] using
      getReference_accesses state key accountNodes hcanonical hnodes after none hg
  | some value =>
    rw [hv] at hr
    obtain ⟨after, pointer, finished, hg, hd, _⟩ := hr
    have hn := getReference_accesses state key accountNodes hcanonical hnodes after (some pointer) hg
    have hval := dereference_accesses after finished pointer value hd
    rw [pointerBound_of_getReference state key accountNodes after pointer hg] at hval
    refine ⟨after, pointer, finished, hg, hd, hn, hval, ?_⟩
    simpa only [readBound, hv, Option.isSome_some, ↓reduceIte] using hn.trans hval

/-- Disk/memory increments are bounded even when accounting began nonzero.
The event delta uses the same original accounting snapshot. -/
theorem accesses_deltas {before after : Accounting} {bound : Nat}
    (h : Accesses before after bound) :
    (after.disk - before.disk) + (after.mem - before.mem) ≤ bound ∧
      after.events.length - before.events.length ≤ bound := by
  obtain ⟨hd, hm, ht, he⟩ := h
  constructor <;> omega

/-- A single actual node or value touch adds exactly one disk-or-memory access,
whether or not the hash was already cached. -/
theorem touch_delta (before : Accounting) (hash : Hash) (kind : String) :
    ((before.touch hash kind).disk - before.disk) +
      ((before.touch hash kind).mem - before.mem) = 1 := by
  have ht := Accounting.touch_total before hash kind
  have hm := accesses_touch before hash kind
  obtain ⟨hd, hmem, _, _⟩ := hm
  omega

/-- Convert the access delta into a host-charge bound for arbitrary disk and
cached-node prices, without assuming which hashes were previously warmed. -/
theorem accesses_weighted {before after : Accounting} {bound : Nat}
    (h : Accesses before after bound) (diskPrice memPrice : Nat) :
    (after.disk - before.disk) * diskPrice + (after.mem - before.mem) * memPrice ≤
      bound * max diskPrice memPrice := by
  have ht := (accesses_deltas h).1
  calc
    _ ≤ (after.disk - before.disk) * max diskPrice memPrice +
        (after.mem - before.mem) * max diskPrice memPrice :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.le_max_left _ _))
        (Nat.mul_le_mul_left _ (Nat.le_max_right _ _))
    _ = ((after.disk - before.disk) + (after.mem - before.mem)) * max diskPrice memPrice :=
      (Nat.add_mul _ _ _).symm
    _ ≤ bound * max diskPrice memPrice := Nat.mul_le_mul_right _ ht

theorem referenceBound_le_nodeBound (state : State) (key : Bytes) (accountNodes : Bool) :
    referenceBound state key accountNodes ≤ nodeBound key accountNodes := by
  unfold referenceBound
  split <;> omega

theorem valueBound_le_one (state : State) (key : Bytes) : valueBound state key ≤ 1 := by
  unfold valueBound
  split <;> omega

/-- A full byte-key bound: node accesses plus a value touch exactly when the
view contains a value. Actual overlay reads have the sharper zero bound below. -/
theorem readBound_le (state : State) (key : Bytes) (accountNodes : Bool) :
    readBound state key accountNodes ≤ nodeBound key accountNodes +
      (if (Lookup.first state.view key).isSome then 1 else 0) := by
  have hn := referenceBound_le_nodeBound state key accountNodes
  have hv := valueBound_le_one state key
  unfold readBound
  split <;> omega

/-- Either overlay, including a deletion, incurs no trie access at all. -/
theorem readBound_selected (state : State) (key : Bytes) (accountNodes : Bool)
    (value : Option Bytes) (hs : selected state key = some value) : readBound state key accountNodes = 0 := by
  simp only [readBound, referenceBound, valueBound, hs, Option.isSome_some, ↓reduceIte]
  split <;> rfl

/-- Disabling node accounting always gives a zero reference-phase bound. -/
theorem referenceBound_unaccounted (state : State) (key : Bytes) : referenceBound state key false = 0 := by
  unfold referenceBound nodeBound
  split <;> rfl

/-- Contract-data keys include the account prefix and two separator bytes;
the access bound uses that complete encoded key, not just the contract key. -/
theorem nodeBound_contractKey (account key : Bytes) :
    nodeBound (contractKey account key) true = 2 * (account.length + key.length + 2) + 1 := by
  simp only [nodeBound, ↓reduceIte, contractKey, List.length_append, List.length_cons, List.length_nil]
  omega

end Near.TrieOverlay.Cost
