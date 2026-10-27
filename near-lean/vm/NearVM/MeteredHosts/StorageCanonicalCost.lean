import NearVM.MeteredHosts.StorageCanonical
import NearVM.MeteredHosts.TrieCost
import NearVM.MeteredHosts.StorageOverlay
import NearInterface.StorageUsage

/-! Original-context bounds for canonical storage-write preparation charges. -/
namespace Wasm.Near.MeteredHosts.StorageCanonicalCost
open StorageMetered StorageOverlay StorageCanonical
open _root_.Near _root_.Near.TrieAccounting _root_.Near.TrieOverlay

/-- The actual primitive length check fixes the length carried by a trie
reference; this is derived from successful dereferencing rather than assumed. -/
theorem trie_reference_length (witness : Witness) (reference : ValueRef)
    (before after : Accounting) (value : Bytes)
    (hd : TrieAccounting.dereference witness reference before = .ok (value, after)) :
    reference.length = value.length := by
  unfold TrieAccounting.dereference at hd
  cases hf : TrieLeaf.fetchObject witness reference.hash with
  | error error =>
    unfold TrieLeaf.fetchObject at hf
    simp [hf, bind, Except.bind] at hd
  | ok bytes =>
    unfold TrieLeaf.fetchObject at hf
    simp only [hf, bind, Except.bind] at hd
    by_cases hl : bytes.length = reference.length
    · simp only [hl, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, pure, Except.pure] at hd
      have he := congrArg (fun pair : Bytes × Accounting => pair.1) (Except.ok.inj hd)
      change bytes = value at he
      simpa only [he] using hl.symm
    · simp [hl] at hd

/-- Both memory and trie pointers expose exactly the successfully returned
value length, even when value hashes alias cached node objects. -/
theorem pointer_reference_length (before after : State) (pointer : ValuePointer) (value : Bytes)
    (hd : dereference before pointer = .ok (after, value)) : pointer.reference.2.length = value.length := by
  cases pointer with
  | memory bytes =>
    cases Except.ok.inj hd
    rfl
  | trie root reference =>
    by_cases he : root = before.base.root
    · subst root
      simp only [TrieOverlay.dereference, beq_self_eq_true, ↓reduceIte, pure, Except.pure, bind, Except.bind] at hd
      cases hf : TrieAccounting.dereference before.base.witness reference before.accounting with
      | error error => simp only [hf] at hd; cases hd
      | ok pair =>
        obtain ⟨bytes, accounting⟩ := pair
        simp only [hf] at hd
        cases Except.ok.inj hd
        exact trie_reference_length _ _ _ _ _ hf
    · rw [dereference_wrong_root before root reference he] at hd
      cases hd

/-- WF counts every raw record in original account storage usage. Thus any
old value represented by the host fits within that original usage budget. -/
theorem old_length_le_usage (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (key old : Bytes)
    (hold : before.host.storage key = some old) : old.length ≤ ctx.storageUsage := by
  have hlookup : Lookup.first storage key = some old := by rw [← hr.2 key]; exact hold
  have hm : (key, old) ∈ raw := by
    rw [← hs]
    exact List.mem_toFinset.mpr (Lookup.first_some_mem storage key old hlookup)
  have hrecord := NearInterface.recordBytes_le_storageUsageOf ctx.protocol raw key old hm
  have htotal := hwf.usage_ge
  simp only [NearInterface.recordBytes] at hrecord
  omega

/-- A bound using only original context, raw key and external prices. Trie
node touches use the full native account-prefixed key, plus one value touch. -/
def phaseBound (costs : ExtCosts) (ctx : NearInterface.Context) (key : Bytes) : Nat :=
  max (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node") *
    (2 * (contractKey ctx.current.bytes key).length + 2) +
  costs.cost "storage_write_evicted_byte" * ctx.storageUsage

/-- The actual old-reference byte bill equals the returned old byte count. -/
theorem evicted_charge_eq (costs : ExtCosts) (before after : State) (pointer : ValuePointer) (old : Bytes)
    (hd : dereference before pointer = .ok (after, old)) :
    burnSum costs (evictedCharges pointer) = costs.cost "storage_write_evicted_byte" * old.length := by
  simp only [evictedCharges, burnSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero, burnCost, pointer_reference_length before after pointer old hd]

/-- The computed canonical plan's complete ordered phase bill is bounded by
original key/account length, original prices and original storage usage. -/
theorem plan_cost_le (costs : ExtCosts) (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes) (key : Bytes) :
    burnSum costs ((plan ctx.trie (contractKey before.host.context.currentAccountId key)).charges ctx.trie) ≤
      phaseBound costs ctx key := by
  have hv := plan_valid before ctx raw hwf storage hs hr hnodes key
  dsimp only at hv
  generalize hp : plan ctx.trie (contractKey before.host.context.currentAccountId key) = p at hv ⊢
  cases p with
  | fresh looked =>
    have hg := hv.1
    have ht := getReference_charge_le costs ctx.trie looked _ true none hg
    simp only [LookupPlan.charges]
    rw [hr.1] at ht
    apply Nat.le_trans ht
    unfold phaseBound
    apply Nat.le_trans (Nat.mul_le_mul_left _ (show
      2 * (contractKey ctx.current.bytes key).length + 1 ≤ 2 * (contractKey ctx.current.bytes key).length + 2 by omega))
    exact Nat.le_add_right _ _
  | replace looked pointer fetched old =>
    obtain ⟨hg, hd, ho⟩ := hv
    have hstorage : before.host.storage key = some old := ho
    have hlength := old_length_le_usage before ctx raw hwf storage hs hr key old hstorage
    have ht := lookup_dereference_charge_le costs ctx.trie looked fetched _ true pointer old hg hd
    rw [hr.1] at ht
    have he := evicted_charge_eq costs looked fetched pointer old hd
    have hev : burnSum costs (evictedCharges pointer) ≤
        costs.cost "storage_write_evicted_byte" * ctx.storageUsage := by
      rw [he]
      exact Nat.mul_le_mul_left _ hlength
    simp only [LookupPlan.charges, burnSum, List.map_append, List.sum_append]
    change burnSum costs (evictedCharges pointer) + burnSum costs (trieCharges ctx.trie fetched) ≤ _
    have hsum := Nat.add_le_add ht hev
    simpa only [phaseBound, Nat.add_comm] using hsum

/-- A register bill is paid on replacement even for discarded output. Its
original-context bound is independent of the old value's computed length. -/
def postBound (costs : ExtCosts) (ctx : NearInterface.Context) : Nat :=
  costs.cost "write_register_base" + costs.cost "write_register_byte" * ctx.storageUsage

theorem postCharges_cost_le (costs : ExtCosts) (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (key : Bytes) :
    burnSum costs (postCharges before key) ≤ postBound costs ctx := by
  cases hv : before.host.storage key with
  | none => simp [postCharges, hv, burnSum]
  | some old =>
    have hl := old_length_le_usage before ctx raw hwf storage hs hr key old hv
    have hm := Nat.mul_le_mul_left (costs.cost "write_register_byte") hl
    simpa only [postCharges, hv, writeReg, burnSum, List.map_cons, List.map_nil,
      List.sum_cons, List.sum_nil, burnCost, Nat.mul_one, Nat.add_zero, postBound] using
      Nat.add_le_add_left hm (costs.cost "write_register_base")

/-- Original symbolic phase coverage discharges computed-plan credits. -/
theorem plan_credits (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes) (key : Bytes) (rest : Nat)
    (hc : before.host.gas.Credits (phaseBound before.host.extCosts ctx key + rest)) :
    before.host.gas.Credits
      (burnSum before.host.extCosts ((plan ctx.trie (contractKey before.host.context.currentAccountId key)).charges ctx.trie) + rest) := by
  exact hc.mono (Nat.add_le_add_right (plan_cost_le before.host.extCosts before ctx raw hwf storage hs hr hnodes key) rest)

/-- A single original-context bound covers both the actual canonical plan and
the actual replacement register bill. Pre-call charges remain separate. -/
theorem plan_post_credits (before : HostStore NearState) (ctx : NearInterface.Context)
    (raw : NearInterface.RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (hr : Represents before.host ctx storage) (hnodes : ctx.trie.NonzeroNodes) (key : Bytes) (rest : Nat)
    (hc : before.host.gas.Credits
      (phaseBound before.host.extCosts ctx key + postBound before.host.extCosts ctx + rest)) :
    before.host.gas.Credits
      (burnSum before.host.extCosts ((plan ctx.trie (contractKey before.host.context.currentAccountId key)).charges ctx.trie) +
        burnSum before.host.extCosts (postCharges before key) + rest) := by
  have hp := plan_cost_le before.host.extCosts before ctx raw hwf storage hs hr hnodes key
  have hpost := postCharges_cost_le before.host.extCosts before ctx raw hwf storage hs hr key
  exact hc.mono (Nat.add_le_add_right (Nat.add_le_add hp hpost) rest)

/-- Expand the native key prefix so the phase budget depends only on
original account length, raw key length, prices and account usage. -/
theorem phaseBound_lengths (costs : ExtCosts) (ctx : NearInterface.Context) (key : Bytes) :
    phaseBound costs ctx key =
      max (costs.cost "touching_trie_node") (costs.cost "read_cached_trie_node") *
        (2 * (ctx.current.bytes.length + key.length + 2) + 2) +
      costs.cost "storage_write_evicted_byte" * ctx.storageUsage := by
  have hl : (contractKey ctx.current.bytes key).length = ctx.current.bytes.length + key.length + 2 := by
    simp only [contractKey, List.length_append, List.length_cons, List.length_nil]
    omega
  simp only [phaseBound, hl]

end Wasm.Near.MeteredHosts.StorageCanonicalCost
