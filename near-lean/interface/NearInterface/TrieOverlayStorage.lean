import NearInterface.Boundary
import NearInterface.TrieOverlayLookup
import Mathlib.Data.List.Infix

/-!
# Overlay references agree with raw contract storage

The boundary's raw-key functionality is enough for account-local lookup
agreement; global uniqueness of the materialized base list is unnecessary.
Disk-trie reference correctness remains a separate obligation.
-/
namespace Near.TrieOverlay.Lookup
variable {K V : Type} [BEq K] [LawfulBEq K]

theorem first_some_mem (entries : List (K × V)) (key : K) (value : V)
    (h : first entries key = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp [first] at h
  | cons entry entries ih =>
    obtain ⟨k, v⟩ := entry
    by_cases hk : k = key
    · subst k
      simp [first_cons] at h
      subst v
      exact List.mem_cons_self
    · have hb : (k == key) = false := beq_eq_false_iff_ne.mpr hk
      simp only [first_cons, hb, Bool.false_eq_true, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem first_eq_some_of_mem (entries : List (K × V)) (key : K) (value : V)
    (hm : (key, value) ∈ entries)
    (hf : ∀ v, (key, v) ∈ entries → v = value) : first entries key = some value := by
  induction entries with
  | nil => simp at hm
  | cons entry entries ih =>
    obtain ⟨k, v⟩ := entry
    by_cases hk : k = key
    · subst k
      have hv := hf v List.mem_cons_self
      simp [first_cons, hv]
    · have hb : (k == key) = false := beq_eq_false_iff_ne.mpr hk
      have ht : (key, value) ∈ entries := by simpa [hk, Ne.symm hk, Prod.mk.injEq] using hm
      simpa only [first_cons, hb, Bool.false_eq_true, ↓reduceIte] using
        ih ht (fun v hv => hf v (List.mem_cons_of_mem _ hv))

theorem first_eq_none_iff (entries : List (K × V)) (key : K) :
    first entries key = none ↔ ∀ value, (key, value) ∉ entries := by
  constructor
  · intro h value hm
    have hn : ∀ entry ∈ entries, ¬ (entry.1 == key) := by
      simpa [first, List.find?_eq_none] using h
    exact hn (key, value) hm (by simp)
  · intro h
    apply first_none
    intro hm
    obtain ⟨⟨k,v⟩, hm, hk⟩ := List.mem_map.mp hm
    change k = key at hk
    subst k
    exact h v hm
end Near.TrieOverlay.Lookup

namespace NearInterface
open Wasm Wasm.Near
open Near.TrieOverlay

/-- Removing the account prefix and adding it back preserves every record. -/
theorem mem_contractData_iff (state : Near.TrieOverlay.State) (account key value : Bytes) :
    (key, value) ∈ contractData state account ↔
      (contractKey account key, value) ∈ state.view := by
  have hkey : contractKey account key = contractKey account [] ++ key := by
    simp [contractKey, List.append_assoc]
  simp only [contractData, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨⟨full, v⟩, hm, he⟩
    split at he
    next hp =>
      have he' := Option.some.inj he
      have hk := congrArg Prod.fst he'
      have hv := congrArg Prod.snd he'
      change full.drop (contractKey account []).length = key at hk
      change v = value at hv
      have hp' : contractKey account [] <+: full := List.isPrefixOf_iff_prefix.mp hp
      have hr := List.prefix_append_drop hp'
      rw [hk] at hr
      rw [hkey, ← hr, ← hv]
      exact hm
    next hp => contradiction
  · intro hm
    refine ⟨(contractKey account key, value), hm, ?_⟩
    rw [hkey]
    simp

/-- WF supplies functionality at precisely the account prefix being observed. -/
theorem wf_view_lookup (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (key value : Bytes) :
    Lookup.first ctx.trie.view (contractKey ctx.current.bytes key) = some value ↔
      (key, value) ∈ raw := by
  have hm (v : Bytes) :
      (contractKey ctx.current.bytes key, v) ∈ ctx.trie.view ↔ (key, v) ∈ raw := by
    rw [← mem_contractData_iff, hwf.trie_storage]
  constructor
  · intro h
    exact (hm value).mp (Lookup.first_some_mem _ _ _ h)
  · intro h
    apply Lookup.first_eq_some_of_mem _ _ _ ((hm value).mpr h)
    intro v hv
    exact hwf.raw_keys_unique key v value ((hm v).mp hv) h

theorem wf_view_lookup_none (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (key : Bytes) :
    Lookup.first ctx.trie.view (contractKey ctx.current.bytes key) = none ↔
      ∀ value, (key, value) ∉ raw := by
  rw [Lookup.first_eq_none_iff]
  simp only [← mem_contractData_iff, hwf.trie_storage]

/-- Any list representation of the boundary raw storage has the same lookup. -/
theorem wf_storage_lookup (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw) (key : Bytes) :
    Lookup.first storage key = Lookup.first ctx.trie.view (contractKey ctx.current.bytes key) := by
  have hm (value : Bytes) : (key, value) ∈ storage ↔ (key, value) ∈ raw := by
    rw [← hs, List.mem_toFinset]
  cases hv : Lookup.first ctx.trie.view (contractKey ctx.current.bytes key) with
  | none =>
    apply (Lookup.first_eq_none_iff storage key).mpr
    intro value hvalue
    exact (wf_view_lookup_none ctx raw hwf key).mp hv value ((hm value).mp hvalue)
  | some value =>
    have hvalue := (wf_view_lookup ctx raw hwf key value).mp hv
    apply Lookup.first_eq_some_of_mem _ _ _ ((hm value).mpr hvalue)
    intro v hv
    exact hwf.raw_keys_unique key v value ((hm v).mp hv) hvalue

/-- An actual in-memory reference agrees with every raw-storage list used by
`storage_write`; this does not assume that the entire host call succeeds. -/
theorem wf_memory_storage (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key value : Bytes) (accountNodes : Bool) (after : Near.TrieOverlay.State)
    (hget : getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes =
      .ok (after, some (.memory value))) :
    Lookup.first storage key = some value ∧ (key, value) ∈ raw := by
  have hv := getReference_memory_value ctx.trie (contractKey ctx.current.bytes key)
    accountNodes hwf.trie_changes_unique after value hget
  exact ⟨(wf_storage_lookup ctx raw hwf storage hs key).trans hv,
    (wf_view_lookup ctx raw hwf key value).mp hv⟩

/-- A selected overlay value supplies both the exact reference result and the
raw value consumed by storage accounting. -/
theorem wf_selected_value (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key value : Bytes) (accountNodes : Bool)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some (some value)) :
    getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes =
      .ok (ctx.trie, some (.memory value)) ∧
    Lookup.first storage key = some value ∧ (key, value) ∈ raw := by
  have hg := getReference_selected_value ctx.trie (contractKey ctx.current.bytes key)
    accountNodes hwf.trie_changes_unique value hselected
  exact ⟨hg.1, (wf_storage_lookup ctx raw hwf storage hs key).trans hg.2,
    (wf_view_lookup ctx raw hwf key value).mp hg.2⟩

/-- A selected tombstone supplies an absent reference and absent raw storage,
including when the base still contains the deleted cell. -/
theorem wf_selected_tombstone (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (storage : List (Bytes × Bytes)) (hs : storage.toFinset = raw)
    (key : Bytes) (accountNodes : Bool)
    (hselected : selected ctx.trie (contractKey ctx.current.bytes key) = some none) :
    getReference ctx.trie (contractKey ctx.current.bytes key) accountNodes = .ok (ctx.trie, none) ∧
    Lookup.first storage key = none ∧ ∀ value, (key, value) ∉ raw := by
  have hg := getReference_selected_tombstone ctx.trie (contractKey ctx.current.bytes key)
    accountNodes hwf.trie_changes_unique hselected
  exact ⟨hg.1, (wf_storage_lookup ctx raw hwf storage hs key).trans hg.2,
    (wf_view_lookup_none ctx raw hwf key).mp hg.2⟩

end NearInterface
