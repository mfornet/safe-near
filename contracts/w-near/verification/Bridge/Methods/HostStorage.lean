import Bridge.Method
import Batteries.Tactic.OpenPrivate

/-!
# The host's contract storage is the trie overlay's view

`hostOf_storage_view`: under `Context.WF`, the value the initial host reads under a contract key
is the one the trie overlay holds under the raw `ContractData` key (`viewVal`). The change lists
must hold one change per key: `State.view` applies them in list order (a later change wins),
while `viewVal` takes the first. With `prospective = [(k, some a), (k, some b)]` the view holds
`b` under `k` and `viewVal` reads `a`. `TrieOverlay.insert` keeps one change per key, but
`Context.WF` does not say so, hence the `Nodup` hypotheses.
-/

namespace WNear.Binary
open Wasm Wasm.Near NearLogic NearInterface

open private applyChanges from NearInterface.TrieOverlay

private theorem find?_filter_ne {E : List (Bytes × Bytes)} {k k' : Bytes} (h : k' ≠ k) :
    (E.filter (·.1 != k')).find? (·.1 == k) = E.find? (·.1 == k) := by
  induction E with
  | nil => rfl
  | cons e E ih =>
    obtain ⟨a, b⟩ := e
    by_cases ha : a = k
    · subst ha
      simp [Ne.symm h]
    · by_cases ha' : a = k'
      · subst ha'
        simp [ha, ih]
      · simp [ha, ha', ih]

/-- Applying a change list with one change per key: the change of `k`, else the entries. -/
private theorem find?_applyChanges (E : List (Bytes × Bytes)) (C : Near.TrieOverlay.Changes)
    (hC : (C.map Prod.fst).Nodup) (k : Bytes) :
    ((applyChanges E C).find? (·.1 == k)).map (·.2) =
      match (C.find? (·.1 == k)).map Prod.snd with
      | some ov => ov
      | none => (E.find? (·.1 == k)).map (·.2) := by
  induction C generalizing E with
  | nil => rfl
  | cons c C ih =>
    obtain ⟨k', ov⟩ := c
    simp only [List.map_cons, List.nodup_cons] at hC
    have hstep : applyChanges E ((k', ov) :: C) =
        applyChanges (match ov with
          | none => E.filter (·.1 != k')
          | some v => (k', v) :: E.filter (·.1 != k')) C := rfl
    rw [hstep, ih _ hC.2]
    by_cases hk : k' = k
    · subst hk
      have hn : C.find? (·.1 == k') = none :=
        List.find?_eq_none.2 fun e he => by
          simp only [beq_iff_eq]
          rintro rfl
          exact hC.1 (List.mem_map.2 ⟨e, he, rfl⟩)
      have hf : (E.filter (·.1 != k')).find? (·.1 == k') = none :=
        List.find?_eq_none.2 fun e he => by
          have := (List.mem_filter.1 he).2
          simpa using this
      cases ov <;> simp [hn, hf]
    · have hc : List.find? (·.1 == k) ((k', ov) :: C) = C.find? (·.1 == k) := by
        simp [hk]
      rw [hc]
      cases ov <;> simp [hk, find?_filter_ne hk]

/-- With one change per key in each change list, the overlay's view reads `viewVal`. -/
theorem view_find?_eq_viewVal (s : Near.TrieOverlay.State)
    (hp : (s.prospective.map Prod.fst).Nodup) (hc : (s.committed.map Prod.fst).Nodup) (k : Bytes) :
    (s.view.find? (·.1 == k)).map (·.2) = viewVal s k := by
  unfold Near.TrieOverlay.State.view viewVal
  rw [find?_applyChanges _ _ hp, find?_applyChanges _ _ hc]
  rfl

/-- The records of `contractData` are the view's entries under the account's prefix. -/
theorem mem_contractData {trie : Near.TrieOverlay.State} {account key v : Bytes} :
    (key, v) ∈ contractData trie account ↔
      (Near.TrieOverlay.contractKey account key, v) ∈ trie.view := by
  unfold contractData Near.TrieOverlay.contractKey
  simp only [List.mem_toFinset, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq, Prod.mk.injEq, Prod.exists]
  constructor
  · rintro ⟨x, w, hx, hp, hd, rfl⟩
    obtain ⟨t, rfl⟩ := List.isPrefixOf_iff_prefix.1 hp
    simp at hd
    subst hd
    simpa using hx
  · intro h
    refine ⟨_, v, h, ?_, ?_, rfl⟩
    · exact List.isPrefixOf_iff_prefix.2 ⟨key, by simp⟩
    · simp

/-- The initial host reads the trie overlay's view of the contract's records. -/
theorem hostOf_storage_view (ctx : Context) (raw : RawStorage) (hwf : ctx.WF raw)
    (hp : (ctx.trie.prospective.map Prod.fst).Nodup)
    (hc : (ctx.trie.committed.map Prod.fst).Nodup) (key : List UInt8) :
    (hostOf ctx raw).storage key =
      viewVal ctx.trie (Near.TrieOverlay.contractKey (hostOf ctx raw).context.currentAccountId key) := by
  rw [← view_find?_eq_viewVal _ hp hc]
  show (raw.toList.find? (·.1 == key)).map (·.2) =
    (ctx.trie.view.find? (·.1 == Near.TrieOverlay.contractKey ctx.current.bytes key)).map (·.2)
  have hmem : ∀ v, (key, v) ∈ raw ↔
      (Near.TrieOverlay.contractKey ctx.current.bytes key, v) ∈ ctx.trie.view := fun v => by
    rw [← hwf.trie_storage]; exact mem_contractData
  cases hv : ctx.trie.view.find? (·.1 == Near.TrieOverlay.contractKey ctx.current.bytes key) with
  | none =>
    have hr : raw.toList.find? (·.1 == key) = none := List.find?_eq_none.2 fun ⟨k', v'⟩ he => by
      simp only [beq_iff_eq]
      rintro rfl
      have := List.find?_eq_none.1 hv _ ((hmem v').1 (Finset.mem_toList.1 he))
      simp at this
    simp [hr]
  | some p =>
    obtain ⟨k', v⟩ := p
    have hk : k' = Near.TrieOverlay.contractKey ctx.current.bytes key := by
      simpa using List.find?_some hv
    subst hk
    have hm := (hmem v).2 (List.mem_of_find?_eq_some hv)
    cases hr : raw.toList.find? (·.1 == key) with
    | none =>
      have := List.find?_eq_none.1 hr _ (Finset.mem_toList.2 hm)
      simp at this
    | some q =>
      obtain ⟨k'', v'⟩ := q
      have hk' : k'' = key := by simpa using List.find?_some hr
      subst hk'
      have := hwf.raw_keys_unique _ _ _ (Finset.mem_toList.1 (List.mem_of_find?_eq_some hr)) hm
      simp [this]

end WNear.Binary
