import Proofs.StateLemmas

namespace WNear

/-- Distinct account IDs cannot alias the same storage key. -/
theorem accountKey_injective {a b : AccountId} (h : accountKey a = accountKey b) : a = b := by
  apply Subtype.ext
  exact Borsh.string_injective (List.append_cancel_left h)

/-- Account keys have at least seven bytes; the state key has five. -/
theorem accountKey_ne_stateKey (a : AccountId) : accountKey a ≠ stateKey := by
  intro h
  have e := congrArg List.length h
  have ha := a.property
  simp only [isValidAccountId, Bool.and_eq_true, decide_eq_true_eq] at ha
  simp only [accountKey, accountsPrefix, stateKey, Borsh.string, Borsh.bytes,
    Borsh.u32, List.length_append, Borsh.leBytes_length, Borsh.byteArray_toList_length] at e
  have hp : "a".toUTF8.size = 1 := by decide
  have hs : "STATE".toUTF8.size = 5 := by decide
  rw [hp, hs] at e
  change (2 ≤ a.val.toUTF8.size ∧ a.val.toUTF8.size ≤ 64) ∧ _ at ha
  omega

/-- Exact membership of an account record, without silently discarding values. -/
theorem mem_encode_account {s : State} {a : AccountId} {v : Borsh.Bytes} :
    (accountKey a, v) ∈ encode s ↔ a ∈ s.registered ∧ v = Borsh.u128 (s.balance a) := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact False.elim (accountKey_ne_stateKey a (congrArg Prod.fst h))
    · obtain ⟨b, hb, e⟩ := Finset.mem_image.mp h
      have hab := accountKey_injective (congrArg Prod.fst e)
      subst b
      exact ⟨hb, (congrArg Prod.snd e).symm⟩
  · rintro ⟨ha, rfl⟩
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a, ha, rfl⟩)

theorem mem_encode_header {s : State} {v : Borsh.Bytes} :
    (stateKey, v) ∈ encode s ↔ v = header s := by
  constructor
  · intro h
    rcases Finset.mem_insert.mp h with h | h
    · exact congrArg Prod.snd h
    · obtain ⟨a, _, e⟩ := Finset.mem_image.mp h
      exact False.elim (accountKey_ne_stateKey a (congrArg Prod.fst e))
  · rintro rfl
    exact Finset.mem_insert_self _ _

/-- The fixed-width header uniquely determines supply and measured usage. -/
theorem header_injective_fields {s t : State} (hs : s.WF) (ht : t.WF)
    (h : header s = header t) :
    s.totalSupply = t.totalSupply ∧ s.accountStorageUsage = t.accountStorageUsage := by
  simp only [header, List.append_assoc] at h
  have hparts := List.append_cancel_left h
  have hlength : (Borsh.u128 s.totalSupply).length = (Borsh.u128 t.totalSupply).length := by
    simp only [Borsh.u128, Borsh.leBytes_length]
  have hsupply := List.append_inj_left hparts hlength
  have husage := List.append_inj_right hparts hlength
  exact ⟨Borsh.leBytes_injective_of_lt hs.totalSupply_lt ht.totalSupply_lt hsupply,
    Borsh.leBytes_injective_of_lt hs.usage_lt ht.usage_lt husage⟩

/-- Equal raw storage determines the entire well-formed mathematical state,
including the zero balances of accounts without records. -/
theorem encode_injective_of_wf {s t : State} (hs : s.WF) (ht : t.WF)
    (h : encode s = encode t) : s = t := by
  have hheader : header s = header t := by
    apply mem_encode_header.mp
    rw [← h]
    exact Finset.mem_insert_self _ _
  obtain ⟨hsupply, husage⟩ := header_injective_fields hs ht hheader
  have hregistered : s.registered = t.registered := by
    apply Finset.ext
    intro a
    constructor
    · intro ha
      have hm := mem_encode_account.mpr ⟨ha, rfl (a := Borsh.u128 (s.balance a))⟩
      rw [h] at hm
      exact (mem_encode_account.mp hm).1
    · intro ha
      have hm := mem_encode_account.mpr ⟨ha, rfl (a := Borsh.u128 (t.balance a))⟩
      rw [← h] at hm
      exact (mem_encode_account.mp hm).1
  have hbalance : s.balance = t.balance := by
    funext a
    by_cases ha : a ∈ s.registered
    · have hm := mem_encode_account.mpr ⟨ha, rfl (a := Borsh.u128 (s.balance a))⟩
      rw [h] at hm
      have he := (mem_encode_account.mp hm).2
      exact Borsh.leBytes_injective_of_lt (hs.balance_lt a) (ht.balance_lt a) he
    · rw [hs.unregistered_zero a ha, ht.unregistered_zero a (by rwa [← hregistered])]
  cases s
  cases t
  simp_all only [State.mk.injEq]

end WNear
