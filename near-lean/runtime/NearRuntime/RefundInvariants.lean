import NearRuntime.Refund
import NearRuntime.Fees
import NearRuntime.StateInvariants

namespace Near

/-- Every actual key update increases a finite allowance to the u128-saturated
sum, preserving the key's nonce and receiver/method restrictions. -/
theorem refundAllowanceUpdate_some (key updated : AccessKey) (deposit : Nat)
    (h : refundAllowanceUpdate key deposit = some updated) :
    ∃ allowance receiver methods, key.permission = .functionCall (some allowance) receiver methods ∧
      updated.nonce = key.nonce ∧
      updated.permission = .functionCall (some (min (allowance + deposit) (2 ^ 128 - 1))) receiver methods ∧
      allowance < min (allowance + deposit) (2 ^ 128 - 1) := by
  unfold refundAllowanceUpdate at h
  split at h
  · dsimp only at h
    split at h
    · simp only [Option.some.injEq] at h
      cases h
      exact ⟨_, _, _, by assumption, rfl, rfl, by assumption⟩
    · simp at h
  · simp at h

/-- Updating a finite allowance changes no serialized storage size. -/
theorem refundAllowanceUpdate_storageBytes (key updated : AccessKey) (pk : PublicKey) (deposit : Nat)
    (h : refundAllowanceUpdate key deposit = some updated) :
    accessKeyStorageBytes pk updated = accessKeyStorageBytes pk key := by
  obtain ⟨_, _, _, hp, _, hu, _⟩ := refundAllowanceUpdate_some key updated deposit h
  simp [accessKeyStorageBytes, functionCallPermissionBytes, hp, hu]

theorem refundAllowanceUpdate_zero (key : AccessKey) : refundAllowanceUpdate key 0 = none := by
  unfold refundAllowanceUpdate
  split
  · simp only [Nat.add_zero]
    exact ite_eq_right (Nat.not_lt.mpr (Nat.min_le_left _ _))
  · rfl

theorem ChainState.refundAllowance_zero (st : ChainState) (id : AccountId) (pk : PublicKey) :
    st.refundAllowance id pk 0 = st := by
  unfold ChainState.refundAllowance
  split
  · rfl
  · rw [refundAllowanceUpdate_zero]

/-- Exact finite-key restoration, including no-write zero/saturation cases. -/
theorem ChainState.refundAllowance_finite (st : ChainState) (id : AccountId) (pk : PublicKey)
    (key : AccessKey) (allowance deposit : Nat) (receiver : AccountId) (methods : List String)
    (hk : st.accessKey? id pk = some key)
    (hp : key.permission = .functionCall (some allowance) receiver methods)
    (hb : allowance ≤ 2 ^ 128 - 1) :
    (st.refundAllowance id pk deposit).accessKey? id pk =
      some { key with permission := .functionCall (some (min (allowance + deposit) (2 ^ 128 - 1))) receiver methods } := by
  have hl : allowance ≤ min (allowance + deposit) (2 ^ 128 - 1) :=
    Nat.le_min.mpr ⟨Nat.le_add_right _ _, hb⟩
  unfold ChainState.refundAllowance
  rw [hk]
  dsimp only
  unfold refundAllowanceUpdate
  rw [hp]
  dsimp only
  by_cases hg : allowance < min (allowance + deposit) (2 ^ 128 - 1)
  · rw [ite_eq_left hg]
    exact Assoc.lookup_insert_self _ _ _
  · have he : min (allowance + deposit) (2 ^ 128 - 1) = allowance := by omega
    have hsame : { key with permission := .functionCall (some allowance) receiver methods } = key := by
      cases key
      simp_all
    rw [ite_eq_right hg]
    simpa only [he, hsame] using hk

/-- Restoring metadata does not credit funds a second time or touch any state
component besides the access-key map. -/
theorem ChainState.refundAllowance_frame (st : ChainState) (id : AccountId) (pk : PublicKey) (deposit : Nat) :
    { st.refundAllowance id pk deposit with accessKeys := st.accessKeys } = st := by
  unfold ChainState.refundAllowance
  split
  · rfl
  · split <;> rfl

theorem ChainState.refundAllowance_totalBalance (st : ChainState) (id : AccountId) (pk : PublicKey) (deposit : Nat) :
    (st.refundAllowance id pk deposit).totalBalance = st.totalBalance := by
  unfold ChainState.refundAllowance
  split
  · rfl
  · split <;> rfl

theorem ChainState.MapsUnique.refundAllowance {st : ChainState} (h : st.MapsUnique)
    (id : AccountId) (pk : PublicKey) (deposit : Nat) : (st.refundAllowance id pk deposit).MapsUnique := by
  unfold ChainState.refundAllowance
  split
  · exact h
  · split
    · exact h
    · exact h.setAccessKey id pk _

theorem ChainState.refundAllowance_missing (st : ChainState) (id : AccountId) (pk : PublicKey) (deposit : Nat)
    (h : st.accessKey? id pk = none) : st.refundAllowance id pk deposit = st := by
  simp [ChainState.refundAllowance, h]

/-- No other key can receive the refund, even when its allowance is finite. -/
theorem ChainState.refundAllowance_other_key (st : ChainState) (id other : AccountId)
    (pk otherPk : PublicKey) (deposit : Nat) (hne : (id, pk) ≠ (other, otherPk)) :
    (st.refundAllowance id pk deposit).accessKey? other otherPk = st.accessKey? other otherPk := by
  unfold ChainState.refundAllowance
  split
  · rfl
  · split
    · rfl
    · exact Assoc.lookup_insert_ne _ _ _ _ hne

/-- Delayed refunds cannot reset a current key's transaction nonce. -/
theorem ChainState.refundAllowance_nonce (st : ChainState) (id : AccountId) (pk : PublicKey) (deposit : Nat) :
    ((st.refundAllowance id pk deposit).accessKey? id pk).map (·.nonce) =
      (st.accessKey? id pk).map (·.nonce) := by
  unfold ChainState.refundAllowance
  split
  · rfl
  · rename_i key hk
    split
    · rfl
    · rename_i updated hu
      have hn := (refundAllowanceUpdate_some key updated deposit hu)
      obtain ⟨_, _, _, _, hn, _, _⟩ := hn
      change (Assoc.lookup (Assoc.insert st.accessKeys (id, pk) updated) (id, pk)).map (·.nonce) = _
      simp only [Assoc.lookup_insert_self, Option.map_some, hk, hn]

/-- A generated gas refund retains its key marker and consumes one receipt id. -/
theorem gasRefundReceipt_marker (st : ChainState) (id : AccountId) (pk : PublicKey) (amount : Nat) :
    (gasRefundReceipt st id pk amount).1.isGasRefund = true ∧
      (gasRefundReceipt st id pk amount).2.nextId = st.nextId + 1 := by
  simp [gasRefundReceipt, ChainState.freshId, Receipt.isGasRefund, Receipt.isRefund]

/-- A balance refund to an ordinary account never carries the key marker. -/
theorem refundReceipt_balance_marker (st : ChainState) (id : AccountId) (amount : Nat)
    (hne : systemAccount ≠ id) : (refundReceipt st id amount).1.isGasRefund = false := by
  simp [refundReceipt, ChainState.freshId, Receipt.isGasRefund, Receipt.isRefund, hne]

end Near
