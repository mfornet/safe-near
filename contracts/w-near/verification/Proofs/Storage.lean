import Spec.Storage
import Proofs.StateLemmas

namespace WNear

@[blueprint "thm:project-encode"
  (statement := /-- \cref{spec:project-encode} holds. -/)]
theorem project_encode : ProjectEncode := by
  sorry

@[blueprint "thm:storage-coverage"
  (statement := /-- \cref{spec:storage-coverage} holds. -/)]
theorem storage_coverage : StorageCoverage := by
  intro cfg s hinv
  have entry_bound (a : AccountId) :
      cfg.recordBytes (accountKey a, Borsh.u128 (s.balance a)) ≤ s.accountStorageUsage := by
    have ha := a.property
    simp only [isValidAccountId, Bool.and_eq_true, decide_eq_true_eq] at ha
    rw [hinv.usage]
    simp only [Config.recordBytes, accountKey, List.length_append, Borsh.string,
      Borsh.bytes, Borsh.u32, Borsh.u128, Borsh.leBytes_length, accountsPrefix,
      Config.measuredAccountStorageUsage, Config.accountEntryBytes, maxAccountIdBytes]
    simp only [Borsh.byteArray_toList_length]
    have hp : "a".toUTF8.size = 1 := by decide
    rw [hp]
    change 1 + (4 + a.val.toUTF8.size) + 16 + cfg.extraBytesPerRecord ≤
      (1 + 4 + 64) + 16 + cfg.extraBytesPerRecord
    change (2 ≤ a.val.toUTF8.size ∧ a.val.toUTF8.size ≤ 64) ∧ _ at ha
    omega
  let records := s.registered.image fun a => (accountKey a, Borsh.u128 (s.balance a))
  have insert_bound :
      (∑ e ∈ insert (stateKey, header s) records, cfg.recordBytes e) ≤
      cfg.recordBytes (stateKey, header s) + ∑ e ∈ records, cfg.recordBytes e := by
    by_cases h : (stateKey, header s) ∈ records
    · simp only [Finset.insert_eq_of_mem h]
      omega
    · rw [Finset.sum_insert h]
  calc
    storageUsage cfg (encode s) ≤ cfg.recordBytes (stateKey, header s) +
        ∑ e ∈ records, cfg.recordBytes e := insert_bound
    _ ≤ cfg.recordBytes (stateKey, header s) +
        ∑ a ∈ s.registered, cfg.recordBytes (accountKey a, Borsh.u128 (s.balance a)) := by
      exact Nat.add_le_add_left (Finset.sum_image_le_of_nonneg (fun _ _ => Nat.zero_le _)) _
    _ ≤ cfg.recordBytes (stateKey, header s) + s.registered.card * s.accountStorageUsage := by
      apply Nat.add_le_add_left
      calc
        _ ≤ ∑ _a ∈ s.registered, s.accountStorageUsage := Finset.sum_le_sum (fun a _ => entry_bound a)
        _ = _ := by simp


end WNear
