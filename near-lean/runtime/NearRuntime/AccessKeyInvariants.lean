import NearRuntime.Apply

namespace Near

attribute [local simp] bind pure throw Except.bind Except.pure Except.map

/-- Protocol authorization granted by the transaction's access key, independent
of the later balance and storage-staking checks. Signatures remain trusted. -/
def AccessKeyAuthorizes (tx : Transaction) (key : AccessKey) (cost : Fees.TxCost) : Prop :=
  match key.permission with
  | .fullAccess => True
  | .functionCall allowance receiver methods =>
    ∃ method args gas, tx.actions = [.functionCall method args gas 0] ∧
      tx.receiverId = receiver ∧ (methods.isEmpty || methods.contains method) = true ∧
      ∀ amount, allowance = some amount → cost.total ≤ amount

/-- Permission after charging the transaction's gas allowance. Unlimited keys
remain unlimited; full-access permissions are unchanged. -/
def chargedPermission (permission : AccessKeyPermission) (cost : Fees.TxCost) : AccessKeyPermission :=
  match permission with
  | .fullAccess => .fullAccess
  | .functionCall allowance receiver methods =>
    .functionCall (allowance.map (· - cost.total)) receiver methods

/-- Successful access-key validation both authorizes this transaction and sets
its nonce. Restricted keys can never authorize an attached deposit. -/
theorem validateTransactionAccessKey_authorizes (tx : Transaction) (key newKey : AccessKey)
    (cost : Fees.TxCost) (h : validateTransactionAccessKey tx key cost = .ok newKey) :
    newKey.nonce = tx.nonce ∧ AccessKeyAuthorizes tx key cost ∧
      newKey.permission = chargedPermission key.permission cost := by
  unfold validateTransactionAccessKey at h
  split at h
  · dsimp only [bind, pure, Except.pure] at h
    cases h
    simp_all [AccessKeyAuthorizes, chargedPermission]
  · split at h
    · dsimp only [bind, pure, throw, Except.bind, Except.pure, Except.map] at h
      split at h
      · simp_all
      · split at h
        · simp_all
        · split at h
          · simp_all
          · split at h
            · split at h
              · simp_all
              · cases h
                simp_all [AccessKeyAuthorizes, chargedPermission]
                tauto
            · cases h
              simp_all [AccessKeyAuthorizes, chargedPermission]
              tauto
    · simp_all

end Near
