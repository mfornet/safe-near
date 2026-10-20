import NearRuntime.Apply
import NearRuntime.StateInvariants
import NearRuntime.AccessKeyInvariants
import NearRuntime.NonceInvariants

namespace Near
open Wasm.Near

attribute [local simp] bind pure throw Except.bind Except.pure Except.map

/-- Every successful conversion reaches the shared commit operation with the
current signer account and a balance sufficient for the exact transaction cost. -/
theorem convertTransaction_success_commit (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    ∃ signer newKey, st.account? tx.signerId = some signer ∧
      (Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions).total ≤ signer.amount ∧
      commitTransaction st tx signer newKey
        (Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions) = (st', receipt, cost) ∧
      ∃ key, st.accessKey? tx.signerId tx.publicKey = some key ∧ key.nonce < tx.nonce ∧
        validateTransactionAccessKey tx key
          (Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions) = .ok newKey ∧
        verifyNonce tx.nonce key.nonce (some ap.blockHeight) tx.nonceMode = .ok () ∧
        (tx.nonceMode = .strict → cfg.strictNonceEnabled = true) := by
  cases hvalidation : validateTransactionActions cfg tx.actions with
  | error error => simp [convertTransaction, hvalidation] at h
  | ok accepted =>
    cases accepted
    have h : convertTransactionCore cfg ap st tx = .ok (st', receipt, cost) := by
      simpa [convertTransaction, hvalidation] using h
    by_cases hversion : tx.versionSupported cfg = false
    · by_cases hg : tx.nonceMode = .strict ∧ cfg.strictNonceEnabled = false
      · simp [convertTransactionCore, hg] at h
      · simp [convertTransactionCore, hg, hversion] at h
    ·
      by_cases hg : tx.nonceMode = .strict ∧ cfg.strictNonceEnabled = false
      · simp [convertTransactionCore, hg] at h
      · have hgate : tx.nonceMode = .strict → cfg.strictNonceEnabled = true := by
          intro hm
          cases hf : cfg.strictNonceEnabled <;> simp [hf, hm] at hg ⊢
        cases hsize : tx.sizeForLimits? cfg with
        | none => simp [convertTransactionCore, hversion, hg, hsize] at h
        | some size =>
          by_cases hlarge : size > cfg.wasm.limits.maxTransactionSize
          · simp [convertTransactionCore, hversion, hg, hsize, hlarge] at h
          ·
            cases hs : st.account? tx.signerId with
            | none => simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs] at h
            | some signer =>
              cases hk : st.accessKey? tx.signerId tx.publicKey with
              | none => simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk] at h
              | some key =>
                cases hvn : verifyNonce tx.nonce key.nonce (some ap.blockHeight) tx.nonceMode with
                | error err => simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk, hvn] at h
                | ok accepted =>
                  cases accepted
                  have hn := verifyNonce_increases tx.nonce key.nonce (some ap.blockHeight) tx.nonceMode hvn
                  by_cases ha : tx.actions.length > cfg.wasm.limits.maxActionsPerReceipt
                  · simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk, hvn, ha] at h
                  · let expected := Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions
                    have he : Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions = expected := rfl
                    by_cases hb : signer.amount < expected.total
                    · simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk, hvn, ha, he, hb] at h
                    · cases hal : validateTransactionAllowance tx key expected with
                      | error err => simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk, hvn, ha, he, hb, hal] at h
                      | ok accepted =>
                        cases accepted
                        by_cases hd : storageStakeDeficit cfg { signer with amount := signer.amount - expected.total } > 0
                        · simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk, hvn, ha, he, hb, hal, hd] at h
                        · cases hv : validateTransactionAccessKey tx key expected with
                          | error err => simp [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk, hvn, ha, he, hb, hal, hd, hv] at h
                          | ok newKey =>
                            refine ⟨signer, newKey, rfl, ?_, ?_, key, rfl, hn, hv, hvn, hgate⟩
                            · change expected.total ≤ signer.amount
                              omega
                            · simpa [convertTransactionCore, hversion, hg, hsize, hlarge, hs, hk, hvn, ha, he, hb, hal, hd, hv] using h

/-- Every successful public conversion passed the stateless action rules. -/
theorem convertTransaction_actions_valid (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    validateTransactionActions cfg tx.actions = .ok () := by
  cases hv : validateTransactionActions cfg tx.actions with
  | error error => simp [convertTransaction, hv] at h
  | ok accepted => cases accepted; rfl

/-- A bad action list fails before stateful admission is evaluated. -/
theorem convertTransaction_actions_error (cfg : RuntimeConfig) (ap : ApplyState)
    (st : ChainState) (tx : Transaction) (error : ActionsValidationError)
    (h : validateTransactionActions cfg tx.actions = .error error) :
    convertTransaction cfg ap st tx = .error (.actionsValidation error) := by
  rw [convertTransaction, h]
  rfl

/-- Successful conversion uses a supported native transaction envelope. -/
theorem convertTransaction_version_supported (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    tx.versionSupported cfg = true := by
  cases hvalidation : validateTransactionActions cfg tx.actions with
  | error error => simp [convertTransaction, hvalidation] at h
  | ok accepted =>
    cases accepted
    have h : convertTransactionCore cfg ap st tx = .ok (st', receipt, cost) := by
      simpa [convertTransaction, hvalidation] using h
    cases hv : tx.versionSupported cfg with
    | false =>
      by_cases hg : tx.nonceMode = .strict ∧ cfg.strictNonceEnabled = false
      · simp [convertTransactionCore, hg] at h
      · simp [convertTransactionCore, hg, hv] at h
    | true => rfl

/-- Every accepted public transaction fits the protocol's chosen Borsh size limit. -/
theorem convertTransaction_size_bound (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    ∃ size, tx.sizeForLimits? cfg = some size ∧ size ≤ cfg.wasm.limits.maxTransactionSize := by
  cases ha : validateTransactionActions cfg tx.actions with
  | error error => simp [convertTransaction, ha] at h
  | ok accepted =>
    cases accepted
    have h : convertTransactionCore cfg ap st tx = .ok (st', receipt, cost) := by
      simpa [convertTransaction, ha] using h
    by_cases hg : tx.nonceMode = .strict ∧ cfg.strictNonceEnabled = false
    · simp [convertTransactionCore, hg] at h
    · by_cases hv : tx.versionSupported cfg = false
      · simp [convertTransactionCore, hg, hv] at h
      · cases hs : tx.sizeForLimits? cfg with
        | none => simp [convertTransactionCore, hg, hv, hs] at h
        | some size =>
          by_cases hl : size > cfg.wasm.limits.maxTransactionSize
          · simp [convertTransactionCore, hg, hv, hs, hl] at h
          · exact ⟨size, rfl, Nat.le_of_not_gt hl⟩

/-- The commit operation debits exactly its validated transaction cost, leaving
locked funds unchanged. Unique account keys prevent hidden duplicate balances. -/
theorem commitTransaction_totalBalance (st : ChainState) (tx : Transaction)
    (signer : Account) (newKey : AccessKey) (cost : Fees.TxCost)
    (hwf : st.AccountsUnique) (hs : st.account? tx.signerId = some signer)
    (hfunded : cost.total ≤ signer.amount) :
    (commitTransaction st tx signer newKey cost).1.totalBalance + cost.total = st.totalBalance := by
  have hb := ChainState.totalBalance_setAccount st tx.signerId
    { signer with amount := signer.amount - cost.total } signer hwf hs
  change (st.setAccount tx.signerId { signer with amount := signer.amount - cost.total }).totalBalance + cost.total = _
  dsimp only at hb
  omega

/-- Transaction conversion conserves account funds plus the transaction debit. -/
theorem convertTransaction_totalBalance (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (hwf : st.AccountsUnique)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    st'.totalBalance + cost.total = st.totalBalance := by
  obtain ⟨signer, newKey, hs, hfunded, hc, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost h
  have hb := commitTransaction_totalBalance st tx signer newKey _ hwf hs hfunded
  have hcost := congrArg (fun result => result.2.2) hc
  have hstate := congrArg (fun result => result.1) hc
  change Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions = cost at hcost
  rw [hstate] at hb
  have hcostTotal := congrArg Fees.TxCost.total hcost
  rw [hcostTotal] at hb
  exact hb

/-- All finite-map key domains remain unique after transaction commitment. -/
theorem commitTransaction_mapsUnique (st : ChainState) (tx : Transaction)
    (signer : Account) (newKey : AccessKey) (cost : Fees.TxCost) (h : st.MapsUnique) :
    (commitTransaction st tx signer newKey cost).1.MapsUnique :=
  ((h.setAccount tx.signerId { signer with amount := signer.amount - cost.total }).setAccessKey
    tx.signerId tx.publicKey newKey).freshId

theorem convertTransaction_mapsUnique (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (hwf : st.MapsUnique)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) : st'.MapsUnique := by
  obtain ⟨signer, newKey, _, _, hc, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost h
  have hs := congrArg (fun result => result.1) hc
  change (commitTransaction st tx signer newKey _).1 = st' at hs
  rw [← hs]
  exact commitTransaction_mapsUnique st tx signer newKey _ hwf

/-- Transaction commitment changes no other account, even without uniqueness. -/
theorem commitTransaction_account_frame (st : ChainState) (tx : Transaction)
    (signer : Account) (newKey : AccessKey) (cost : Fees.TxCost) (other : AccountId)
    (hne : tx.signerId ≠ other) :
    (commitTransaction st tx signer newKey cost).1.account? other = st.account? other :=
  ChainState.account?_setAccount_ne _ _ _ _ hne

theorem convertTransaction_account_frame (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (other : AccountId) (hne : tx.signerId ≠ other)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    st'.account? other = st.account? other := by
  obtain ⟨signer, newKey, _, _, hc, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost h
  have hs := congrArg (fun result => result.1) hc
  change (commitTransaction st tx signer newKey _).1 = st' at hs
  rw [← hs]
  exact commitTransaction_account_frame st tx signer newKey _ other hne

/-- The generated receipt uses the old counter and advances it exactly once.
A global freshness theorem additionally needs bounds on every in-flight id. -/
theorem convertTransaction_receipt_counter (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    receipt.receiptId = st.nextId ∧ st'.nextId = st.nextId + 1 := by
  obtain ⟨signer, newKey, _, _, hc, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost h
  have hs := congrArg (fun result => result.1.nextId) hc
  have hr := congrArg (fun result => result.2.1.receiptId) hc
  constructor
  · exact hr.symm
  · exact hs.symm

/-- The transaction debit backs the new receipt and the gas burnt at conversion.
The reserved system sender is excluded so the new receipt is not a free refund. -/
theorem convertTransaction_conservation (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (hwf : st.AccountsUnique) (hnotSystem : tx.signerId ≠ systemAccount)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    st'.totalBalance + Fees.receiptFunds cfg receipt + cost.gasBurnt * ap.gasPrice = st.totalBalance := by
  obtain ⟨signer, newKey, hs, hfunded, hc, _⟩ := convertTransaction_success_commit cfg ap st st' tx receipt cost h
  let expected := Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions
  have hb := commitTransaction_totalBalance st tx signer newKey expected hwf hs hfunded
  have hp : Fees.receiptFunds cfg (commitTransaction st tx signer newKey expected).2.1 +
      expected.gasBurnt * ap.gasPrice = expected.total := by
    simp [commitTransaction, Fees.receiptFunds, Receipt.isRefund, hnotSystem, expected, Fees.txCost]
    omega
  have identity : (commitTransaction st tx signer newKey expected).1.totalBalance +
      Fees.receiptFunds cfg (commitTransaction st tx signer newKey expected).2.1 +
      expected.gasBurnt * ap.gasPrice = st.totalBalance := by omega
  have hstate := congrArg (fun result => result.1) hc
  have hreceipt := congrArg (fun result => result.2.1) hc
  have hcost := congrArg (fun result => result.2.2) hc
  change expected = cost at hcost
  change (commitTransaction st tx signer newKey expected).1 = st' at hstate
  change (commitTransaction st tx signer newKey expected).2.1 = receipt at hreceipt
  rw [hstate, hreceipt, hcost] at identity
  exact identity

/-- Successful conversion installs the validated key and advances its nonce.
For function-call keys, authorization includes receiver/method restrictions,
a zero deposit, and a sufficient allowance. -/
theorem convertTransaction_authorized (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    ∃ oldKey newKey, st.accessKey? tx.signerId tx.publicKey = some oldKey ∧
      st'.accessKey? tx.signerId tx.publicKey = some newKey ∧
      newKey.nonce = tx.nonce ∧ oldKey.nonce < newKey.nonce ∧ AccessKeyAuthorizes tx oldKey cost ∧
      newKey.permission = chargedPermission oldKey.permission cost := by
  obtain ⟨signer, newKey, _, _, hc, key, hk, hn, hv, _, _⟩ :=
    convertTransaction_success_commit cfg ap st st' tx receipt cost h
  have ha := validateTransactionAccessKey_authorizes tx key newKey _ hv
  have hcost := congrArg (fun result => result.2.2) hc
  change Fees.txCost cfg ap.gasPrice tx.signerId tx.receiverId tx.actions = cost at hcost
  have hstate := congrArg (fun result => result.1) hc
  change (commitTransaction st tx signer newKey _).1 = st' at hstate
  refine ⟨key, newKey, hk, ?_, ha.1, by omega, ?_, ?_⟩
  · rw [← hstate]
    change Assoc.lookup (Assoc.insert st.accessKeys (tx.signerId, tx.publicKey) newKey)
      (tx.signerId, tx.publicKey) = some newKey
    exact Assoc.lookup_insert_self _ _ _
  · simpa only [hcost] using ha.2.1
  · simpa only [hcost] using ha.2.2

/-- Successful admission has the reference's nonce ordering and u64 ceiling;
strict requests additionally require the protocol feature. -/
theorem convertTransaction_nonce_bounds (cfg : RuntimeConfig) (ap : ApplyState)
    (st st' : ChainState) (tx : Transaction) (receipt : Receipt) (cost : Fees.TxCost)
    (h : convertTransaction cfg ap st tx = .ok (st', receipt, cost)) :
    ∃ key, st.accessKey? tx.signerId tx.publicKey = some key ∧
      NonceOrdered tx.nonceMode tx.nonce key.nonce ∧
      tx.nonce < nonceUpperBound ap.blockHeight ∧ tx.nonce < 2 ^ 64 - 1 ∧
      (tx.nonceMode = .strict → cfg.strictNonceEnabled = true) := by
  obtain ⟨_, _, _, _, _, key, hk, _, _, hvn, hg⟩ :=
    convertTransaction_success_commit cfg ap st st' tx receipt cost h
  exact ⟨key, hk, ((verifyNonce_success_iff _ _ _ _).mp hvn).1,
    verifyNonce_below_ceiling _ _ _ _ hvn, verifyNonce_u64 _ _ _ _ hvn, hg⟩

end Near
