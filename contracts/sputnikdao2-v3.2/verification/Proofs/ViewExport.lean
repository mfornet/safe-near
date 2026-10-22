import Model.ViewExport
import Proofs.ExportWrapper

namespace SputnikDAO2

theorem available_view_saturates_and_preserves_storage
    (raw : BountyRawTrie) (locked deposit balance byteCost usage : Nat) :
    runAvailableView raw (some locked) deposit balance byteCost usage =
      some (viewAvailable balance byteCost usage locked, raw) := by
  have hi : findDAOExport "get_available_amount" =
      some ⟨"get_available_amount", .view, false, false⟩ := by decide
  simp [runAvailableView, runGeneratedViewWrapper, hi, runViewWrapper]

theorem available_view_zero_when_reserves_exceed_balance
    (raw : BountyRawTrie) (locked deposit balance byteCost usage : Nat)
    (hreserve : balance ≤ viewLockedStorage byteCost usage + locked) :
    runAvailableView raw (some locked) deposit balance byteCost usage =
      some (0, raw) := by
  rw [available_view_saturates_and_preserves_storage]
  simp [viewAvailable, Nat.sub_sub]
  omega

theorem locked_storage_view_preserves_storage
    (raw : BountyRawTrie) (deposit byteCost usage : Nat) :
    runLockedStorageView raw (some ()) deposit byteCost usage =
      some (viewLockedStorage byteCost usage, raw) := by
  have hi : findDAOExport "get_locked_storage_amount" =
      some ⟨"get_locked_storage_amount", .view, false, false⟩ := by decide
  simp [runLockedStorageView, runGeneratedViewWrapper, hi, runViewWrapper]

theorem delegation_balance_view_defaults_to_zero
    (raw : BountyRawTrie) (deposit : Nat) :
    runDelegationBalanceView raw (some none) deposit = some (0, raw) := by
  have hi : findDAOExport "delegation_balance_of" =
      some ⟨"delegation_balance_of", .view, false, false⟩ := by decide
  simp [runDelegationBalanceView, runGeneratedViewWrapper, hi,
    runViewWrapper, viewDelegationBalance]

theorem delegation_ratio_view_defaults_to_zero_balance
    (raw : BountyRawTrie) (total deposit : Nat) :
    runDelegationRatioView raw (some (none, total)) deposit =
      some ((0, total), raw) := by
  have hi : findDAOExport "delegation_balance_ratio" =
      some ⟨"delegation_balance_ratio", .view, false, false⟩ := by decide
  simp [runDelegationRatioView, runGeneratedViewWrapper, hi,
    runViewWrapper, viewDelegationRatio]

theorem delegation_supply_view_reads_total
    (raw : BountyRawTrie) (total deposit : Nat) :
    runDelegationSupplyView raw (some total) deposit = some (total, raw) := by
  have hi : findDAOExport "delegation_total_supply" =
      some ⟨"delegation_total_supply", .view, false, false⟩ := by decide
  simp [runDelegationSupplyView, runGeneratedViewWrapper, hi, runViewWrapper]

theorem has_blob_view_reads_raw_key
    (raw : BountyRawTrie) (deposit : Nat) (digest : BountyBytes)
    (hlen : digest.length = 32) :
    runHasBlobView raw (some ()) deposit digest =
      some ((raw digest).isSome, raw) := by
  have hi : findDAOExport "has_blob" =
      some ⟨"has_blob", .view, false, false⟩ := by decide
  simp [runHasBlobView, hlen, runGeneratedViewWrapper, hi,
    runViewWrapper]

theorem has_blob_view_missing_raw_key_is_false
    (raw : BountyRawTrie) (deposit : Nat) (digest : BountyBytes)
    (hlen : digest.length = 32) (hmissing : raw digest = none) :
    runHasBlobView raw (some ()) deposit digest = some (false, raw) := by
  rw [has_blob_view_reads_raw_key raw deposit digest hlen]
  simp [hmissing]

theorem version_view_preserves_storage (raw : BountyRawTrie) (deposit : Nat) :
    runVersionView raw (some ()) deposit = some ("2.3.1", raw) := by
  have hi : findDAOExport "version" =
      some ⟨"version", .view, false, false⟩ := by decide
  simp [runVersionView, runGeneratedViewWrapper, hi, runViewWrapper, viewVersion]

theorem config_view_missing_aborts {α : Type}
    (raw : BountyRawTrie) (deposit : Nat) :
    runConfigView (α := α) raw (some none) deposit = none := by
  simp [runConfigView, readConfig]

theorem policy_view_rejects_legacy {α : Type}
    (raw : BountyRawTrie) (deposit : Nat) (council : List String) :
    runPolicyView (α := α) raw (some (some (.default council))) deposit = none := by
  simp [runPolicyView, readPolicy, Except.toOption]

theorem policy_view_reads_current {α : Type}
    (raw : BountyRawTrie) (deposit : Nat) (policy : α) :
    runPolicyView raw (some (some (.current policy))) deposit =
      some (policy, raw) := by
  have hi : findDAOExport "get_policy" =
      some ⟨"get_policy", .view, false, false⟩ := by decide
  simp [runPolicyView, readPolicy, Except.toOption,
    runGeneratedViewWrapper, hi, runViewWrapper]

theorem staking_view_absent_is_empty (raw : BountyRawTrie) (deposit : Nat) :
    runNamedStakingView raw (some none) deposit = some ("", raw) := by
  have hi : findDAOExport "get_staking_contract" =
      some ⟨"get_staking_contract", .view, false, false⟩ := by decide
  simp [runNamedStakingView, runGeneratedViewWrapper, hi, runViewWrapper,
    viewStakingContract]

theorem factory_view_malformed_aborts
    (raw : BountyRawTrie) (deposit : Nat) (current : String) :
    runFactoryInfoView raw (some ()) deposit .malformed current = none := by
  simp [runFactoryInfoView, factoryInfoForAccount, effectiveFactory]

theorem factory_view_stored_info (raw : BountyRawTrie) (deposit : Nat)
    (info : FactoryInfo) (current : String) :
    runFactoryInfoView raw (some ()) deposit (.stored info) current =
      some (info, raw) := by
  have hi : findDAOExport "get_factory_info" =
      some ⟨"get_factory_info", .view, false, false⟩ := by decide
  simp [runFactoryInfoView, factoryInfoForAccount, effectiveFactory,
    runGeneratedViewWrapper, hi, runViewWrapper]

theorem proposals_view_overflow_aborts {α : Type}
    (raw : BountyRawTrie) (lastId deposit fromIndex limit : Nat)
    (lookup : Nat → Option α) (hoverflow : maxU64 < fromIndex + limit) :
    runProposalsView raw (some lastId) deposit fromIndex limit lookup = none := by
  simp [runProposalsView, viewPage, Nat.not_le.mpr hoverflow]

theorem bounties_view_overflow_aborts {α : Type}
    (raw : BountyRawTrie) (lastId deposit fromIndex limit : Nat)
    (lookup : Nat → Option α) (hoverflow : maxU64 < fromIndex + limit) :
    runBountiesView raw (some lastId) deposit fromIndex limit lookup = none := by
  simp [runBountiesView, viewPage, Nat.not_le.mpr hoverflow]

theorem proposal_view_missing_aborts {α : Type}
    (raw : BountyRawTrie) (deposit id : Nat) :
    runProposalView (α := α) raw (some ()) deposit id none = none := by
  simp [runProposalView, viewOne]

theorem bounty_view_missing_aborts {α : Type}
    (raw : BountyRawTrie) (deposit id : Nat) :
    runBountyView (α := α) raw (some ()) deposit id none = none := by
  simp [runBountyView, viewOne]

theorem bounty_claims_view_absent_is_empty {α : Type}
    (raw : BountyRawTrie) (deposit : Nat) :
    runBountyClaimsView (α := α) raw (some ()) deposit none =
      some ([], raw) := by
  have hi : findDAOExport "get_bounty_claims" =
      some ⟨"get_bounty_claims", .view, false, false⟩ := by decide
  simp [runBountyClaimsView, runGeneratedViewWrapper, hi, runViewWrapper,
    viewBountyClaims]

theorem bounty_claim_count_view_absent_is_zero
    (raw : BountyRawTrie) (deposit : Nat) :
    runBountyClaimCountView raw (some ()) deposit none = some (0, raw) := by
  have hi : findDAOExport "get_bounty_number_of_claims" =
      some ⟨"get_bounty_number_of_claims", .view, false, false⟩ := by decide
  simp [runBountyClaimCountView, runGeneratedViewWrapper, hi, runViewWrapper,
    viewBountyClaimCount]

end SputnikDAO2
