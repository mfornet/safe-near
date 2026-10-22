import Model.Initialize

namespace SputnikDAO2

theorem initialized_policy_readable (config : String)
    (policy : StoredPolicy String) (makeDefault : List String → String)
    (predecessor : String) :
    ∃ current, readPolicy
      (some (initializeDAO config policy makeDefault predecessor).policy) = .ok current := by
  cases policy <;> simp [initializeDAO, upgradeStoredPolicy, readPolicy]

theorem initialized_current_policy_preserved (config current predecessor : String)
    (makeDefault : List String → String) :
    (initializeDAO config (.current current) makeDefault predecessor).policy =
      .current current := by rfl

theorem initialized_default_policy_expanded (config predecessor : String)
    (council : List String) (makeDefault : List String → String) :
    (initializeDAO config (.default council) makeDefault predecessor).policy =
      .current (makeDefault council) := by rfl

theorem initialized_ids_locks_and_collections_empty (config : String)
    (policy : StoredPolicy String) (makeDefault : List String → String)
    (predecessor : String) :
    let dao := initializeDAO config policy makeDefault predecessor
    dao.lockedAmount = 0 ∧ dao.stakingId = none ∧
    dao.totalDelegationAmount = 0 ∧ dao.delegations = [] ∧
    dao.lastProposalId = 0 ∧ dao.proposals = [] ∧
    dao.lastBountyId = 0 ∧ dao.bounties = [] ∧
    dao.bountyClaimers = [] ∧ dao.bountyClaimsCount = [] ∧
    dao.blobs = [] ∧ dao.actionsLog = [] := by
  simp [initializeDAO]

theorem initialized_factory_and_version (config predecessor current : String)
    (policy : StoredPolicy String) (makeDefault : List String → String) :
    let dao := initializeDAO config policy makeDefault predecessor
    dao.factoryInfo = ⟨predecessor, true⟩ ∧
    dao.stateVersion = .v2 ∧
    factoryInfoForAccount (.stored dao.factoryInfo) current =
      some ⟨predecessor, true⟩ := by
  simp [initializeDAO, factoryInfoForAccount, effectiveFactory]

theorem initialized_factory_bytes_end_enabled (predecessor : String) :
    (initializedFactoryBytes predecessor).getLast? = some 1 := by
  simp [initializedFactoryBytes, encodeFactoryInfo]

theorem initialized_version_is_v2_byte : initializedVersionBytes = [1] := by rfl

-- Exact arrays consumed by oracle/init_test.rs on the pinned source.
theorem initialized_raw_oracle_vectors :
    initializedFactoryBytes "factory.near" =
      [12, 0, 0, 0, 102, 97, 99, 116, 111, 114, 121, 46, 110, 101, 97, 114, 1] ∧
    initializedVersionBytes = [1] := by
  decide

end SputnikDAO2
