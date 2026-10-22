import Model.RootStateEncoding

namespace SputnikDAO2

set_option maxRecDepth 2048

theorem root_locked_offset (state : RootStateScalars) :
    ((rootStateScalarBytes state).drop 10).take 16 =
      bountyLE 16 state.lockedAmount := by
  simp [rootStateScalarBytes, rootBeforeBounty, rootBeforeProposal,
    rootHandle, bountyLE]

theorem root_staking_offset (state : RootStateScalars) :
    ((rootStateScalarBytes state).drop 26).take
      (rootStakingBytes state.stakingId).length =
      rootStakingBytes state.stakingId := by
  simp [rootStateScalarBytes, rootBeforeBounty, rootBeforeProposal,
    rootHandle, bountyLE]

theorem root_proposal_counter_offset (state : RootStateScalars) :
    ((rootStateScalarBytes state).drop
      (47 + (rootStakingBytes state.stakingId).length)).take 8 =
      bountyLE 8 state.lastProposalId := by
  have hlen : (rootBeforeProposal state).length =
      47 + (rootStakingBytes state.stakingId).length := by
    simp [rootBeforeProposal, rootHandle, bountyLE]
    omega
  rw [← hlen]
  simp [rootStateScalarBytes, rootBeforeBounty, bountyLE]

theorem root_bounty_counter_offset (state : RootStateScalars) :
    ((rootStateScalarBytes state).drop
      (60 + (rootStakingBytes state.stakingId).length)).take 8 =
      bountyLE 8 state.lastBountyId := by
  have hlen : (rootBeforeBounty state).length =
      60 + (rootStakingBytes state.stakingId).length := by
    simp [rootBeforeBounty, rootBeforeProposal, rootHandle, bountyLE]
    omega
  rw [← hlen]
  simp [rootStateScalarBytes, bountyLE]

theorem root_counter_offsets (proposalId bountyId : Nat) :
    rootProposalIdBytes (rootStateBytes proposalId bountyId) =
      bountyLE 8 proposalId ∧
    rootBountyIdBytes (rootStateBytes proposalId bountyId) =
      bountyLE 8 bountyId := by
  simp [rootProposalIdBytes, rootBountyIdBytes, rootStateBytes,
    rootStateScalarBytes, rootBeforeBounty, rootBeforeProposal, rootAfterBounty,
    rootStakingBytes, rootHandle, bountyLE]

theorem initialized_root_length : initializedRootBytes.length = 93 := by decide

theorem v1_root_is_v2_without_empty_log (state : RootStateScalars) :
    rootStateScalarBytes { state with actionsLog := [] } =
      rootStateV1Bytes state ++ bountyLE 4 0 := by
  simp [rootStateScalarBytes, rootStateV1Bytes, rootAfterBounty,
    rootBeforeBounty, rootBeforeProposal, List.append_assoc]

theorem v1_migration_root_extension (ctx : MigrationContext)
    (old : StateCore)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v1)
    (hstate : ctx.oldState = some old) :
    (runMigrate ctx).map (fun result =>
      rootStateScalarBytes (rootScalarsOfStateCore result.state.core)) =
      some (rootStateV1Bytes (rootScalarsOfStateCore old) ++
        bountyLE 4 0) := by
  simpa [runMigrate, hcaller, hversion, hstate,
    rootScalarsOfStateCore] using
    (v1_root_is_v2_without_empty_log (rootScalarsOfStateCore old))

theorem initialized_v1_root_length :
    (rootStateV1Bytes ⟨0, none, 0, 0, 0, []⟩).length = 89 := by decide

theorem initialized_root_widths :
    validRootScalarWidths ⟨0, none, 0, 0, 0, []⟩ := by
  simp [validRootScalarWidths]

theorem populated_root_fixture_length :
    (rootStateScalarBytes populatedRootFixture).length = 140 := by decide

theorem populated_root_fixture_widths :
    validRootScalarWidths populatedRootFixture := by
  simp [validRootScalarWidths, validRootLogWidths, populatedRootFixture]
  decide

theorem populated_root_fixture_fields :
    ((rootStateScalarBytes populatedRootFixture).drop 10).take 16 =
      bountyLE 16 17 ∧
    ((rootStateScalarBytes populatedRootFixture).drop 26).take 17 =
      rootStakingBytes (some "staking.near") ∧
    ((rootStateScalarBytes populatedRootFixture).drop 64).take 8 =
      bountyLE 8 7 ∧
    ((rootStateScalarBytes populatedRootFixture).drop 77).take 8 =
      bountyLE 8 9 ∧
    (rootStateScalarBytes populatedRootFixture).drop 105 =
      bountyLE 4 1 ++
        rootActionLogBytes ⟨"alice.near", 7, .voteApprove, 123⟩ := by
  decide

theorem initialized_root_counter_offsets :
    rootProposalIdBytes initializedRootBytes = bountyLE 8 0 ∧
    rootBountyIdBytes initializedRootBytes = bountyLE 8 0 := by decide

theorem initialized_root_handle_prefixes :
    initializedRootBytes.take 10 = rootHandle 0 ++ rootHandle 1 ∧
    (initializedRootBytes.drop 43).take 5 = rootHandle 2 ∧
    (initializedRootBytes.drop 56).take 5 = rootHandle 3 ∧
    (initializedRootBytes.drop 69).take 20 =
      rootHandle 4 ++ rootHandle 5 ++ rootHandle 6 ++ rootHandle 7 := by decide

theorem initialized_root_exact_oracle_vector :
    initializedRootBytes =
      ([1, 0, 0, 0, 0, 1, 0, 0, 0, 1] : BountyBytes) ++
      List.replicate 33 0 ++
      [1, 0, 0, 0, 2] ++
      List.replicate 8 0 ++
      [1, 0, 0, 0, 3] ++
      List.replicate 8 0 ++
      [1, 0, 0, 0, 4, 1, 0, 0, 0, 5,
       1, 0, 0, 0, 6, 1, 0, 0, 0, 7] ++
      List.replicate 4 0 := by decide

end SputnikDAO2
