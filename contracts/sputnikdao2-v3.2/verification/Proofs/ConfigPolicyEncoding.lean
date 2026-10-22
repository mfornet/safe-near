import Model.ConfigPolicyEncoding

namespace SputnikDAO2

set_option maxRecDepth 2048

theorem wire_config_oracle_vector :
    encodeWireConfig wireTestConfig =
      ([4, 0, 0, 0, 84, 101, 115, 116,
        7, 0, 0, 0, 116, 111, 32, 116, 101, 115, 116,
        3, 0, 0, 0, 0, 255, 1] : BountyBytes) := by decide

theorem wire_small_policy_oracle_vector :
    encodeWireVersionedPolicy (.current wireSmallPolicy) =
      ([1, 0, 0, 0, 0, 1] : BountyBytes) ++
      List.replicate 16 0 ++
      [1, 1, 0, 0, 0, 0, 0, 0, 0,
       2, 0, 0, 0, 0, 0, 0, 0] ++
      [17] ++ List.replicate 15 0 ++
      [123] ++ List.replicate 7 0 ++
      [19] ++ List.replicate 15 0 ++
      [200, 1] ++ List.replicate 6 0 := by decide

theorem wire_small_policy_length :
    (encodeWireVersionedPolicy (.current wireSmallPolicy)).length = 87 := by
  decide

theorem wire_test_config_fits : wireConfigFits wireTestConfig := by
  simp [wireConfigFits, wireStringFits, wireTestConfig]
  decide

theorem wire_small_policy_fits : wirePolicyFits wireSmallPolicy := by
  simp [wirePolicyFits, wireSmallPolicy, wireVotePolicyFits,
    wireThresholdFits, wireDefaultVote]

theorem wire_role_fixture_ordered : wireRoleOrdered wireRoleFixture := by
  simp [wireRoleOrdered, wireStringsOrdered, wireRoleFixture]

theorem wire_role_fixture_prefix :
    (encodeWireRolePermission wireRoleFixture).take 12 =
      ([7, 0, 0, 0, 99, 111, 117, 110, 99, 105, 108, 2] :
        BountyBytes) := by decide

theorem wire_role_fixture_oracle_vector :
    encodeWireRolePermission wireRoleFixture =
      bountyBorshString "council" ++
      [2, 2, 0, 0, 0] ++
      bountyBorshString "a.near" ++
      bountyBorshString "z.near" ++
      [2, 0, 0, 0] ++
      bountyBorshString "X:VoteApprove" ++
      bountyBorshString "X:VoteReject" ++
      [2, 0, 0, 0] ++
      bountyBorshString "A" ++ encodeWireVotePolicy wireDefaultVote ++
      bountyBorshString "Z" ++ encodeWireVotePolicy wireDefaultVote := by
  decide

theorem wire_role_fixture_length :
    (encodeWireRolePermission wireRoleFixture).length = 155 := by decide

theorem wire_role_fixture_fits : wireRoleFits wireRoleFixture := by
  simp [wireRoleFits, wireRoleKindFits, wireVotePolicyFits,
    wireThresholdFits, wireRoleOrdered, wireStringsOrdered,
    wireStringFits, wireRoleFixture, wireDefaultVote]
  decide

theorem wire_version_tags :
    (encodeWireVersionedPolicy (.default [])).head? = some 0 ∧
    (encodeWireVersionedPolicy (.current wireSmallPolicy)).head? = some 1 := by
  decide

theorem constructor_policy_bytes_always_current
    (makeDefault : List String → WirePolicy)
    (input : WireVersionedPolicy) :
    ∃ policy,
      encodeWireVersionedPolicy
        (upgradeWireVersionedPolicy makeDefault input) =
          1 :: encodeWirePolicy policy := by
  cases input with
  | default council => exact ⟨makeDefault council, rfl⟩
  | current policy => exact ⟨policy, rfl⟩

theorem constructor_default_policy_bytes
    (makeDefault : List String → WirePolicy) (council : List String) :
    encodeWireVersionedPolicy
      (upgradeWireVersionedPolicy makeDefault (.default council)) =
        encodeWireVersionedPolicy (.current (makeDefault council)) := by
  rfl

end SputnikDAO2
