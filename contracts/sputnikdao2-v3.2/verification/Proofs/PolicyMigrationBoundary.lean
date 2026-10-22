import Proofs.InitExport
import Proofs.PolicyGovernanceExport
import Proofs.UpdateExport

namespace SputnikDAO2

theorem raw_update_ignores_policy_key_replacement
    (raw : BountyRawTrie) (policyBytes : BountyBytes)
    (ctx : RawUpdateContext) (validAccount : String → Bool)
    (hashCode : CodeBytes → String) :
    runParsedUpdateExport
      (bountyRawWrite raw daoPolicyKey policyBytes) ctx validAccount
      hashCode =
      runParsedUpdateExport raw ctx validAccount hashCode := by
  have hkey :
      (bountyRawWrite raw daoPolicyKey policyBytes) daoFactoryKey =
        raw daoFactoryKey := by
    simp [bountyRawWrite, daoPolicyKey, daoFactoryKey]
  exact raw_update_depends_on_factory_key_only
    (bountyRawWrite raw daoPolicyKey policyBytes) raw ctx
    (parseFactoryInfoExact validAccount) validAccount hashCode hkey

theorem migrate_wrapper_preserves_policy_key
    (raw final : BountyRawTrie) (deposit : Nat)
    (ctx : MigrationContext)
    (encodeCurrent : CurrentState → BountyBytes)
    (hrun : runMigrateWrapper raw deposit ctx encodeCurrent = some final) :
    final daoPolicyKey = raw daoPolicyKey := by
  unfold runMigrateWrapper at hrun
  split at hrun
  · simp at hrun
  · split at hrun
    · simp at hrun
    · cases hresult : runMigrate ctx with
      | none => simp [hresult] at hrun
      | some result =>
          simp [hresult] at hrun
          cases hrun
          by_cases hw : result.wroteV2Version = true
          · simp [hw, bountyRawWrite, daoPolicyKey,
              daoVersionKey, daoRootKey]
          · simp [hw, bountyRawWrite, daoPolicyKey,
              daoRootKey]

theorem named_migrate_preserves_policy_key
    (raw final : BountyRawTrie) (deposit : Nat)
    (current predecessor : String)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hrun : runNamedMigrateExport raw deposit current predecessor
      decodeV1 decodeV2 encodeCurrent = some final) :
    final daoPolicyKey = raw daoPolicyKey := by
  have hi : findDAOExport "migrate" =
      some ⟨"migrate", .init, false, true⟩ := by decide
  cases hroot : raw daoRootKey with
  | none => simp [runNamedMigrateExport, hi, hroot] at hrun
  | some bytes =>
      have hbody : runMigrateWrapper raw deposit
          ⟨current, predecessor, versionReadFromRaw raw,
            decodeV1 bytes, decodeV2 bytes⟩ encodeCurrent =
          some final := by
        simpa [runNamedMigrateExport, hi, hroot] using hrun
      exact migrate_wrapper_preserves_policy_key raw final deposit _
        encodeCurrent hbody

theorem named_migrate_preserves_policy_readability
    (raw final : BountyRawTrie) (deposit : Nat)
    (current predecessor : String)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hrun : runNamedMigrateExport raw deposit current predecessor
      decodeV1 decodeV2 encodeCurrent = some final) :
    policyReadableFromRaw final = policyReadableFromRaw raw := by
  have hkey := named_migrate_preserves_policy_key raw final deposit
    current predecessor decodeV1 decodeV2 encodeCurrent hrun
  simp [policyReadableFromRaw, hkey]

end SputnikDAO2
