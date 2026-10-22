import Model.InitExport
import Proofs.WrapperInit

namespace SputnikDAO2

theorem named_new_uses_init_wrapper
    (raw : BountyRawTrie) (ctx : NewWrapperContext)
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) :
    runNamedNewExport raw ctx config policy predecessor =
      runNewWrapper raw ctx config policy predecessor := by
  have hi : findDAOExport "new" =
      some ⟨"new", .init, false, false⟩ := by decide
  simp [runNamedNewExport, hi]

theorem named_new_rejects_existing_state
    (raw : BountyRawTrie) (ctx : NewWrapperContext)
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String)
    (hroot : (raw daoRootKey).isSome = true) :
    runNamedNewExport raw ctx config policy predecessor = none := by
  rw [named_new_uses_init_wrapper]
  exact new_wrapper_rejects_existing_state raw ctx config policy
    predecessor hroot

theorem version_read_missing_is_v1_fallback (raw : BountyRawTrie)
    (h : raw daoVersionKey = none) :
    versionReadFromRaw raw = .missing := by
  simp [versionReadFromRaw, h]

theorem version_read_exact_v1 (raw : BountyRawTrie)
    (h : raw daoVersionKey = some [0]) :
    versionReadFromRaw raw = .v1 := by
  simp [versionReadFromRaw, h]

theorem version_read_exact_v2 (raw : BountyRawTrie)
    (h : raw daoVersionKey = some [1]) :
    versionReadFromRaw raw = .v2 := by
  simp [versionReadFromRaw, h]

theorem version_read_unknown_aborts (raw : BountyRawTrie)
    (h : raw daoVersionKey = some [2]) :
    versionReadFromRaw raw = .malformed := by
  simp [versionReadFromRaw, h]

theorem version_read_trailing_bytes_abort (raw : BountyRawTrie)
    (h : raw daoVersionKey = some [1, 0]) :
    versionReadFromRaw raw = .malformed := by
  simp [versionReadFromRaw, h]

theorem named_migrate_requires_root_bytes
    (raw : BountyRawTrie) (deposit : Nat) (current predecessor : String)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hroot : raw daoRootKey = none) :
    runNamedMigrateExport raw deposit current predecessor decodeV1
      decodeV2 encodeCurrent = none := by
  have hi : findDAOExport "migrate" =
      some ⟨"migrate", .init, false, true⟩ := by decide
  simp [runNamedMigrateExport, hi, hroot]

theorem named_migrate_rejects_malformed_version
    (raw : BountyRawTrie) (deposit : Nat) (current predecessor : String)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hversion : raw daoVersionKey = some [2]) :
    runNamedMigrateExport raw deposit current predecessor decodeV1
      decodeV2 encodeCurrent = none := by
  have hi : findDAOExport "migrate" =
      some ⟨"migrate", .init, false, true⟩ := by decide
  cases hroot : raw daoRootKey with
  | none => simp [runNamedMigrateExport, hi, hroot]
  | some bytes =>
      simp [runNamedMigrateExport, hi, hroot,
        versionReadFromRaw, hversion, runMigrateWrapper, runMigrate]

theorem named_migrate_rejects_trailing_version_bytes
    (raw : BountyRawTrie) (deposit : Nat) (current predecessor : String)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hversion : raw daoVersionKey = some [1, 0]) :
    runNamedMigrateExport raw deposit current predecessor decodeV1
      decodeV2 encodeCurrent = none := by
  have hi : findDAOExport "migrate" =
      some ⟨"migrate", .init, false, true⟩ := by decide
  cases hroot : raw daoRootKey with
  | none => simp [runNamedMigrateExport, hi, hroot]
  | some bytes =>
      simp [runNamedMigrateExport, hi, hroot,
        versionReadFromRaw, hversion, runMigrateWrapper, runMigrate]

theorem named_migrate_missing_version_writes_v2_and_root
    (raw : BountyRawTrie) (current : String) (bytes : BountyBytes)
    (old : StateCore)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hroot : raw daoRootKey = some bytes)
    (hversion : raw daoVersionKey = none)
    (hdecode : decodeV1 bytes = some old) :
    runNamedMigrateExport raw 0 current current decodeV1 decodeV2
      encodeCurrent =
      some (bountyRawWrite
        (bountyRawWrite raw daoVersionKey initializedVersionBytes)
        daoRootKey (encodeCurrent ⟨old, []⟩)) := by
  have hi : findDAOExport "migrate" =
      some ⟨"migrate", .init, false, true⟩ := by decide
  simp [runNamedMigrateExport, hi, hroot, versionReadFromRaw,
    hversion, runMigrateWrapper, runMigrate, hdecode]

theorem named_migrate_exact_v1_writes_v2_and_root
    (raw : BountyRawTrie) (current : String) (bytes : BountyBytes)
    (old : StateCore)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hroot : raw daoRootKey = some bytes)
    (hversion : raw daoVersionKey = some [0])
    (hdecode : decodeV1 bytes = some old) :
    runNamedMigrateExport raw 0 current current decodeV1 decodeV2
      encodeCurrent =
      some (bountyRawWrite
        (bountyRawWrite raw daoVersionKey initializedVersionBytes)
        daoRootKey (encodeCurrent ⟨old, []⟩)) := by
  have hi : findDAOExport "migrate" =
      some ⟨"migrate", .init, false, true⟩ := by decide
  simp [runNamedMigrateExport, hi, hroot, versionReadFromRaw,
    hversion, runMigrateWrapper, runMigrate, hdecode]

theorem named_migrate_v2_rewrites_only_root
    (raw : BountyRawTrie) (current : String) (bytes : BountyBytes)
    (state : CurrentState)
    (decodeV1 : BountyBytes → Option StateCore)
    (decodeV2 : BountyBytes → Option CurrentState)
    (encodeCurrent : CurrentState → BountyBytes)
    (hroot : raw daoRootKey = some bytes)
    (hversion : raw daoVersionKey = some [1])
    (hdecode : decodeV2 bytes = some state) :
    runNamedMigrateExport raw 0 current current decodeV1 decodeV2
      encodeCurrent =
      some (bountyRawWrite raw daoRootKey (encodeCurrent state)) := by
  have hi : findDAOExport "migrate" =
      some ⟨"migrate", .init, false, true⟩ := by decide
  simp [runNamedMigrateExport, hi, hroot, versionReadFromRaw,
    hversion, runMigrateWrapper, runMigrate, hdecode]

end SputnikDAO2
