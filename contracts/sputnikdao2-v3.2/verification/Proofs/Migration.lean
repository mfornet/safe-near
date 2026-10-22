import Model.Migration

namespace SputnikDAO2

theorem external_caller_cannot_migrate (ctx : MigrationContext)
    (h : ctx.predecessor ≠ ctx.current) :
    runMigrate ctx = none := by
  simp [runMigrate, h]

theorem malformed_version_cannot_migrate (ctx : MigrationContext)
    (h : ctx.versionRead = .malformed) :
    runMigrate ctx = none := by
  by_cases hc : ctx.predecessor = ctx.current
  · simp [runMigrate, hc, h]
  · simp [runMigrate, hc]

theorem v1_migration_preserves_all_old_fields (ctx : MigrationContext)
    (old : StateCore)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v1)
    (hstate : ctx.oldState = some old) :
    runMigrate ctx = some ⟨⟨old, []⟩, true⟩ := by
  simp [runMigrate, hcaller, hversion, hstate]

theorem missing_version_uses_v1_migration (ctx : MigrationContext)
    (old : StateCore)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .missing)
    (hstate : ctx.oldState = some old) :
    runMigrate ctx = some ⟨⟨old, []⟩, true⟩ := by
  simp [runMigrate, hcaller, hversion, hstate]

theorem v2_migration_preserves_current_state (ctx : MigrationContext)
    (current : CurrentState)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v2)
    (hstate : ctx.currentState = some current) :
    runMigrate ctx = some ⟨current, false⟩ := by
  simp [runMigrate, hcaller, hversion, hstate]

theorem v1_missing_state_aborts (ctx : MigrationContext)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v1)
    (hstate : ctx.oldState = none) :
    runMigrate ctx = none := by
  simp [runMigrate, hcaller, hversion, hstate]

theorem v2_missing_state_aborts (ctx : MigrationContext)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v2)
    (hstate : ctx.currentState = none) :
    runMigrate ctx = none := by
  simp [runMigrate, hcaller, hversion, hstate]

theorem v1_migration_keeps_legacy_policy_unreadable
    (ctx : MigrationContext) (old : StateCore) (council : List String)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v1)
    (hstate : ctx.oldState = some old) :
    (runMigrateWithPolicy ctx (some (.default council))).map
      (fun result => readPolicy result.2) =
        some (.error .legacy) := by
  simp [runMigrateWithPolicy, runMigrate, hcaller, hversion,
    hstate, readPolicy]

theorem v1_migration_keeps_current_policy_readable
    (ctx : MigrationContext) (old : StateCore) (policy : String)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v1)
    (hstate : ctx.oldState = some old) :
    (runMigrateWithPolicy ctx (some (.current policy))).map
      (fun result => readPolicy result.2) = some (.ok policy) := by
  simp [runMigrateWithPolicy, runMigrate, hcaller, hversion,
    hstate, readPolicy]

end SputnikDAO2
