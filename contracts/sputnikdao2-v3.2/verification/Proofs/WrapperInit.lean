import Model.WrapperInit
import Proofs.ConstructorTrie

namespace SputnikDAO2

theorem constructor_on_empty_eq_fresh
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) :
    constructorOnExistingTrie bountyEmptyRaw config policy predecessor =
      constructorTrie config policy predecessor := by
  rfl

theorem new_wrapper_rejects_deposit
    (raw : BountyRawTrie) (ctx : NewWrapperContext)
    (config : WireConfig) (policy : WirePolicy) (predecessor : String)
    (h : ctx.attachedDeposit ≠ 0) :
    runNewWrapper raw ctx config policy predecessor = none := by
  simp [runNewWrapper, h]

theorem new_wrapper_rejects_bad_arguments
    (raw : BountyRawTrie) (config : WireConfig)
    (policy : WirePolicy) (predecessor : String) :
    runNewWrapper raw ⟨0, false⟩ config policy predecessor = none := by
  rfl

theorem new_wrapper_rejects_existing_state
    (raw : BountyRawTrie) (ctx : NewWrapperContext)
    (config : WireConfig) (policy : WirePolicy) (predecessor : String)
    (hpresent : (raw daoRootKey).isSome = true) :
    runNewWrapper raw ctx config policy predecessor = none := by
  simp [runNewWrapper, hpresent]

theorem new_wrapper_accepts_absent_root
    (raw : BountyRawTrie) (config : WireConfig)
    (policy : WirePolicy) (predecessor : String)
    (habsent : raw daoRootKey = none) :
    runNewWrapper raw ⟨0, true⟩ config policy predecessor =
      some (constructorOnExistingTrie raw config policy predecessor) := by
  simp [runNewWrapper, habsent]

theorem new_wrapper_fresh_image
    (config : WireConfig) (policy : WirePolicy)
    (predecessor : String) :
    runNewWrapper bountyEmptyRaw ⟨0, true⟩ config policy predecessor =
      some (constructorTrie config policy predecessor) := by
  rw [new_wrapper_accepts_absent_root]
  · rw [constructor_on_empty_eq_fresh]
  · rfl

theorem constructor_on_existing_root_value
    (raw : BountyRawTrie) (config : WireConfig)
    (policy : WirePolicy) (predecessor : String) :
    constructorOnExistingTrie raw config policy predecessor daoRootKey =
      some initializedRootBytes := by
  simp [constructorOnExistingTrie, bountyRawWrite]

theorem new_wrapper_cannot_repeat
    (raw next : BountyRawTrie) (ctx : NewWrapperContext)
    (config : WireConfig) (policy : WirePolicy) (predecessor : String)
    (h : runNewWrapper raw ctx config policy predecessor = some next) :
    runNewWrapper next ctx config policy predecessor = none := by
  unfold runNewWrapper at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  apply new_wrapper_rejects_existing_state
  simp [constructor_on_existing_root_value]

theorem constructor_on_existing_preserves_unrelated_key
    (raw : BountyRawTrie) (config : WireConfig)
    (policy : WirePolicy) (predecessor : String)
    (key : BountyBytes) (hother : ¬ constructorKey key) :
    constructorOnExistingTrie raw config policy predecessor key = raw key := by
  simp only [constructorKey, not_or] at hother
  rcases hother with ⟨hc, hp, hf, hv, hr⟩
  simp [constructorOnExistingTrie, bountyRawWrite,
    hc, hp, hf, hv, hr]

theorem nonfresh_wrapper_preserves_unrelated_key
    (raw next : BountyRawTrie) (ctx : NewWrapperContext)
    (config : WireConfig) (policy : WirePolicy) (predecessor : String)
    (key : BountyBytes) (hother : ¬ constructorKey key)
    (h : runNewWrapper raw ctx config policy predecessor = some next) :
    next key = raw key := by
  unfold runNewWrapper at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h <;> try contradiction
  cases h
  exact constructor_on_existing_preserves_unrelated_key
    raw config policy predecessor key hother

theorem migrate_wrapper_rejects_external_caller
    (raw : BountyRawTrie) (attachedDeposit : Nat)
    (ctx : MigrationContext)
    (encodeCurrent : CurrentState → BountyBytes)
    (hcaller : ctx.predecessor ≠ ctx.current) :
    runMigrateWrapper raw attachedDeposit ctx encodeCurrent = none := by
  simp [runMigrateWrapper, hcaller]

theorem migrate_wrapper_rejects_deposit
    (raw : BountyRawTrie) (attachedDeposit : Nat)
    (ctx : MigrationContext)
    (encodeCurrent : CurrentState → BountyBytes)
    (hdeposit : attachedDeposit ≠ 0) :
    runMigrateWrapper raw attachedDeposit ctx encodeCurrent = none := by
  by_cases hcaller : ctx.predecessor = ctx.current
  · simp [runMigrateWrapper, hcaller, hdeposit]
  · simp [runMigrateWrapper, hcaller]

theorem migrate_wrapper_v1_writes_version_then_root
    (raw : BountyRawTrie) (ctx : MigrationContext)
    (old : StateCore) (encodeCurrent : CurrentState → BountyBytes)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v1)
    (hstate : ctx.oldState = some old) :
    runMigrateWrapper raw 0 ctx encodeCurrent =
      some (bountyRawWrite
        (bountyRawWrite raw daoVersionKey initializedVersionBytes)
        daoRootKey (encodeCurrent ⟨old, []⟩)) := by
  simp [runMigrateWrapper, runMigrate, hcaller, hversion, hstate]

theorem migrate_wrapper_missing_version_uses_v1
    (raw : BountyRawTrie) (ctx : MigrationContext)
    (old : StateCore) (encodeCurrent : CurrentState → BountyBytes)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .missing)
    (hstate : ctx.oldState = some old) :
    runMigrateWrapper raw 0 ctx encodeCurrent =
      some (bountyRawWrite
        (bountyRawWrite raw daoVersionKey initializedVersionBytes)
        daoRootKey (encodeCurrent ⟨old, []⟩)) := by
  simp [runMigrateWrapper, runMigrate, hcaller, hversion, hstate]

theorem migrate_wrapper_v2_writes_only_root
    (raw : BountyRawTrie) (ctx : MigrationContext)
    (current : CurrentState) (encodeCurrent : CurrentState → BountyBytes)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v2)
    (hstate : ctx.currentState = some current) :
    runMigrateWrapper raw 0 ctx encodeCurrent =
      some (bountyRawWrite raw daoRootKey (encodeCurrent current)) := by
  simp [runMigrateWrapper, runMigrate, hcaller, hversion, hstate]

theorem migrate_wrapper_v2_preserves_version_bytes
    (raw next : BountyRawTrie) (ctx : MigrationContext)
    (current : CurrentState) (encodeCurrent : CurrentState → BountyBytes)
    (hcaller : ctx.predecessor = ctx.current)
    (hversion : ctx.versionRead = .v2)
    (hstate : ctx.currentState = some current)
    (hrun : runMigrateWrapper raw 0 ctx encodeCurrent = some next) :
    next daoVersionKey = raw daoVersionKey := by
  rw [migrate_wrapper_v2_writes_only_root raw ctx current encodeCurrent
    hcaller hversion hstate] at hrun
  cases hrun
  simp [bountyRawWrite, daoVersionKey, daoRootKey]

theorem view_wrapper_never_writes_storage {α β : Type}
    (raw next : BountyRawTrie) (decoded : Option α)
    (attachedDeposit : Nat) (view : α → BountyRawTrie → β)
    (result : β)
    (h : runViewWrapper raw decoded attachedDeposit view =
      some (result, next)) :
    next = raw := by
  cases decoded with
  | none => simp [runViewWrapper] at h
  | some state =>
      simp [runViewWrapper] at h
      exact h.2.symm

theorem owned_staking_view_accepts_any_deposit
    (raw : BountyRawTrie) (state : CurrentState)
    (attachedDeposit : Nat) :
    runStakingViewWrapper raw (some state) attachedDeposit =
      some (viewStakingContract state.core.stakingId, raw) := by
  rfl

theorem owned_staking_view_missing_state_aborts
    (raw : BountyRawTrie) (attachedDeposit : Nat) :
    runStakingViewWrapper raw none attachedDeposit = none := by
  rfl

end SputnikDAO2
