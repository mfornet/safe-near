import Model.SyncSettings
import Proofs.Upgrade

namespace SputnikDAO2

theorem change_config_preserves_factory (state : SyncSettingsState)
    (config : ConfigImage) (bond : Nat) (proposer : String) :
    (executeSyncSettings state (.changeConfig config) bond proposer).state.factoryRead =
      state.factoryRead := by rfl

theorem factory_update_overwrites_even_malformed (config : ConfigImage)
    (locked bond : Nat) (proposer : String) (info : FactoryInfo) :
    (executeSyncSettings ⟨config, .malformed, locked⟩
      (.factoryInfoUpdate info) bond proposer).state.factoryRead =
      .stored info := by rfl

theorem settings_refund_old_bond_without_callback
    (state : SyncSettingsState) (action : SyncSettingsAction)
    (bond : Nat) (proposer : String) :
    (executeSyncSettings state action bond proposer).refund =
      ⟨proposer, bond⟩ ∧
    (executeSyncSettings state action bond proposer).state.locked =
      state.locked - bond ∧
    (executeSyncSettings state action bond proposer).callbackScheduled = false := by
  cases action <;> simp [executeSyncSettings]

theorem disabled_factory_governance_update_blocks_external_raw_update
    (hashCode : CodeBytes → String) (state : SyncSettingsState)
    (ctx : UpdateContext) (factory proposer : String) (bond : Nat)
    (hfactory : ctx.predecessor = factory)
    (hnotself : ctx.predecessor ≠ ctx.current) :
    runUpdate hashCode
      (updateContextAfterSettings ctx
        (executeSyncSettings state
          (.factoryInfoUpdate ⟨factory, false⟩) bond proposer)) = none := by
  apply disabled_factory_cannot_update
  · rfl
  · exact hfactory
  · exact hnotself

theorem enabled_factory_governance_update_allows_raw_input
    (hashCode : CodeBytes → String) (state : SyncSettingsState)
    (ctx : UpdateContext) (factory proposer : String) (bond : Nat)
    (code : CodeBytes) (hfactory : ctx.predecessor = factory)
    (hnotself : ctx.predecessor ≠ ctx.current)
    (hinput : ctx.rawInput = some code) :
    runUpdate hashCode
      (updateContextAfterSettings ctx
        (executeSyncSettings state
          (.factoryInfoUpdate ⟨factory, true⟩) bond proposer)) =
      some (upgradeReceipt ctx.current (hashCode code)) := by
  apply factory_update_receipt
  · rfl
  · exact hfactory
  · rfl
  · exact hnotself
  · exact hinput

end SputnikDAO2
