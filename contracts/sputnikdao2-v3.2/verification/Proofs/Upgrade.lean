import Model.Upgrade

namespace SputnikDAO2

theorem missing_factory_defaults_to_enabled (fallback : String) :
    effectiveFactory .missing (some fallback) =
      some ⟨fallback, true⟩ := by
  rfl

theorem missing_factory_uses_parent_suffix (current parent : String)
    (h : factoryParentSuffix current = some parent) :
    factoryInfoForAccount .missing current = some ⟨parent, true⟩ := by
  simp [factoryInfoForAccount, effectiveFactory, h]

theorem missing_factory_without_parent_aborts (current : String)
    (h : factoryParentSuffix current = none) :
    factoryInfoForAccount .missing current = none := by
  simp [factoryInfoForAccount, effectiveFactory, h]

theorem stored_factory_ignores_account_parent (current : String)
    (info : FactoryInfo) :
    factoryInfoForAccount (.stored info) current = some info := by
  rfl

theorem malformed_factory_info_view_aborts (current : String) :
    factoryInfoForAccount .malformed current = none := by rfl

theorem malformed_factory_aborts (hashCode : CodeBytes → String)
    (ctx : UpdateContext) (h : ctx.factoryRead = .malformed) :
    runUpdate hashCode ctx = none := by
  simp [runUpdate, effectiveFactory, h]

theorem missing_factory_without_valid_parent_aborts
    (hashCode : CodeBytes → String) (ctx : UpdateContext)
    (hread : ctx.factoryRead = .missing)
    (hparent : ctx.fallbackFactory = none) :
    runUpdate hashCode ctx = none := by
  simp [runUpdate, effectiveFactory, hread, hparent]

theorem unauthorized_update_aborts (hashCode : CodeBytes → String)
    (ctx : UpdateContext) (info : FactoryInfo)
    (hfactory : effectiveFactory ctx.factoryRead ctx.fallbackFactory = some info)
    (hdeny : updateAuthorized ctx info = false) :
    runUpdate hashCode ctx = none := by
  simp [runUpdate, hfactory, hdeny]

theorem disabled_factory_cannot_update (hashCode : CodeBytes → String)
    (ctx : UpdateContext) (factory : String)
    (hread : ctx.factoryRead = .stored ⟨factory, false⟩)
    (hpre : ctx.predecessor = factory)
    (hnotself : ctx.predecessor ≠ ctx.current) :
    runUpdate hashCode ctx = none := by
  have hf : factory ≠ ctx.current := by simpa [hpre] using hnotself
  simp [runUpdate, effectiveFactory, hread, updateAuthorized, hpre, hf]

theorem self_update_requires_successful_result (hashCode : CodeBytes → String)
    (ctx : UpdateContext) (hself : ctx.predecessor = ctx.current)
    (hresult : ctx.successfulPromiseResult = none) :
    runUpdate hashCode ctx = none := by
  cases heff : effectiveFactory ctx.factoryRead ctx.fallbackFactory with
  | none => simp [runUpdate, heff]
  | some info => simp [runUpdate, heff, updateAuthorized, hself, hresult]

theorem self_update_receipt (hashCode : CodeBytes → String)
    (ctx : UpdateContext) (info : FactoryInfo) (code : CodeBytes)
    (hfactory : effectiveFactory ctx.factoryRead ctx.fallbackFactory = some info)
    (hself : ctx.predecessor = ctx.current)
    (hresult : ctx.successfulPromiseResult = some code) :
    runUpdate hashCode ctx = some (upgradeReceipt ctx.current (hashCode code)) := by
  simp [runUpdate, hfactory, updateAuthorized, hself, hresult]

theorem factory_update_receipt (hashCode : CodeBytes → String)
    (ctx : UpdateContext) (info : FactoryInfo) (code : CodeBytes)
    (hfactory : effectiveFactory ctx.factoryRead ctx.fallbackFactory = some info)
    (hcaller : ctx.predecessor = info.factoryId)
    (henabled : info.autoUpdate = true)
    (hnotself : ctx.predecessor ≠ ctx.current)
    (hinput : ctx.rawInput = some code) :
    runUpdate hashCode ctx = some (upgradeReceipt ctx.current (hashCode code)) := by
  have hf : info.factoryId ≠ ctx.current := by simpa [hcaller] using hnotself
  simp [runUpdate, hfactory, updateAuthorized, hcaller, henabled,
    hf, hinput]

theorem factory_update_requires_raw_input (hashCode : CodeBytes → String)
    (ctx : UpdateContext) (info : FactoryInfo)
    (hfactory : effectiveFactory ctx.factoryRead ctx.fallbackFactory = some info)
    (hcaller : ctx.predecessor = info.factoryId)
    (henabled : info.autoUpdate = true)
    (hnotself : ctx.predecessor ≠ ctx.current)
    (hinput : ctx.rawInput = none) :
    runUpdate hashCode ctx = none := by
  have hf : info.factoryId ≠ ctx.current := by simpa [hcaller] using hnotself
  simp [runUpdate, hfactory, updateAuthorized, hcaller, henabled,
    hf, hinput]

theorem receipt_has_zero_deposit_and_static_gas (current hash : String) :
    (upgradeReceipt current hash).attachedDeposit = 0 ∧
    (upgradeReceipt current hash).staticGas = 0 ∧
    (upgradeReceipt current hash).returned = true := by
  simp [upgradeReceipt]

end SputnikDAO2
