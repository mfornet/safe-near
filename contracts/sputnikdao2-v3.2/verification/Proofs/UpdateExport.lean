import Model.UpdateExport
import Proofs.Upgrade
import Proofs.FactoryEncoding

namespace SputnikDAO2

theorem raw_update_uses_source_projection
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String) :
    runRawUpdateExport raw ctx decodeFactory validAccount hashCode =
      runUpdate hashCode
        { current := ctx.current
          predecessor := ctx.predecessor
          factoryRead := factoryReadFromRaw raw decodeFactory
          fallbackFactory := validatedFactoryParent ctx.current validAccount
          successfulPromiseResult := ctx.successfulPromiseResult
          rawInput := ctx.rawInput } := by
  have hi : findDAOExport "update" =
      some ⟨"update", .raw, false, false⟩ := by decide
  simp [runRawUpdateExport, hi]

theorem raw_update_depends_on_factory_key_only
    (raw₁ raw₂ : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (hfactory : raw₁ daoFactoryKey = raw₂ daoFactoryKey) :
    runRawUpdateExport raw₁ ctx decodeFactory validAccount hashCode =
      runRawUpdateExport raw₂ ctx decodeFactory validAccount hashCode := by
  simp [raw_update_uses_source_projection, factoryReadFromRaw, hfactory]

theorem raw_update_ignores_attached_deposit
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (deposit : Nat)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String) :
    runRawUpdateExport raw { ctx with attachedDeposit := deposit }
      decodeFactory validAccount hashCode =
    runRawUpdateExport raw ctx decodeFactory validAccount hashCode := by
  simp [raw_update_uses_source_projection]

theorem raw_update_malformed_factory_aborts
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (bytes : BountyBytes)
    (hraw : raw daoFactoryKey = some bytes)
    (hdecode : decodeFactory bytes = none) :
    runRawUpdateExport raw ctx decodeFactory validAccount hashCode = none := by
  rw [raw_update_uses_source_projection]
  simp [factoryReadFromRaw, hraw, hdecode, runUpdate, effectiveFactory]

theorem raw_update_missing_factory_invalid_parent_aborts
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (hraw : raw daoFactoryKey = none)
    (hparent : validatedFactoryParent ctx.current validAccount = none) :
    runRawUpdateExport raw ctx decodeFactory validAccount hashCode = none := by
  rw [raw_update_uses_source_projection]
  simp [factoryReadFromRaw, hraw, hparent, runUpdate, effectiveFactory]

theorem raw_update_self_receipt_without_root_guard
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (bytes code : BountyBytes) (info : FactoryInfo)
    (hraw : raw daoFactoryKey = some bytes)
    (hdecode : decodeFactory bytes = some info)
    (hself : ctx.predecessor = ctx.current)
    (hresult : ctx.successfulPromiseResult = some code) :
    runRawUpdateExport raw ctx decodeFactory validAccount hashCode =
      some (upgradeReceipt ctx.current (hashCode code)) := by
  rw [raw_update_uses_source_projection]
  simp [factoryReadFromRaw, hraw, hdecode, runUpdate,
    effectiveFactory, updateAuthorized, hself, hresult]

theorem raw_update_factory_receipt_without_root_guard
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (bytes code : BountyBytes) (info : FactoryInfo)
    (hraw : raw daoFactoryKey = some bytes)
    (hdecode : decodeFactory bytes = some info)
    (hcaller : ctx.predecessor = info.factoryId)
    (henabled : info.autoUpdate = true)
    (hnotself : ctx.predecessor ≠ ctx.current)
    (hinput : ctx.rawInput = some code) :
    runRawUpdateExport raw ctx decodeFactory validAccount hashCode =
      some (upgradeReceipt ctx.current (hashCode code)) := by
  rw [raw_update_uses_source_projection]
  have hf : info.factoryId ≠ ctx.current := by simpa [hcaller] using hnotself
  simp [factoryReadFromRaw, hraw, hdecode, runUpdate,
    effectiveFactory, updateAuthorized, hcaller, henabled, hf, hinput]

theorem raw_update_disabled_factory_denies_external_caller
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (decodeFactory : BountyBytes → Option FactoryInfo)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (bytes : BountyBytes) (factory : String)
    (hraw : raw daoFactoryKey = some bytes)
    (hdecode : decodeFactory bytes = some ⟨factory, false⟩)
    (hcaller : ctx.predecessor = factory)
    (hnotself : ctx.predecessor ≠ ctx.current) :
    runRawUpdateExport raw ctx decodeFactory validAccount hashCode = none := by
  rw [raw_update_uses_source_projection]
  have hf : factory ≠ ctx.current := by simpa [hcaller] using hnotself
  simp [factoryReadFromRaw, hraw, hdecode, runUpdate,
    effectiveFactory, updateAuthorized, hcaller, hf]

theorem parsed_update_self_from_stored_bytes
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (info : FactoryInfo) (code : BountyBytes)
    (hraw : raw daoFactoryKey = some (encodeFactoryInfo info))
    (hfits : wireStringFits info.factoryId)
    (hvalid : validAccount info.factoryId = true)
    (hself : ctx.predecessor = ctx.current)
    (hresult : ctx.successfulPromiseResult = some code) :
    runParsedUpdateExport raw ctx validAccount hashCode =
      some (upgradeReceipt ctx.current (hashCode code)) := by
  exact raw_update_self_receipt_without_root_guard raw ctx
    (parseFactoryInfoExact validAccount) validAccount hashCode
    (encodeFactoryInfo info) code info hraw
    (parse_factory_info_exact_encoded validAccount info hfits hvalid)
    hself hresult

theorem parsed_update_disabled_factory_denies_external_caller
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (factory : String)
    (hraw : raw daoFactoryKey =
      some (encodeFactoryInfo ⟨factory, false⟩))
    (hfits : wireStringFits factory)
    (hvalid : validAccount factory = true)
    (hcaller : ctx.predecessor = factory)
    (hnotself : ctx.predecessor ≠ ctx.current) :
    runParsedUpdateExport raw ctx validAccount hashCode = none := by
  exact raw_update_disabled_factory_denies_external_caller raw ctx
    (parseFactoryInfoExact validAccount) validAccount hashCode
    (encodeFactoryInfo ⟨factory, false⟩) factory hraw
    (parse_factory_info_exact_encoded validAccount
      ⟨factory, false⟩ hfits hvalid) hcaller hnotself

theorem parsed_update_invalid_factory_bool_aborts
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (factoryId : String)
    (hraw : raw daoFactoryKey =
      some (bountyBorshString factoryId ++ [2]))
    (hfits : wireStringFits factoryId)
    (hvalid : validAccount factoryId = true) :
    runParsedUpdateExport raw ctx validAccount hashCode = none := by
  exact raw_update_malformed_factory_aborts raw ctx
    (parseFactoryInfoExact validAccount) validAccount hashCode
    (bountyBorshString factoryId ++ [2]) hraw
    (parse_factory_info_rejects_invalid_bool
      validAccount factoryId hfits hvalid)

theorem parsed_update_trailing_factory_byte_aborts
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (info : FactoryInfo) (extra : UInt8)
    (hraw : raw daoFactoryKey =
      some (encodeFactoryInfo info ++ [extra]))
    (hfits : wireStringFits info.factoryId)
    (hvalid : validAccount info.factoryId = true) :
    runParsedUpdateExport raw ctx validAccount hashCode = none := by
  exact raw_update_malformed_factory_aborts raw ctx
    (parseFactoryInfoExact validAccount) validAccount hashCode
    (encodeFactoryInfo info ++ [extra]) hraw
    (parse_factory_info_rejects_trailing_byte
      validAccount info extra hfits hvalid)

end SputnikDAO2
