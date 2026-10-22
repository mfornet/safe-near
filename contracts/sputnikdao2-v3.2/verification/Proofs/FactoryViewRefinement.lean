import Model.FactoryViewRefinement
import Proofs.ViewExport
import Proofs.UpdateExport

namespace SputnikDAO2

theorem parsed_factory_view_reads_shared_info
    (raw : BountyRawTrie) (deposit : Nat) (current : String)
    (validAccount : String → Bool) :
    runParsedFactoryInfoView raw (some ()) deposit current validAccount =
      (readFactoryInfoFromRaw raw current validAccount).map
        (fun info => (info, raw)) := by
  have hi : findDAOExport "get_factory_info" =
      some ⟨"get_factory_info", .view, false, false⟩ := by decide
  cases hread : readFactoryInfoFromRaw raw current validAccount with
  | none => simp [runParsedFactoryInfoView, hread]
  | some info =>
      simp [runParsedFactoryInfoView, hread,
        runGeneratedViewWrapper, hi, runViewWrapper]

theorem parsed_factory_view_requires_root_decode
    (raw : BountyRawTrie) (deposit : Nat) (current : String)
    (validAccount : String → Bool) :
    runParsedFactoryInfoView raw none deposit current validAccount = none := by
  simp [runParsedFactoryInfoView]

theorem parsed_factory_view_stored_bytes
    (raw : BountyRawTrie) (deposit : Nat) (current : String)
    (validAccount : String → Bool) (info : FactoryInfo)
    (hraw : raw daoFactoryKey = some (encodeFactoryInfo info))
    (hfits : wireStringFits info.factoryId)
    (hvalid : validAccount info.factoryId = true) :
    runParsedFactoryInfoView raw (some ()) deposit current validAccount =
      some (info, raw) := by
  rw [parsed_factory_view_reads_shared_info]
  simp [readFactoryInfoFromRaw, factoryReadFromRaw, hraw,
    parse_factory_info_exact_encoded validAccount info hfits hvalid,
    effectiveFactory]

theorem parsed_factory_view_malformed_bool_aborts
    (raw : BountyRawTrie) (deposit : Nat) (current factoryId : String)
    (validAccount : String → Bool)
    (hraw : raw daoFactoryKey =
      some (bountyBorshString factoryId ++ [2]))
    (hfits : wireStringFits factoryId)
    (hvalid : validAccount factoryId = true) :
    runParsedFactoryInfoView raw (some ()) deposit current validAccount =
      none := by
  rw [parsed_factory_view_reads_shared_info]
  simp [readFactoryInfoFromRaw, factoryReadFromRaw, hraw,
    parse_factory_info_rejects_invalid_bool
      validAccount factoryId hfits hvalid, effectiveFactory]

theorem parsed_factory_view_and_update_share_authorization_info
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (info : FactoryInfo)
    (hread : readFactoryInfoFromRaw raw ctx.current validAccount =
      some info) :
    runParsedUpdateExport raw ctx validAccount hashCode =
      runUpdate hashCode
        { current := ctx.current
          predecessor := ctx.predecessor
          factoryRead := .stored info
          fallbackFactory := none
          successfulPromiseResult := ctx.successfulPromiseResult
          rawInput := ctx.rawInput } := by
  rw [runParsedUpdateExport, raw_update_uses_source_projection]
  simp only [readFactoryInfoFromRaw] at hread
  cases hfactory : factoryReadFromRaw raw
      (parseFactoryInfoExact validAccount) with
  | missing =>
      cases hparent : validatedFactoryParent ctx.current validAccount with
      | none => simp [effectiveFactory, hfactory, hparent] at hread
      | some parent =>
          simp [effectiveFactory, hfactory, hparent] at hread
          cases hread
          simp [runUpdate, effectiveFactory,
            updateAuthorized]
  | stored storedInfo =>
      simp [effectiveFactory, hfactory] at hread
      cases hread
      simp [runUpdate, effectiveFactory, updateAuthorized]
  | malformed => simp [effectiveFactory, hfactory] at hread

theorem parsed_factory_view_result_controls_update
    (raw : BountyRawTrie) (ctx : RawUpdateContext)
    (validAccount : String → Bool) (hashCode : CodeBytes → String)
    (deposit : Nat) (info : FactoryInfo)
    (hview : runParsedFactoryInfoView raw (some ()) deposit
      ctx.current validAccount = some (info, raw)) :
    runParsedUpdateExport raw ctx validAccount hashCode =
      runUpdate hashCode
        { current := ctx.current
          predecessor := ctx.predecessor
          factoryRead := .stored info
          fallbackFactory := none
          successfulPromiseResult := ctx.successfulPromiseResult
          rawInput := ctx.rawInput } := by
  rw [parsed_factory_view_reads_shared_info] at hview
  cases hread : readFactoryInfoFromRaw raw ctx.current validAccount with
  | none => simp [hread] at hview
  | some resolved =>
      simp [hread] at hview
      subst resolved
      exact parsed_factory_view_and_update_share_authorization_info
        raw ctx validAccount hashCode info hread

end SputnikDAO2
