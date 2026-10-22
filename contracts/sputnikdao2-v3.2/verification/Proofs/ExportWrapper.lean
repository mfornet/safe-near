import Model.ExportWrapper

namespace SputnikDAO2

theorem dao_export_inventory_count : daoExports.length = 34 := by decide

theorem dao_export_names_unique :
    (daoExports.map ExportInfo.name).Nodup := by decide

theorem dao_export_class_counts :
    (daoExports.filter (fun e => e.kind == .init)).length = 2 ∧
    (daoExports.filter (fun e => e.kind == .call)).length = 10 ∧
    (daoExports.filter (fun e => e.kind == .view)).length = 20 ∧
    (daoExports.filter (fun e => e.kind == .raw)).length = 2 := by
  decide

theorem only_callback_is_private_generated_call :
    (daoExports.filter (fun e =>
      e.kind == .call && e.privateCall)).map ExportInfo.name =
      ["on_proposal_callback"] := by decide

theorem generated_payable_calls :
    (daoExports.filter (fun e =>
      e.kind == .call && e.payable)).map ExportInfo.name =
      ["add_proposal", "bounty_claim", "bounty_done",
       "register_delegation"] := by decide

theorem owned_staking_export_is_view :
    (findDAOExport "get_staking_contract").map ExportInfo.kind =
      some .view := by decide

theorem raw_exports_skip_generated_wrapper :
    (findDAOExport "store_blob").map ExportInfo.kind = some .raw ∧
    (findDAOExport "update").map ExportInfo.kind = some .raw := by
  decide

theorem generated_callback_rejects_external_caller
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (body : Option (BountyRawTrie × BountyBytes))
    (h : ctx.current ≠ ctx.predecessor) :
    runGeneratedCallWrapper raw "on_proposal_callback" ctx body = none := by
  have hi : findDAOExport "on_proposal_callback" =
      some ⟨"on_proposal_callback", .call, false, true⟩ := by decide
  simp [runGeneratedCallWrapper, hi, h]

theorem generated_nonpayable_call_rejects_deposit
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (body : Option (BountyRawTrie × BountyBytes))
    (hdeposit : ctx.attachedDeposit ≠ 0) :
    runGeneratedCallWrapper raw "remove_blob" ctx body = none := by
  have hi : findDAOExport "remove_blob" =
      some ⟨"remove_blob", .call, false, false⟩ := by decide
  simp [runGeneratedCallWrapper, hi, hdeposit]

theorem generated_call_requires_decoded_state
    (raw : BountyRawTrie) (name : String)
    (ctx : CallWrapperContext)
    (body : Option (BountyRawTrie × BountyBytes))
    (hdecoded : ctx.stateDecoded = false) :
    runGeneratedCallWrapper raw name ctx body = none := by
  cases hi : findDAOExport name with
  | none => simp [runGeneratedCallWrapper, hi]
  | some info => simp [runGeneratedCallWrapper, hi, hdecoded]

theorem generated_call_body_abort_has_no_result
    (raw : BountyRawTrie) (name : String)
    (ctx : CallWrapperContext) :
    runGeneratedCallWrapper raw name ctx none = none := by
  cases hi : findDAOExport name with
  | none => simp [runGeneratedCallWrapper, hi]
  | some info => simp [runGeneratedCallWrapper, hi]

theorem noncall_export_uses_other_wrapper
    (raw : BountyRawTrie) (name : String)
    (ctx : CallWrapperContext)
    (body : Option (BountyRawTrie × BountyBytes))
    (info : ExportInfo)
    (hinfo : findDAOExport name = some info)
    (hkind : info.kind ≠ .call) :
    runGeneratedCallWrapper raw name ctx body = none := by
  simp [runGeneratedCallWrapper, hinfo, hkind]

theorem generated_call_success_writes_root
    (raw afterBody final : BountyRawTrie)
    (name : String) (ctx : CallWrapperContext)
    (rootBytes : BountyBytes)
    (h : runGeneratedCallWrapper raw name ctx
      (some (afterBody, rootBytes)) = some final) :
    final daoRootKey = some rootBytes := by
  cases hi : findDAOExport name with
  | none => simp [runGeneratedCallWrapper, hi] at h
  | some info =>
      simp only [runGeneratedCallWrapper, hi] at h
      split at h
      · contradiction
      · simp at h
        cases h
        simp [bountyRawWrite]

theorem generated_call_success_is_root_write
    (raw afterBody final : BountyRawTrie)
    (name : String) (ctx : CallWrapperContext)
    (rootBytes : BountyBytes)
    (h : runGeneratedCallWrapper raw name ctx
      (some (afterBody, rootBytes)) = some final) :
    final = bountyRawWrite afterBody daoRootKey rootBytes := by
  cases hi : findDAOExport name with
  | none => simp [runGeneratedCallWrapper, hi] at h
  | some info =>
      simp only [runGeneratedCallWrapper, hi] at h
      split at h
      · contradiction
      · simp at h
        exact h.symm

theorem generated_view_preserves_raw
    {α β : Type} (raw final : BountyRawTrie) (name : String)
    (decoded : Option α) (deposit : Nat)
    (view : α → BountyRawTrie → β) (result : β)
    (h : runGeneratedViewWrapper raw name decoded deposit view =
      some (result, final)) :
    final = raw := by
  cases hi : findDAOExport name with
  | none => simp [runGeneratedViewWrapper, hi] at h
  | some info =>
      by_cases hkind : info.kind = .view
      · cases decoded with
        | none =>
            simp [runGeneratedViewWrapper, hi, hkind,
              runViewWrapper] at h
        | some state =>
            simp [runGeneratedViewWrapper, hi, hkind,
              runViewWrapper] at h
            exact h.2.symm
      · simp [runGeneratedViewWrapper, hi, hkind] at h

end SputnikDAO2
