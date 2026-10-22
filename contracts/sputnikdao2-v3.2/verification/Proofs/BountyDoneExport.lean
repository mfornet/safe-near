import Model.BountyDoneExport
import Proofs.ExportWrapper
import Proofs.BountyGiveupExport

namespace SputnikDAO2

theorem bounty_done_stored_requires_shared_lock
    (state : BountyDoneExportState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description : String)
    (hne : state.bounty.locked ≠ state.proposals.locked) :
    bountyDoneStored state ctx target bountyId description = none := by
  simp [bountyDoneStored, hne]

theorem bounty_done_stored_completed_first_aborts
    (state : BountyDoneExportState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claims : List StoredBountyClaim) (claim : StoredBountyClaim)
    (remaining : List StoredBountyClaim)
    (htarget : target.getD ctx.predecessor = account)
    (hclaims : state.bounty.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (claim, remaining)) (hcompleted : claim.completed = true) :
    bountyDoneStored state ctx target bountyId description = none := by
  simp [bountyDoneStored, htarget, hclaims, hfind, hcompleted]

theorem bounty_done_stored_expired_clears_claim
    (state : BountyDoneExportState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claims : List StoredBountyClaim) (claim : StoredBountyClaim)
    (remaining : List StoredBountyClaim) (removed : BountyStorageState)
    (hlock : state.bounty.locked = state.proposals.locked)
    (htarget : target.getD ctx.predecessor = account)
    (hclaims : state.bounty.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (claim, remaining))
    (hremove : removeStoredClaim state.bounty account bountyId =
      some (removed, claim))
    (hwidth : bountyId ≤ maxU64 ∧ claim.completed = false ∧
      claim.start ≤ maxU64 ∧ claim.deadline ≤ maxU64 ∧
      ctx.blockTimestamp ≤ maxU64 ∧
      claim.start + claim.deadline ≤ maxU64)
    (hexpired : claim.start + claim.deadline < ctx.blockTimestamp) :
    bountyDoneStored state ctx target bountyId description =
      some (⟨removed, state.proposals⟩, .expired) := by
  simp [bountyDoneStored, hlock, htarget, hclaims, hfind, hremove,
    hwidth.1, hwidth.2.1, hwidth.2.2.1, hwidth.2.2.2.1,
    hwidth.2.2.2.2.1, hwidth.2.2.2.2.2, hexpired]

theorem bounty_done_stored_expired_success_removes
    (state after : BountyDoneExportState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description : String)
    (h : bountyDoneStored state ctx target bountyId description =
      some (after, .expired)) :
    ∃ claim,
      removeStoredClaim state.bounty (target.getD ctx.predecessor)
        bountyId = some (after.bounty, claim) ∧
      after.proposals = state.proposals := by
  by_cases hlock : state.bounty.locked = state.proposals.locked
  · let account := target.getD ctx.predecessor
    cases hclaims : state.bounty.claimers account with
    | none => simp [bountyDoneStored, hlock, account, hclaims] at h
    | some claims =>
        cases hfind : removeFirstBountyClaim claims bountyId with
        | none =>
            simp [bountyDoneStored, hlock, account, hclaims, hfind] at h
        | some pair =>
            obtain ⟨found, remaining⟩ := pair
            by_cases hexpired : found.start + found.deadline <
                ctx.blockTimestamp
            · cases hremove : removeStoredClaim state.bounty account
                  bountyId with
              | none =>
                  simp [bountyDoneStored, hlock, account, hclaims,
                    hfind, hexpired, hremove] at h
              | some removedPair =>
                  obtain ⟨removed, claim⟩ := removedPair
                  simp [bountyDoneStored, hlock, account, hclaims,
                    hfind, hexpired, hremove] at h
                  obtain ⟨_, heq⟩ := h
                  have hafter : after = ⟨removed, state.proposals⟩ :=
                    heq.symm
                  subst after
                  exact ⟨claim, rfl, rfl⟩
            · simp [bountyDoneStored, hlock, account, hclaims,
                hfind, hexpired] at h
              cases hadd : addProposal state.proposals ctx
                  (.bountyDone bountyId (target.getD ctx.predecessor))
                  description with
              | none => simp [hadd] at h
              | some pair =>
                  obtain ⟨created, id⟩ := pair
                  cases hcomplete : completeStoredClaim state.bounty
                      (target.getD ctx.predecessor) bountyId with
                  | none => simp [hadd, hcomplete] at h
                  | some completed => simp [hadd, hcomplete] at h
  · simp [bountyDoneStored, hlock] at h

theorem bounty_done_stored_active_requires_self
    (state : BountyDoneExportState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claims : List StoredBountyClaim) (claim : StoredBountyClaim)
    (remaining : List StoredBountyClaim)
    (htarget : target.getD ctx.predecessor = account)
    (hclaims : state.bounty.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (claim, remaining))
    (hactive : ctx.blockTimestamp ≤ claim.start + claim.deadline)
    (hother : account ≠ ctx.predecessor) :
    bountyDoneStored state ctx target bountyId description = none := by
  simp [bountyDoneStored, htarget, hclaims, hfind,
    Nat.not_lt.mpr hactive, hother]

theorem bounty_done_stored_active_creates_and_completes
    (state : BountyDoneExportState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description account : String)
    (claims : List StoredBountyClaim) (claim : StoredBountyClaim)
    (remaining : List StoredBountyClaim)
    (created : ProposalCreateState) (proposalId : Nat)
    (completed : BountyStorageState)
    (hlock : state.bounty.locked = state.proposals.locked)
    (htarget : target.getD ctx.predecessor = account)
    (hclaims : state.bounty.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (claim, remaining))
    (hwidth : bountyId ≤ maxU64 ∧ claim.completed = false ∧
      claim.start ≤ maxU64 ∧ claim.deadline ≤ maxU64 ∧
      ctx.blockTimestamp ≤ maxU64 ∧
      claim.start + claim.deadline ≤ maxU64)
    (hactive : ctx.blockTimestamp ≤ claim.start + claim.deadline)
    (hself : account = ctx.predecessor)
    (hadd : addProposal state.proposals ctx
      (.bountyDone bountyId account) description =
      some (created, proposalId))
    (hcomplete : completeStoredClaim state.bounty account bountyId =
      some completed) :
    bountyDoneStored state ctx target bountyId description =
      some (⟨{ completed with locked := created.locked }, created⟩,
        .proposal proposalId) := by
  have htargetSelf : target.getD ctx.predecessor = ctx.predecessor :=
    htarget.trans hself
  rw [hself] at hclaims hadd hcomplete
  simp [bountyDoneStored, hlock, htargetSelf, hclaims, hfind,
    hwidth.1, hwidth.2.1, hwidth.2.2.1, hwidth.2.2.2.1,
    hwidth.2.2.2.2.1, hwidth.2.2.2.2.2,
    Nat.not_lt.mpr hactive, hadd, hcomplete]

theorem bounty_done_stored_active_success_shape
    (state after : BountyDoneExportState) (ctx : ProposalCreateContext)
    (target : Option String) (bountyId proposalId : Nat)
    (description : String)
    (h : bountyDoneStored state ctx target bountyId description =
      some (after, .proposal proposalId)) :
    ∃ completed,
      completeStoredClaim state.bounty (target.getD ctx.predecessor)
        bountyId = some completed ∧
      after.bounty =
        { completed with locked := after.proposals.locked } := by
  by_cases hlock : state.bounty.locked = state.proposals.locked
  · let account := target.getD ctx.predecessor
    cases hclaims : state.bounty.claimers account with
    | none => simp [bountyDoneStored, hlock, account, hclaims] at h
    | some claims =>
        cases hfind : removeFirstBountyClaim claims bountyId with
        | none =>
            simp [bountyDoneStored, hlock, account, hclaims, hfind] at h
        | some pair =>
            obtain ⟨found, remaining⟩ := pair
            by_cases hexpired : found.start + found.deadline <
                ctx.blockTimestamp
            · cases hremove : removeStoredClaim state.bounty account
                  bountyId with
              | none =>
                  simp [bountyDoneStored, hlock, account, hclaims,
                    hfind, hexpired, hremove] at h
              | some removedPair =>
                  simp [bountyDoneStored, hlock, account, hclaims,
                    hfind, hexpired, hremove] at h
            · by_cases hself : account = ctx.predecessor
              · have htargetSelf : target.getD ctx.predecessor =
                    ctx.predecessor := hself
                rw [hself] at hclaims
                cases hadd : addProposal state.proposals ctx
                    (.bountyDone bountyId ctx.predecessor) description with
                | none =>
                    simp [bountyDoneStored, hlock, htargetSelf, hclaims,
                      hfind, hexpired, hadd] at h
                | some createdPair =>
                    obtain ⟨created, id⟩ := createdPair
                    cases hcomplete : completeStoredClaim state.bounty
                        ctx.predecessor bountyId with
                    | none =>
                        simp [bountyDoneStored, hlock, htargetSelf,
                          hclaims, hfind, hexpired, hadd,
                          hcomplete] at h
                    | some completed =>
                        simp [bountyDoneStored, hlock, htargetSelf,
                          hclaims, hfind, hexpired, hadd,
                          hcomplete] at h
                        obtain ⟨_, heq⟩ := h
                        have hafter : after =
                            ⟨{ completed with locked := created.locked },
                              created⟩ := heq.1.symm
                        subst after
                        exact ⟨completed, by simpa [htargetSelf] using
                          hcomplete, rfl⟩
              · simp [bountyDoneStored, hlock, account, hclaims,
                  hfind, hexpired, hself] at h
  · simp [bountyDoneStored, hlock] at h

theorem bounty_done_raw_expired_is_claim_removal
    (raw : BountyRawTrie) (before after : BountyDoneExportState)
    (account : String) (bountyId : Nat) (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes) :
    bountyDoneRawEffect raw before after account bountyId .expired
      decoded encodeProposal =
      bountyRawRemoveClaim raw before.bounty account bountyId := by
  rfl

theorem bounty_done_expired_raw_preserves_valid_image
    (raw afterRaw : BountyRawTrie)
    (before after : BountyDoneExportState)
    (account : String) (bountyId : Nat)
    (claim : StoredBountyClaim) (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw before.bounty)
    (hserial : bountyStorageSerializable before.bounty)
    (hremove : removeStoredClaim before.bounty account bountyId =
      some (after.bounty, claim))
    (hraw : bountyDoneRawEffect raw before after account bountyId
      .expired decoded encodeProposal = some afterRaw) :
    bountyRawImage afterRaw after.bounty ∧
      bountyStorageSerializable after.bounty := by
  exact bounty_giveup_remove_preserves_valid_image raw afterRaw
    before.bounty after.bounty account bountyId claim hid himage hserial
    hremove (by simpa [bountyDoneRawEffect] using hraw)

theorem proposal_write_preserves_bounty_image
    (raw : BountyRawTrie) (state : BountyStorageState)
    (proposalId : Nat) (proposalBytes : BountyBytes)
    (himage : bountyRawImage raw state) :
    bountyRawImage
      (bountyRawWrite raw (daoProposalEntryKey proposalId) proposalBytes)
      state := by
  constructor
  · intro account
    have hsep : bountyClaimersKey account ≠
        daoProposalEntryKey proposalId := by
      simp [bountyClaimersKey, daoProposalEntryKey]
    simpa [bountyRawWrite, hsep] using himage.1 account
  · intro id hid
    have hsep : bountyCountKey id ≠ daoProposalEntryKey proposalId := by
      simp [bountyCountKey, daoProposalEntryKey]
    simpa [bountyRawWrite, hsep] using himage.2 id hid

theorem bounty_done_active_raw_preserves_valid_image
    (raw afterRaw : BountyRawTrie)
    (before after : BountyDoneExportState)
    (account : String) (bountyId proposalId : Nat)
    (claims completedClaims : List StoredBountyClaim)
    (proposal : CreatedProposal) (completed : BountyStorageState)
    (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (himage : bountyRawImage raw before.bounty)
    (hserial : bountyStorageSerializable before.bounty)
    (hclaims : before.bounty.claimers account = some claims)
    (hcomplete : completeFirstBountyClaim claims bountyId =
      some completedClaims)
    (hstate : completeStoredClaim before.bounty account bountyId =
      some completed)
    (hbounty : after.bounty =
      { completed with locked := after.proposals.locked })
    (hproposal : proposalAt after.proposals.proposals proposalId =
      some proposal)
    (hraw : bountyDoneRawEffect raw before after account bountyId
      (.proposal proposalId) decoded encodeProposal = some afterRaw) :
    bountyRawImage afterRaw after.bounty ∧
      bountyStorageSerializable after.bounty := by
  let proposalRaw := bountyRawWrite raw (daoProposalEntryKey proposalId)
    (encodeProposal proposal)
  have himageProposal : bountyRawImage proposalRaw before.bounty :=
    proposal_write_preserves_bounty_image raw before.bounty proposalId
      (encodeProposal proposal) himage
  obtain ⟨next, nextRaw, hnext, hnextRaw, himageNext,
    hserialNext⟩ :=
    bounty_raw_complete_claim_preserves_valid_image proposalRaw
      before.bounty account bountyId claims completedClaims
      himageProposal hserial hclaims hcomplete
  rw [hstate] at hnext
  have hnextEq : next = completed := (Option.some.inj hnext).symm
  have hrawStep : bountyRawCompleteClaim proposalRaw before.bounty account
      bountyId = some afterRaw := by
    have hraw' := hraw
    simp [bountyDoneRawEffect, hproposal] at hraw'
    exact hraw'.2
  rw [hrawStep] at hnextRaw
  have hrawEq : nextRaw = afterRaw := (Option.some.inj hnextRaw).symm
  subst next
  subst nextRaw
  rw [hbounty]
  simpa [bountyRawImage, bountyStorageSerializable] using
    And.intro himageNext hserialNext

theorem bounty_done_raw_active_rejects_malformed_old_proposal
    (raw : BountyRawTrie) (before after : BountyDoneExportState)
    (account : String) (bountyId proposalId : Nat)
    (encodeProposal : CreatedProposal → BountyBytes)
    (hoccupied : (raw (daoProposalEntryKey proposalId)).isSome = true) :
    bountyDoneRawEffect raw before after account bountyId
      (.proposal proposalId) false encodeProposal = none := by
  cases hp : proposalAt after.proposals.proposals proposalId with
  | none => simp [bountyDoneRawEffect, hp]
  | some proposal =>
      simp [bountyDoneRawEffect, hp, hoccupied]

theorem bounty_done_raw_active_success_witnesses
    (raw afterRaw : BountyRawTrie)
    (before after : BountyDoneExportState)
    (account : String) (bountyId proposalId : Nat)
    (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (hraw : bountyDoneRawEffect raw before after account bountyId
      (.proposal proposalId) decoded encodeProposal = some afterRaw) :
    ∃ proposal claims completedClaims,
      proposalAt after.proposals.proposals proposalId = some proposal ∧
      before.bounty.claimers account = some claims ∧
      completeFirstBountyClaim claims bountyId = some completedClaims := by
  cases hp : proposalAt after.proposals.proposals proposalId with
  | none => simp [bountyDoneRawEffect, hp] at hraw
  | some proposal =>
      cases hclaims : before.bounty.claimers account with
      | none =>
          simp [bountyDoneRawEffect, hp, bountyRawCompleteClaim,
            hclaims] at hraw
      | some claims =>
          cases hcomplete : completeFirstBountyClaim claims bountyId with
          | none =>
              simp [bountyDoneRawEffect, hp, bountyRawCompleteClaim,
                hclaims, hcomplete] at hraw
          | some completedClaims =>
              exact ⟨proposal, claims, completedClaims, rfl, rfl,
                hcomplete⟩

theorem bounty_done_export_success_root
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : BountyDoneExportState) (create : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description : String)
    (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (effect : BountyDoneExportEffect)
    (h : runBountyDoneExport raw wrapper (some state) create target bountyId
      description oldProposalDecoded encodeProposal encodeRoot =
      some (final, effect)) :
    ∃ after,
      bountyDoneStored state
        ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
          wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
        target bountyId description = some (after, effect) ∧
      final daoRootKey = some (encodeRoot after) := by
  let bodyCtx : ProposalCreateContext :=
    ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
      wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
  cases hstep : bountyDoneStored state bodyCtx target bountyId description with
  | none => simp [runBountyDoneExport, bodyCtx, hstep] at h
  | some pair =>
      obtain ⟨after, outcome⟩ := pair
      let account := target.getD wrapper.predecessor
      cases hraw : bountyDoneRawEffect raw state after account bountyId
          outcome oldProposalDecoded encodeProposal with
      | none => simp [runBountyDoneExport, bodyCtx, account, hstep, hraw] at h
      | some afterRaw =>
          cases hw : runGeneratedCallWrapper raw "bounty_done"
              { wrapper with stateDecoded := true }
              (some (afterRaw, encodeRoot after)) with
          | none =>
              simp [runBountyDoneExport, bodyCtx, account, hstep,
                hraw, hw] at h
          | some produced =>
              simp [runBountyDoneExport, bodyCtx, account, hstep,
                hraw, hw] at h
              obtain ⟨rfl, rfl⟩ := h
              have hfinal := generated_call_success_is_root_write raw
                afterRaw produced "bounty_done"
                { wrapper with stateDecoded := true }
                (encodeRoot after) hw
              exact ⟨after, rfl, by simp [hfinal, bountyRawWrite]⟩

theorem bounty_done_export_success_body
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : BountyDoneExportState) (create : ProposalCreateContext)
    (target : Option String) (bountyId : Nat) (description : String)
    (oldProposalDecoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (effect : BountyDoneExportEffect)
    (h : runBountyDoneExport raw wrapper (some state) create target bountyId
      description oldProposalDecoded encodeProposal encodeRoot =
      some (final, effect)) :
    ∃ after afterRaw,
      bountyDoneStored state
        ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
          wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
        target bountyId description = some (after, effect) ∧
      bountyDoneRawEffect raw state after
        (target.getD wrapper.predecessor) bountyId effect
        oldProposalDecoded encodeProposal = some afterRaw ∧
      final = bountyRawWrite afterRaw daoRootKey (encodeRoot after) := by
  let bodyCtx : ProposalCreateContext :=
    ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
      wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
  cases hstep : bountyDoneStored state bodyCtx target bountyId description with
  | none => simp [runBountyDoneExport, bodyCtx, hstep] at h
  | some pair =>
      obtain ⟨after, outcome⟩ := pair
      let account := target.getD wrapper.predecessor
      cases hraw : bountyDoneRawEffect raw state after account bountyId
          outcome oldProposalDecoded encodeProposal with
      | none => simp [runBountyDoneExport, bodyCtx, account, hstep, hraw] at h
      | some afterRaw =>
          cases hw : runGeneratedCallWrapper raw "bounty_done"
              { wrapper with stateDecoded := true }
              (some (afterRaw, encodeRoot after)) with
          | none =>
              simp [runBountyDoneExport, bodyCtx, account, hstep,
                hraw, hw] at h
          | some produced =>
              simp [runBountyDoneExport, bodyCtx, account, hstep,
                hraw, hw] at h
              obtain ⟨rfl, rfl⟩ := h
              have hfinal := generated_call_success_is_root_write raw
                afterRaw produced "bounty_done"
                { wrapper with stateDecoded := true }
                (encodeRoot after) hw
              exact ⟨after, afterRaw, rfl, hraw, hfinal⟩

theorem root_write_preserves_bounty_image
    (raw : BountyRawTrie) (state : BountyStorageState)
    (rootBytes : BountyBytes) (himage : bountyRawImage raw state) :
    bountyRawImage (bountyRawWrite raw daoRootKey rootBytes) state := by
  constructor
  · intro account
    simpa [bountyRawWrite, daoRootKey, bountyClaimersKey] using
      himage.1 account
  · intro id hid
    simpa [bountyRawWrite, daoRootKey, bountyCountKey] using
      himage.2 id hid

theorem bounty_done_expired_export_preserves_valid_image
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state after : BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (bountyId : Nat) (description : String) (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (claim : StoredBountyClaim)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state.bounty)
    (hserial : bountyStorageSerializable state.bounty)
    (hstep : bountyDoneStored state
      ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
        wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
      target bountyId description = some (after, .expired))
    (hremove : removeStoredClaim state.bounty
      (target.getD wrapper.predecessor) bountyId =
      some (after.bounty, claim))
    (h : runBountyDoneExport raw wrapper (some state) create target
      bountyId description decoded encodeProposal encodeRoot =
      some (final, .expired)) :
    bountyRawImage final after.bounty ∧
      bountyStorageSerializable after.bounty := by
  obtain ⟨actual, afterRaw, hlogical, hraw, hfinal⟩ :=
    bounty_done_export_success_body raw final wrapper state create target
      bountyId description decoded encodeProposal encodeRoot .expired h
  rw [hstep] at hlogical
  have heq := Option.some.inj hlogical
  have hactual : actual = after := (Prod.mk.inj heq).1.symm
  subst actual
  have hvalid := bounty_done_expired_raw_preserves_valid_image raw afterRaw
    state after (target.getD wrapper.predecessor) bountyId claim decoded
    encodeProposal hid himage hserial hremove hraw
  rw [hfinal]
  exact ⟨root_write_preserves_bounty_image afterRaw after.bounty
    (encodeRoot after) hvalid.1, hvalid.2⟩

theorem bounty_done_expired_export_success_valid_image
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (bountyId : Nat) (description : String) (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state.bounty)
    (hserial : bountyStorageSerializable state.bounty)
    (h : runBountyDoneExport raw wrapper (some state) create target
      bountyId description decoded encodeProposal encodeRoot =
      some (final, .expired)) :
    ∃ after,
      bountyDoneStored state
        ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
          wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
        target bountyId description = some (after, .expired) ∧
      bountyRawImage final after.bounty ∧
      bountyStorageSerializable after.bounty := by
  obtain ⟨after, _, hstep, _, _⟩ :=
    bounty_done_export_success_body raw final wrapper state create target
      bountyId description decoded encodeProposal encodeRoot .expired h
  obtain ⟨claim, hremove, _⟩ :=
    bounty_done_stored_expired_success_removes state after
      ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
        wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
      target bountyId description hstep
  have hvalid := bounty_done_expired_export_preserves_valid_image raw final
    wrapper state after create target bountyId description decoded
    encodeProposal encodeRoot claim hid himage hserial hstep hremove h
  exact ⟨after, hstep, hvalid.1, hvalid.2⟩

theorem bounty_done_active_export_preserves_valid_image
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state after : BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (bountyId proposalId : Nat) (description : String) (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (claims completedClaims : List StoredBountyClaim)
    (proposal : CreatedProposal) (completed : BountyStorageState)
    (himage : bountyRawImage raw state.bounty)
    (hserial : bountyStorageSerializable state.bounty)
    (hstep : bountyDoneStored state
      ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
        wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
      target bountyId description = some (after, .proposal proposalId))
    (hclaims : state.bounty.claimers (target.getD wrapper.predecessor) =
      some claims)
    (hcomplete : completeFirstBountyClaim claims bountyId =
      some completedClaims)
    (hstate : completeStoredClaim state.bounty
      (target.getD wrapper.predecessor) bountyId = some completed)
    (hbounty : after.bounty =
      { completed with locked := after.proposals.locked })
    (hproposal : proposalAt after.proposals.proposals proposalId =
      some proposal)
    (h : runBountyDoneExport raw wrapper (some state) create target
      bountyId description decoded encodeProposal encodeRoot =
      some (final, .proposal proposalId)) :
    bountyRawImage final after.bounty ∧
      bountyStorageSerializable after.bounty := by
  obtain ⟨actual, afterRaw, hlogical, hraw, hfinal⟩ :=
    bounty_done_export_success_body raw final wrapper state create target
      bountyId description decoded encodeProposal encodeRoot
      (.proposal proposalId) h
  rw [hstep] at hlogical
  have heq := Option.some.inj hlogical
  have hactual : actual = after := (Prod.mk.inj heq).1.symm
  subst actual
  have hvalid := bounty_done_active_raw_preserves_valid_image raw afterRaw
    state after (target.getD wrapper.predecessor) bountyId proposalId
    claims completedClaims proposal completed decoded encodeProposal
    himage hserial hclaims hcomplete hstate hbounty hproposal hraw
  rw [hfinal]
  exact ⟨root_write_preserves_bounty_image afterRaw after.bounty
    (encodeRoot after) hvalid.1, hvalid.2⟩

theorem bounty_done_active_export_success_valid_image
    (raw final : BountyRawTrie) (wrapper : CallWrapperContext)
    (state : BountyDoneExportState)
    (create : ProposalCreateContext) (target : Option String)
    (bountyId proposalId : Nat) (description : String) (decoded : Bool)
    (encodeProposal : CreatedProposal → BountyBytes)
    (encodeRoot : BountyDoneExportState → BountyBytes)
    (himage : bountyRawImage raw state.bounty)
    (hserial : bountyStorageSerializable state.bounty)
    (h : runBountyDoneExport raw wrapper (some state) create target
      bountyId description decoded encodeProposal encodeRoot =
      some (final, .proposal proposalId)) :
    ∃ after,
      bountyDoneStored state
        ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
          wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
        target bountyId description = some (after, .proposal proposalId) ∧
      bountyRawImage final after.bounty ∧
      bountyStorageSerializable after.bounty := by
  obtain ⟨after, afterRaw, hstep, hraw, _⟩ :=
    bounty_done_export_success_body raw final wrapper state create target
      bountyId description decoded encodeProposal encodeRoot
      (.proposal proposalId) h
  obtain ⟨completed, hstate, hbounty⟩ :=
    bounty_done_stored_active_success_shape state after
      ⟨wrapper.predecessor, create.blockTimestamp, create.blockHeight,
        wrapper.attachedDeposit, create.policyBond, create.addPermission⟩
      target bountyId proposalId description hstep
  obtain ⟨proposal, claims, completedClaims, hproposal, hclaims,
    hcomplete⟩ :=
    bounty_done_raw_active_success_witnesses raw afterRaw state after
      (target.getD wrapper.predecessor) bountyId proposalId decoded
      encodeProposal hraw
  have hvalid := bounty_done_active_export_preserves_valid_image raw final
    wrapper state after create target bountyId proposalId description
    decoded encodeProposal encodeRoot claims completedClaims proposal
    completed himage hserial hstep hclaims hcomplete hstate hbounty
    hproposal h
  exact ⟨after, hstep, hvalid.1, hvalid.2⟩

end SputnikDAO2
