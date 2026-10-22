import Model.BountyClaimExport
import Proofs.ExportWrapper
import Proofs.BountySerial

namespace SputnikDAO2

theorem bounty_claim_export_requires_bounty
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyStorageState) (policyBond : Option Nat)
    (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) :
    runBountyClaimExport raw ctx state none policyBond bountyId now
      deadline encodeRoot = none := by
  simp [runBountyClaimExport]

theorem bounty_claim_export_requires_policy
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyStorageState)
    (bounty : Option (Nat × Nat)) (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) :
    runBountyClaimExport raw ctx state bounty none bountyId now
      deadline encodeRoot = none := by
  simp [runBountyClaimExport]

theorem bounty_claim_export_wrong_bond_aborts
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyStorageState)
    (bounty : Option (Nat × Nat)) (bond : Nat)
    (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes)
    (hbond : ctx.attachedDeposit ≠ bond) :
    runBountyClaimExport raw ctx state bounty (some bond)
      bountyId now deadline encodeRoot = none := by
  simp [runBountyClaimExport, addStoredClaim, hbond]

theorem bounty_claim_export_success_body
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyStorageState) (maxDeadline times bond : Nat)
    (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes)
    (h : runBountyClaimExport raw ctx (some state)
      (some (maxDeadline, times)) (some bond)
      bountyId now deadline encodeRoot = some final) :
    ∃ after,
      addStoredClaim state ctx.predecessor bountyId now deadline
        maxDeadline times bond ctx.attachedDeposit = some after ∧
      runGeneratedCallWrapper raw "bounty_claim"
        { ctx with stateDecoded := true }
        (some (bountyRawAddClaim raw state ctx.predecessor
          bountyId now deadline ctx.attachedDeposit,
          encodeRoot after)) = some final := by
  cases ha : addStoredClaim state ctx.predecessor bountyId now deadline
      maxDeadline times bond ctx.attachedDeposit with
  | none => simp [runBountyClaimExport, ha] at h
  | some after =>
      refine ⟨after, rfl, ?_⟩
      simpa [runBountyClaimExport, ha] using h

theorem bounty_claim_export_success_keys
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyStorageState) (maxDeadline times bond : Nat)
    (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes)
    (h : runBountyClaimExport raw ctx (some state)
      (some (maxDeadline, times)) (some bond)
      bountyId now deadline encodeRoot = some final) :
    ∃ after,
      addStoredClaim state ctx.predecessor bountyId now deadline
        maxDeadline times bond ctx.attachedDeposit = some after ∧
      final (bountyCountKey bountyId) =
        some (encodeBountyCount ((state.counts bountyId).getD 0 + 1)) ∧
      final (bountyClaimersKey ctx.predecessor) =
        some (encodeStoredBountyClaims
          ((state.claimers ctx.predecessor).getD [] ++
            [⟨bountyId, now, deadline, false, ctx.attachedDeposit⟩])) ∧
      final daoRootKey = some (encodeRoot after) := by
  obtain ⟨after, ha, hw⟩ := bounty_claim_export_success_body
    raw final ctx state maxDeadline times bond bountyId now deadline
    encodeRoot h
  have hfinal := generated_call_success_is_root_write raw
    (bountyRawAddClaim raw state ctx.predecessor bountyId now
      deadline ctx.attachedDeposit) final "bounty_claim"
    { ctx with stateDecoded := true } (encodeRoot after) hw
  rw [hfinal]
  refine ⟨after, ha, ?_, ?_, ?_⟩
  · simp [bountyRawWrite, bountyRawAddClaim,
      bountyCountKey, bountyClaimersKey, daoRootKey]
  · simp [bountyRawWrite, bountyRawAddClaim,
      bountyCountKey, bountyClaimersKey, daoRootKey]
  · simp [bountyRawWrite]

theorem bounty_claim_export_preserves_storage_image
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyStorageState) (maxDeadline times bond : Nat)
    (bountyId now deadline : Nat)
    (encodeRoot : BountyStorageState → BountyBytes)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state)
    (h : runBountyClaimExport raw ctx (some state)
      (some (maxDeadline, times)) (some bond)
      bountyId now deadline encodeRoot = some final) :
    ∃ after,
      addStoredClaim state ctx.predecessor bountyId now deadline
        maxDeadline times bond ctx.attachedDeposit = some after ∧
      bountyRawImage final after ∧ bountyStorageSerializable after := by
  obtain ⟨after, ha, hw⟩ := bounty_claim_export_success_body
    raw final ctx state maxDeadline times bond bountyId now deadline
    encodeRoot h
  have hbond : ctx.attachedDeposit = bond := by
    by_cases heq : ctx.attachedDeposit = bond
    · exact heq
    · simp [addStoredClaim, heq] at ha
  subst bond
  have hvalid := bounty_raw_add_claim_preserves_valid_image raw state
    after ctx.predecessor bountyId now deadline maxDeadline times
    ctx.attachedDeposit hid himage hserial ha
  have hfinal := generated_call_success_is_root_write raw
    (bountyRawAddClaim raw state ctx.predecessor bountyId now
      deadline ctx.attachedDeposit) final "bounty_claim"
    { ctx with stateDecoded := true } (encodeRoot after) hw
  refine ⟨after, ha, ?_, hvalid.2⟩
  constructor
  · intro account
    have hkey := hvalid.1.1 account
    rw [hfinal]
    simpa [bountyRawWrite, bountyClaimersKey, daoRootKey] using hkey
  · intro id hid'
    have hkey := hvalid.1.2 id hid'
    rw [hfinal]
    simpa [bountyRawWrite, bountyCountKey, daoRootKey] using hkey

end SputnikDAO2
