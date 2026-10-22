import Model.BountyGiveupExport
import Proofs.ExportWrapper
import Proofs.BountySerial

namespace SputnikDAO2

theorem bounty_giveup_export_requires_policy
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyStorageState) (bountyId now : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) :
    runBountyGiveupExport raw ctx state none bountyId now encodeRoot = none := by
  simp [runBountyGiveupExport]

theorem bounty_giveup_export_nonpayable
    (raw : BountyRawTrie) (ctx : CallWrapperContext)
    (state : Option BountyStorageState) (policy : Option (Nat × Nat))
    (bountyId now : Nat) (encodeRoot : BountyStorageState → BountyBytes)
    (hdeposit : ctx.attachedDeposit ≠ 0) :
    runBountyGiveupExport raw ctx state policy bountyId now encodeRoot = none := by
  cases state with
  | none => simp [runBountyGiveupExport]
  | some before =>
      cases policy with
      | none => simp [runBountyGiveupExport]
      | some pair =>
          obtain ⟨forgiveness, bond⟩ := pair
          cases hstep : giveupStoredClaim before ctx.predecessor bountyId
              now forgiveness bond with
          | none => simp [runBountyGiveupExport, hstep]
          | some result =>
              obtain ⟨after, refund⟩ := result
              cases hraw : bountyRawRemoveClaim raw before ctx.predecessor bountyId with
              | none => simp [runBountyGiveupExport, hstep, hraw]
              | some afterRaw =>
                  have hi : findDAOExport "bounty_giveup" =
                      some ⟨"bounty_giveup", .call, false, false⟩ := by decide
                  simp [runBountyGiveupExport,
                    runGeneratedCallWrapper, hi, hdeposit]

theorem giveup_stored_claim_rejects_time_underflow
    (state : BountyStorageState) (account : String)
    (bountyId now forgiveness bond : Nat)
    (removed : BountyStorageState) (claim : StoredBountyClaim)
    (hremove : removeStoredClaim state account bountyId =
      some (removed, claim)) (hbefore : now < claim.start) :
    giveupStoredClaim state account bountyId now forgiveness bond = none := by
  simp [giveupStoredClaim, hremove, hbefore]

theorem giveup_stored_claim_late_has_no_refund
    (state : BountyStorageState) (account : String)
    (bountyId now forgiveness bond : Nat)
    (removed : BountyStorageState) (claim : StoredBountyClaim)
    (hremove : removeStoredClaim state account bountyId =
      some (removed, claim))
    (hwidth : now ≤ maxU64 ∧ forgiveness ≤ maxU64 ∧ bond ≤ maxU128 ∧
      claim.start ≤ maxU64)
    (hstarted : claim.start ≤ now)
    (hlate : forgiveness < now - claim.start) :
    giveupStoredClaim state account bountyId now forgiveness bond =
      some (removed, none) := by
  simp [giveupStoredClaim, hremove, hwidth.1, hwidth.2.1,
    hwidth.2.2.1, hwidth.2.2.2, hstarted, hlate]

theorem giveup_stored_claim_refunds_current_bond
    (state : BountyStorageState) (account : String)
    (bountyId now forgiveness bond : Nat)
    (removed : BountyStorageState) (claim : StoredBountyClaim)
    (hremove : removeStoredClaim state account bountyId =
      some (removed, claim))
    (hwidth : now ≤ maxU64 ∧ forgiveness ≤ maxU64 ∧ bond ≤ maxU128 ∧
      claim.start ≤ maxU64)
    (hstarted : claim.start ≤ now)
    (hwithin : now - claim.start ≤ forgiveness) :
    giveupStoredClaim state account bountyId now forgiveness bond =
      some ({ removed with locked := removed.locked - bond }, some bond) := by
  simp [giveupStoredClaim, hremove, hwidth.1, hwidth.2.1,
    hwidth.2.2.1, hwidth.2.2.2, hstarted, hwithin]

theorem bounty_giveup_export_success_body
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyStorageState) (forgiveness bond bountyId now : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) (refund : Option Nat)
    (h : runBountyGiveupExport raw ctx (some state)
      (some (forgiveness, bond)) bountyId now encodeRoot =
      some (final, refund)) :
    ∃ after afterRaw,
      giveupStoredClaim state ctx.predecessor bountyId now
        forgiveness bond = some (after, refund) ∧
      bountyRawRemoveClaim raw state ctx.predecessor bountyId =
        some afterRaw ∧
      runGeneratedCallWrapper raw "bounty_giveup"
        { ctx with stateDecoded := true }
        (some (afterRaw, encodeRoot after)) = some final := by
  cases hstep : giveupStoredClaim state ctx.predecessor bountyId now
      forgiveness bond with
  | none => simp [runBountyGiveupExport, hstep] at h
  | some result =>
      obtain ⟨after, paid⟩ := result
      cases hraw : bountyRawRemoveClaim raw state ctx.predecessor bountyId with
      | none => simp [runBountyGiveupExport, hstep, hraw] at h
      | some afterRaw =>
          cases hw : runGeneratedCallWrapper raw "bounty_giveup"
              { ctx with stateDecoded := true }
              (some (afterRaw, encodeRoot after)) with
          | none => simp [runBountyGiveupExport, hstep, hraw, hw] at h
          | some actual =>
              simp [runBountyGiveupExport, hstep, hraw, hw] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨after, afterRaw, rfl, rfl, hw⟩

theorem bounty_giveup_export_success_root
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyStorageState) (forgiveness bond bountyId now : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) (refund : Option Nat)
    (h : runBountyGiveupExport raw ctx (some state)
      (some (forgiveness, bond)) bountyId now encodeRoot =
      some (final, refund)) :
    ∃ after,
      giveupStoredClaim state ctx.predecessor bountyId now
        forgiveness bond = some (after, refund) ∧
      final daoRootKey = some (encodeRoot after) := by
  obtain ⟨after, afterRaw, hstep, _, hw⟩ :=
    bounty_giveup_export_success_body raw final ctx state forgiveness
      bond bountyId now encodeRoot refund h
  have hfinal := generated_call_success_is_root_write raw afterRaw final
    "bounty_giveup" { ctx with stateDecoded := true }
    (encodeRoot after) hw
  exact ⟨after, hstep, by simp [hfinal, bountyRawWrite]⟩

theorem bounty_giveup_remove_preserves_valid_image
    (raw afterRaw : BountyRawTrie) (state removed : BountyStorageState)
    (account : String) (bountyId : Nat) (claim : StoredBountyClaim)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state)
    (hremove : removeStoredClaim state account bountyId =
      some (removed, claim))
    (hraw : bountyRawRemoveClaim raw state account bountyId =
      some afterRaw) :
    bountyRawImage afterRaw removed ∧
      bountyStorageSerializable removed := by
  cases hclaims : state.claimers account with
  | none => simp [removeStoredClaim, hclaims] at hremove
  | some claims =>
      cases hfind : removeFirstBountyClaim claims bountyId with
      | none => simp [removeStoredClaim, hclaims, hfind] at hremove
      | some pair =>
          obtain ⟨found, remaining⟩ := pair
          cases hcount : state.counts bountyId with
          | none => simp [removeStoredClaim, hclaims, hfind, hcount] at hremove
          | some count =>
              have hpositive : 0 < count := by
                cases count with
                | zero =>
                    simp [removeStoredClaim, hclaims, hfind, hcount] at hremove
                | succ n => exact Nat.zero_lt_succ n
              obtain ⟨next, nextRaw, hnext, hnextRaw,
                himageNext, hserialNext⟩ :=
                bounty_raw_remove_claim_preserves_valid_image raw state
                  account bountyId count claims remaining found hid himage
                  hserial hclaims hfind hcount hpositive
              rw [hremove] at hnext
              have heq := Option.some.inj hnext
              have hstate : next = removed := (Prod.mk.inj heq).1.symm
              rw [hraw] at hnextRaw
              have htrie : nextRaw = afterRaw :=
                (Option.some.inj hnextRaw).symm
              subst next
              subst nextRaw
              exact ⟨himageNext, hserialNext⟩

theorem giveup_stored_claim_success_shape
    (state after : BountyStorageState) (account : String)
    (bountyId now forgiveness bond : Nat) (refund : Option Nat)
    (hstep : giveupStoredClaim state account bountyId now
      forgiveness bond = some (after, refund)) :
    ∃ removed claim,
      removeStoredClaim state account bountyId = some (removed, claim) ∧
      (after = removed ∨
        after = { removed with locked := removed.locked - bond }) := by
  cases hremove : removeStoredClaim state account bountyId with
  | none => simp [giveupStoredClaim, hremove] at hstep
  | some pair =>
      obtain ⟨removed, claim⟩ := pair
      refine ⟨removed, claim, rfl, ?_⟩
      unfold giveupStoredClaim at hstep
      split at hstep
      · contradiction
      · simp [hremove] at hstep
        all_goals
          rcases hstep with ⟨_, heq⟩
          split at heq
          · exact Or.inl (Prod.mk.inj (Option.some.inj heq)).1.symm
          · exact Or.inr (Prod.mk.inj (Option.some.inj heq)).1.symm

theorem bounty_giveup_export_preserves_valid_image
    (raw final : BountyRawTrie) (ctx : CallWrapperContext)
    (state : BountyStorageState) (forgiveness bond bountyId now : Nat)
    (encodeRoot : BountyStorageState → BountyBytes) (refund : Option Nat)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state)
    (h : runBountyGiveupExport raw ctx (some state)
      (some (forgiveness, bond)) bountyId now encodeRoot =
      some (final, refund)) :
    ∃ after,
      giveupStoredClaim state ctx.predecessor bountyId now
        forgiveness bond = some (after, refund) ∧
      bountyRawImage final after ∧ bountyStorageSerializable after := by
  obtain ⟨after, afterRaw, hstep, hraw, hw⟩ :=
    bounty_giveup_export_success_body raw final ctx state forgiveness
      bond bountyId now encodeRoot refund h
  obtain ⟨removed, claim, hremove, hshape⟩ :=
    giveup_stored_claim_success_shape state after ctx.predecessor
      bountyId now forgiveness bond refund hstep
  have hvalidRemoved := bounty_giveup_remove_preserves_valid_image
    raw afterRaw state removed ctx.predecessor bountyId claim
    hid himage hserial hremove hraw
  have hvalidAfter : bountyRawImage afterRaw after ∧
      bountyStorageSerializable after := by
    cases hshape with
    | inl heq =>
        subst after
        exact hvalidRemoved
    | inr heq =>
        subst after
        simpa [bountyRawImage, bountyStorageSerializable] using
          hvalidRemoved
  have hfinal := generated_call_success_is_root_write raw afterRaw final
    "bounty_giveup" { ctx with stateDecoded := true }
    (encodeRoot after) hw
  refine ⟨after, hstep, ?_, hvalidAfter.2⟩
  constructor
  · intro account
    have hkey := hvalidAfter.1.1 account
    rw [hfinal]
    simpa [bountyRawWrite, bountyClaimersKey, daoRootKey] using hkey
  · intro id hid'
    have hkey := hvalidAfter.1.2 id hid'
    rw [hfinal]
    simpa [bountyRawWrite, bountyCountKey, daoRootKey] using hkey

end SputnikDAO2
