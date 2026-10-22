import Model.BountyTrie
import Proofs.BountyStorage
import Proofs.BountyTrie

namespace SputnikDAO2

private theorem bounty_u32_width : 256 ^ 4 = maxU32 + 1 := by
  decide

private theorem bounty_u64_width : 256 ^ 8 = maxU64 + 1 := by
  decide

theorem bounty_empty_valid_image :
    bountyRawImage bountyEmptyRaw bountyEmptyState ∧
      bountyStorageSerializable bountyEmptyState := by
  constructor
  · constructor
    · intro account
      rfl
    · intro bountyId _
      rfl
  · constructor
    · intro _ _ hclaims
      simp [bountyEmptyState] at hclaims
    · intro _ _ hcount
      simp [bountyEmptyState] at hcount

theorem bounty_empty_counts_coherent (accounts : List String) :
    coherentAllBountyCounts bountyEmptyState accounts := by
  intro bountyId
  induction accounts with
  | nil => simp [coherentBountyCount, observedBountyCount,
      accountClaimCount, bountyEmptyState]
  | cons account rest ih =>
      simpa [coherentBountyCount, observedBountyCount,
        accountClaimCount, bountyEmptyState] using ih

theorem complete_first_bounty_claim_preserves_serializable
    (claims completed : List StoredBountyClaim) (bountyId : Nat)
    (hstep : completeFirstBountyClaim claims bountyId = some completed)
    (hvalid : ∀ claim ∈ claims, validStoredBountyClaim claim) :
    completed.length = claims.length ∧
      ∀ claim ∈ completed, validStoredBountyClaim claim := by
  induction claims generalizing completed with
  | nil => simp [completeFirstBountyClaim] at hstep
  | cons head tail ih =>
      have hhead := hvalid head (by simp)
      have htail : ∀ claim ∈ tail, validStoredBountyClaim claim := by
        intro claim hmem
        exact hvalid claim (List.mem_cons_of_mem _ hmem)
      by_cases hmatch : head.bountyId = bountyId
      · by_cases hdone : head.completed
        · simp [completeFirstBountyClaim, hmatch, hdone] at hstep
        · simp [completeFirstBountyClaim, hmatch, hdone] at hstep
          subst completed
          constructor
          · rfl
          · intro claim hmem
            simp at hmem
            rcases hmem with hnew | hold
            · subst claim
              simpa [validStoredBountyClaim, hmatch] using hhead
            · exact htail claim hold
      · cases hrec : completeFirstBountyClaim tail bountyId with
        | none =>
            simp [completeFirstBountyClaim, hmatch, hrec] at hstep
        | some rest =>
            simp [completeFirstBountyClaim, hmatch, hrec] at hstep
            subst completed
            obtain ⟨hlen, hrest⟩ := ih rest hrec htail
            constructor
            · simp [hlen]
            · intro claim hmem
              simp at hmem
              rcases hmem with hfirst | hrestmem
              · subst claim
                exact hhead
              · exact hrest claim hrestmem

theorem complete_first_bounty_claim_preserves_counts
    (claims completed : List StoredBountyClaim)
    (bountyId query : Nat)
    (hstep : completeFirstBountyClaim claims bountyId = some completed) :
    accountClaimCount completed query =
      accountClaimCount claims query := by
  induction claims generalizing completed with
  | nil => simp [completeFirstBountyClaim] at hstep
  | cons head tail ih =>
      by_cases hmatch : head.bountyId = bountyId
      · by_cases hdone : head.completed
        · simp [completeFirstBountyClaim, hmatch, hdone] at hstep
        · simp [completeFirstBountyClaim, hmatch, hdone] at hstep
          subst completed
          by_cases hq : bountyId = query <;>
            simp [accountClaimCount, hmatch, hq]
      · cases hrec : completeFirstBountyClaim tail bountyId with
        | none =>
            simp [completeFirstBountyClaim, hmatch, hrec] at hstep
        | some rest =>
            simp [completeFirstBountyClaim, hmatch, hrec] at hstep
            subst completed
            have hcount := ih rest hrec
            by_cases hq : head.bountyId = query
            · simp [accountClaimCount, hq]
              simpa [accountClaimCount] using hcount
            · simpa [accountClaimCount, hq]
                using hcount

theorem bounty_raw_complete_claim_preserves_valid_image
    (raw : BountyRawTrie) (state : BountyStorageState)
    (account : String) (bountyId : Nat)
    (claims completed : List StoredBountyClaim)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state)
    (hclaims : state.claimers account = some claims)
    (hcomplete : completeFirstBountyClaim claims bountyId =
      some completed) :
    ∃ next nextRaw,
      completeStoredClaim state account bountyId = some next ∧
      bountyRawCompleteClaim raw state account bountyId = some nextRaw ∧
      bountyRawImage nextRaw next ∧ bountyStorageSerializable next := by
  let next : BountyStorageState := { state with
    claimers := fun key => if key == account then some completed
      else state.claimers key }
  let nextRaw : BountyRawTrie := bountyRawWrite raw
    (bountyClaimersKey account) (encodeStoredBountyClaims completed)
  have hlist := complete_first_bounty_claim_preserves_serializable
    claims completed bountyId hcomplete (hserial.1 account claims hclaims).2
  refine ⟨next, nextRaw, ?_, ?_, ?_, ?_⟩
  · simp [completeStoredClaim, hclaims, hcomplete, next]
  · simp [bountyRawCompleteClaim, hclaims, hcomplete, nextRaw]
  · constructor
    · intro query
      by_cases hsame : query = account
      · subst query
        simp [next, nextRaw, bountyRawWrite]
      · have hkey : bountyClaimersKey query ≠
            bountyClaimersKey account := by
          intro heq
          exact hsame (bounty_claimers_key_injective query account heq)
        simp [next, nextRaw, bountyRawWrite, hsame, hkey,
          himage.1 query]
    · intro query hquery
      have hcross : bountyCountKey query ≠
          bountyClaimersKey account :=
        Ne.symm (bounty_claimers_and_count_keys_disjoint account query)
      simpa [next, nextRaw, bountyRawWrite, hcross]
        using himage.2 query hquery
  · constructor
    · intro query entries hentries
      by_cases hsame : query = account
      · subst query
        have heq : entries = completed := by
          simpa [next] using hentries.symm
        subst entries
        exact ⟨by rw [hlist.1]; exact (hserial.1 account claims hclaims).1,
          hlist.2⟩
      · have horig : state.claimers query = some entries := by
          simpa [next, hsame] using hentries
        exact hserial.1 query entries horig
    · intro query value hvalue
      exact hserial.2 query value (by simpa [next] using hvalue)

theorem bounty_complete_observed_count_unchanged
    (state : BountyStorageState) (account : String)
    (completed : List StoredBountyClaim) (accounts : List String)
    (query : Nat)
    (hlocal : accountClaimCount completed query =
      accountClaimCount ((state.claimers account).getD []) query) :
    observedBountyCount
      { state with claimers := fun key =>
          if key == account then some completed else state.claimers key }
      accounts query = observedBountyCount state accounts query := by
  induction accounts with
  | nil => rfl
  | cons head tail ih =>
      simp only [observedBountyCount, List.map_cons, List.sum_cons]
      by_cases hsame : head = account
      · subst head
        simp [hlocal]
        simpa [observedBountyCount] using ih
      · simp [hsame]
        simpa [observedBountyCount] using ih

theorem bounty_complete_preserves_all_coherence
    (state next : BountyStorageState)
    (account : String) (bountyId : Nat) (accounts : List String)
    (hcoherent : coherentAllBountyCounts state accounts)
    (hstep : completeStoredClaim state account bountyId = some next) :
    coherentAllBountyCounts next accounts := by
  cases hclaims : state.claimers account with
  | none => simp [completeStoredClaim, hclaims] at hstep
  | some claims =>
      cases hcomplete : completeFirstBountyClaim claims bountyId with
      | none =>
          simp [completeStoredClaim, hclaims, hcomplete] at hstep
      | some completed =>
          simp [completeStoredClaim, hclaims, hcomplete] at hstep
          subst next
          intro query
          have hlocal := complete_first_bounty_claim_preserves_counts
            claims completed bountyId query hcomplete
          have hobs := bounty_complete_observed_count_unchanged
            state account completed accounts query (by
              simpa [hclaims] using hlocal)
          have hc := hcoherent query
          dsimp [coherentBountyCount] at hc ⊢
          simp only [beq_iff_eq] at hobs
          rw [hobs]
          exact hc

theorem bounty_storage_serializable_add
    (state next : BountyStorageState) (account : String)
    (bountyId now deadline maxDeadline times bond : Nat)
    (hserial : bountyStorageSerializable state)
    (hid : bountyId < 256 ^ 8)
    (hnow : now < 256 ^ 8)
    (hdeadline : deadline < 256 ^ 8)
    (htimes : times ≤ maxU32)
    (hcapacity : (state.counts bountyId).getD 0 < times)
    (hlength : ((state.claimers account).getD []).length < maxU32)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    bountyStorageSerializable next := by
  simp [addStoredClaim] at hstep
  split at hstep
  · contradiction
  · split at hstep
    · contradiction
    · simp at hstep
      subst next
      constructor
      · intro query entries hentries
        by_cases hsame : query = account
        · subst query
          have heq : entries = (state.claimers account).getD [] ++
              [⟨bountyId, now, deadline, false, bond⟩] := by
            simpa using hentries.symm
          subst entries
          constructor
          · simp only [List.length_append, List.length_singleton]
            rw [bounty_u32_width]
            omega
          · intro claim hmem
            simp only [List.mem_append, List.mem_singleton] at hmem
            rcases hmem with hold | hnew
            · cases hclaims : state.claimers account with
              | none => simp [hclaims] at hold
              | some oldClaims =>
                  exact (hserial.1 account oldClaims hclaims).2 claim
                    (by simpa [hclaims] using hold)
            · subst claim
              exact ⟨hid, hnow, hdeadline⟩
        · have horig : state.claimers query = some entries := by
            simpa [hsame] using hentries
          exact hserial.1 query entries horig
      · intro query value hvalue
        by_cases hsame : query = bountyId
        · subst query
          have heq : value = (state.counts bountyId).getD 0 + 1 := by
            simpa using hvalue.symm
          subst value
          rw [bounty_u32_width]
          omega
        · have horig : state.counts query = some value := by
            simpa [hsame] using hvalue
          exact hserial.2 query value horig

theorem bounty_storage_serializable_add_success
    (state next : BountyStorageState) (account : String)
    (bountyId now deadline maxDeadline times bond : Nat)
    (hserial : bountyStorageSerializable state)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    bountyStorageSerializable next := by
  have hid : bountyId < 256 ^ 8 := by
    rw [bounty_u64_width]
    by_cases hbad : maxU64 < bountyId
    · simp [addStoredClaim, hbad] at hstep
    · omega
  have hnow : now < 256 ^ 8 := by
    rw [bounty_u64_width]
    by_cases hbad : maxU64 < now
    · simp [addStoredClaim, hbad] at hstep
    · omega
  have hdeadline : deadline < 256 ^ 8 := by
    rw [bounty_u64_width]
    by_cases hbad : maxU64 < deadline
    · simp [addStoredClaim, hbad] at hstep
    · omega
  have htimes : times ≤ maxU32 := by
    by_cases hbad : maxU32 < times
    · simp [addStoredClaim, hbad] at hstep
    · omega
  have hcapacity : (state.counts bountyId).getD 0 < times := by
    by_cases hbad : times ≤ (state.counts bountyId).getD 0
    · simp [addStoredClaim, hbad] at hstep
    · omega
  have hlength : ((state.claimers account).getD []).length < maxU32 := by
    by_cases hbad : maxU32 ≤ ((state.claimers account).getD []).length
    · simp [addStoredClaim, hbad] at hstep
    · omega
  exact bounty_storage_serializable_add state next account bountyId now
    deadline maxDeadline times bond hserial hid hnow hdeadline htimes
    hcapacity hlength hstep

theorem remove_first_bounty_claim_remaining_mem
    (claims remaining : List StoredBountyClaim)
    (bountyId : Nat) (found claim : StoredBountyClaim)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hmem : claim ∈ remaining) : claim ∈ claims := by
  induction claims generalizing found remaining with
  | nil => simp [removeFirstBountyClaim] at hfind
  | cons head tail ih =>
      by_cases hmatch : head.bountyId = bountyId
      · simp [removeFirstBountyClaim, hmatch] at hfind
        rcases hfind with ⟨_, hremaining⟩
        subst remaining
        simp [hmem]
      · cases hrec : removeFirstBountyClaim tail bountyId with
        | none => simp [removeFirstBountyClaim, hmatch, hrec] at hfind
        | some pair =>
            rcases pair with ⟨first, rest⟩
            simp [removeFirstBountyClaim, hmatch, hrec] at hfind
            rcases hfind with ⟨hfound, hremaining⟩
            subst found
            subst remaining
            simp at hmem
            rcases hmem with heq | htail
            · simp [heq]
            · exact List.mem_cons_of_mem _ (ih rest first hrec htail)

theorem bounty_storage_serializable_remove
    (state : BountyStorageState) (account : String)
    (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hserial : bountyStorageSerializable state)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count) :
    ∃ next, removeStoredClaim state account bountyId = some (next, found) ∧
      bountyStorageSerializable next := by
  let next : BountyStorageState := {
    claimers := fun key => if key == account then
      if remaining.isEmpty then none else some remaining
      else state.claimers key
    counts := fun key => if key == bountyId then some (count - 1)
      else state.counts key
    locked := state.locked }
  refine ⟨next,
    remove_stored_claim_exact state account bountyId count claims
      remaining found hclaims hfind hcount hpositive, ?_⟩
  constructor
  · intro query entries hentries
    by_cases hsame : query = account
    · subst query
      by_cases hempty : remaining.isEmpty
      · simp [next, hempty] at hentries
      · have heq : entries = remaining := by
          simpa [next, hempty] using hentries.symm
        subst entries
        obtain ⟨hlen, hvalid⟩ := hserial.1 account claims hclaims
        constructor
        · have hlength := remove_first_bounty_claim_length claims
            bountyId found remaining hfind
          omega
        · intro claim hmem
          exact hvalid claim (remove_first_bounty_claim_remaining_mem
            claims remaining bountyId found claim hfind hmem)
    · have hsame' : query ≠ account := hsame
      have horig : state.claimers query = some entries := by
        simpa [next, hsame'] using hentries
      exact hserial.1 query entries horig
  · intro query value hvalue
    by_cases hsame : query = bountyId
    · subst query
      have heq : value = count - 1 := by
        simpa [next] using hvalue.symm
      subst value
      have hbound := hserial.2 bountyId count hcount
      omega
    · have horig : state.counts query = some value := by
        simpa [next, hsame] using hvalue
      exact hserial.2 query value horig

theorem bounty_raw_claimers_read_serializable
    (raw : BountyRawTrie) (state : BountyStorageState)
    (account : String)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state) :
    (raw (bountyClaimersKey account)).bind bountyParseClaims =
      (state.claimers account).map
        (fun claims => claims.map physicalBountyClaim) :=
  bounty_raw_claimers_read_decodes raw state account himage
    (hserial.1 account)

theorem bounty_raw_count_read_serializable
    (raw : BountyRawTrie) (state : BountyStorageState)
    (bountyId : Nat) (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state) :
    (raw (bountyCountKey bountyId)).bind bountyParseCount =
      state.counts bountyId :=
  bounty_raw_count_read_decodes raw state bountyId hid himage
    (hserial.2 bountyId)

theorem bounty_raw_add_claim_preserves_valid_image
    (raw : BountyRawTrie) (state next : BountyStorageState)
    (account : String)
    (bountyId now deadline maxDeadline times bond : Nat)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    bountyRawImage
      (bountyRawAddClaim raw state account bountyId now deadline bond)
      next ∧ bountyStorageSerializable next := by
  exact ⟨bounty_raw_add_claim_preserves_image raw state next account
    bountyId now deadline maxDeadline times bond hid himage hstep,
    bounty_storage_serializable_add_success state next account bountyId
      now deadline maxDeadline times bond hserial hstep⟩

theorem bounty_raw_remove_claim_preserves_valid_image
    (raw : BountyRawTrie) (state : BountyStorageState)
    (account : String) (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hid : bountyId < 256 ^ 8)
    (himage : bountyRawImage raw state)
    (hserial : bountyStorageSerializable state)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count) :
    ∃ next nextRaw,
      removeStoredClaim state account bountyId = some (next, found) ∧
      bountyRawRemoveClaim raw state account bountyId = some nextRaw ∧
      bountyRawImage nextRaw next ∧ bountyStorageSerializable next := by
  obtain ⟨next, nextRaw, hstep, hraw, himageNext⟩ :=
    bounty_raw_remove_claim_preserves_image raw state account bountyId
      count claims remaining found hid himage hclaims hfind hcount
      hpositive
  obtain ⟨nextSerial, hstepSerial, hserialNext⟩ :=
    bounty_storage_serializable_remove state account bountyId count
      claims remaining found hserial hclaims hfind hcount hpositive
  rw [hstep] at hstepSerial
  have heq : nextSerial = next := by
    injection hstepSerial with hpair
    exact (Prod.mk.inj hpair).1.symm
  subst nextSerial
  exact ⟨next, nextRaw, hstep, hraw, himageNext, hserialNext⟩

end SputnikDAO2
