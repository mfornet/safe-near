import Model.BountyTrace
import Proofs.BountySerial

namespace SputnikDAO2

theorem bounty_trie_step_preserves_valid_image
    (account : String) (raw nextRaw : BountyRawTrie)
    (state next : BountyStorageState)
    (hvalid : bountyRawImage raw state ∧
      bountyStorageSerializable state)
    (hstep : BountyTrieStep account raw state nextRaw next) :
    bountyRawImage nextRaw next ∧ bountyStorageSerializable next := by
  cases hstep with
  | add =>
      rename_i bountyId now deadline maxDeadline times bond hid hlogical
      exact bounty_raw_add_claim_preserves_valid_image raw state next
        account bountyId now deadline maxDeadline times bond hid
        hvalid.1 hvalid.2 hlogical
  | remove =>
      rename_i bountyId count claims remaining found hid hfind
        hpositive hcount hclaims hraw hlogical
      obtain ⟨next', nextRaw', hlogical', hraw', himage', hserial'⟩ :=
        bounty_raw_remove_claim_preserves_valid_image raw state account
          bountyId count claims remaining found hid hvalid.1 hvalid.2
          hclaims hfind hcount hpositive
      rw [hlogical] at hlogical'
      have hnext : next' = next := by
        injection hlogical' with hpair
        exact (Prod.mk.inj hpair).1.symm
      rw [hraw] at hraw'
      have hnextRaw : nextRaw' = nextRaw := (Option.some.inj hraw').symm
      subst next'
      subst nextRaw'
      exact ⟨himage', hserial'⟩
  | complete =>
      rename_i bountyId claims completed hcomplete hclaims hraw hlogical
      obtain ⟨next', nextRaw', hlogical', hraw', himage', hserial'⟩ :=
        bounty_raw_complete_claim_preserves_valid_image raw state account
          bountyId claims completed hvalid.1 hvalid.2 hclaims hcomplete
      rw [hlogical] at hlogical'
      have hnext : next' = next := (Option.some.inj hlogical').symm
      rw [hraw] at hraw'
      have hnextRaw : nextRaw' = nextRaw := (Option.some.inj hraw').symm
      subst next'
      subst nextRaw'
      exact ⟨himage', hserial'⟩

theorem bounty_trie_reachable_valid_image
    (raw : BountyRawTrie) (state : BountyStorageState)
    (hreach : BountyTrieReachable raw state) :
    bountyRawImage raw state ∧ bountyStorageSerializable state := by
  induction hreach with
  | empty => exact bounty_empty_valid_image
  | advance prior step ih =>
      exact bounty_trie_step_preserves_valid_image _ _ _ _ _ ih step

theorem bounty_trie_reachable_claimers_decode
    (raw : BountyRawTrie) (state : BountyStorageState)
    (account : String) (hreach : BountyTrieReachable raw state) :
    (raw (bountyClaimersKey account)).bind bountyParseClaims =
      (state.claimers account).map
        (fun claims => claims.map physicalBountyClaim) := by
  obtain ⟨himage, hserial⟩ :=
    bounty_trie_reachable_valid_image raw state hreach
  exact bounty_raw_claimers_read_serializable raw state account
    himage hserial

theorem bounty_trie_reachable_count_decode
    (raw : BountyRawTrie) (state : BountyStorageState)
    (bountyId : Nat) (hid : bountyId < 256 ^ 8)
    (hreach : BountyTrieReachable raw state) :
    (raw (bountyCountKey bountyId)).bind bountyParseCount =
      state.counts bountyId := by
  obtain ⟨himage, hserial⟩ :=
    bounty_trie_reachable_valid_image raw state hreach
  exact bounty_raw_count_read_serializable raw state bountyId hid
    himage hserial

-- The first matching claim blocks a later unfinished duplicate. The source
-- checks `completed` on the first index returned by `position`.
theorem completed_first_duplicate_blocks_completion :
    let old : StoredBountyClaim := ⟨7, 1, 10, true, 5⟩
    let fresh : StoredBountyClaim := ⟨7, 2, 10, false, 5⟩
    completeFirstBountyClaim [old, fresh] 7 = none := by
  decide

theorem one_claim_reachable :
    ∃ raw state, BountyTrieReachable raw state ∧
      state.counts 7 = some 1 ∧
      state.claimers "alice.near" =
        some [⟨7, 1, 10, false, 5⟩] := by
  let next : BountyStorageState := {
    claimers := fun key => if key == "alice.near" then
      some [⟨7, 1, 10, false, 5⟩] else none
    counts := fun key => if key == 7 then some 1 else none
    locked := 5 }
  have hstep : addStoredClaim bountyEmptyState "alice.near"
      7 1 10 20 2 5 5 = some next := by
    rfl
  refine ⟨bountyRawAddClaim bountyEmptyRaw bountyEmptyState
    "alice.near" 7 1 10 5, next, ?_, ?_, ?_⟩
  · exact BountyTrieReachable.advance BountyTrieReachable.empty
      (BountyTrieStep.add bountyEmptyRaw bountyEmptyState next
        "alice.near" 7 1 10 20 2 5 (by decide) hstep)
  · rfl
  · rfl

theorem bounty_coherence_permute_accounts
    (state : BountyStorageState) (left right : List String)
    (hperm : left.Perm right)
    (hcoherent : coherentAllBountyCounts state left) :
    coherentAllBountyCounts state right := by
  intro bountyId
  have hsum : observedBountyCount state left bountyId =
      observedBountyCount state right bountyId := by
    exact (hperm.map (fun account =>
      accountClaimCount ((state.claimers account).getD []) bountyId)).sum_nat
  have hc := hcoherent bountyId
  dsimp [coherentBountyCount] at hc ⊢
  rw [← hsum]
  exact hc

theorem bounty_add_preserves_coherence_in_nodup_accounts
    (state next : BountyStorageState)
    (account : String) (accounts : List String)
    (bountyId now deadline maxDeadline times bond : Nat)
    (hnodup : accounts.Nodup) (hmem : account ∈ accounts)
    (hcoherent : coherentAllBountyCounts state accounts)
    (hstep : addStoredClaim state account bountyId now deadline
      maxDeadline times bond bond = some next) :
    coherentAllBountyCounts next accounts := by
  let others := accounts.erase account
  have hperm : accounts.Perm (account :: others) :=
    List.perm_cons_erase hmem
  have hnot : account ∉ others := hnodup.not_mem_erase
  have hbefore := bounty_coherence_permute_accounts state accounts
    (account :: others) hperm hcoherent
  have hafter := add_stored_claim_preserves_all_enumerated_coherence
    state next account others bountyId now deadline maxDeadline times
    bond hnot hbefore hstep
  exact bounty_coherence_permute_accounts next (account :: others)
    accounts hperm.symm hafter

theorem bounty_remove_preserves_coherence_in_nodup_accounts
    (state next : BountyStorageState)
    (account : String) (accounts : List String)
    (bountyId count : Nat)
    (claims remaining : List StoredBountyClaim)
    (found : StoredBountyClaim)
    (hnodup : accounts.Nodup) (hmem : account ∈ accounts)
    (hclaims : state.claimers account = some claims)
    (hfind : removeFirstBountyClaim claims bountyId =
      some (found, remaining))
    (hcount : state.counts bountyId = some count)
    (hpositive : 0 < count)
    (hcoherent : coherentAllBountyCounts state accounts)
    (hstep : removeStoredClaim state account bountyId = some (next, found)) :
    coherentAllBountyCounts next accounts := by
  let others := accounts.erase account
  have hperm : accounts.Perm (account :: others) :=
    List.perm_cons_erase hmem
  have hnot : account ∉ others := hnodup.not_mem_erase
  have hbefore := bounty_coherence_permute_accounts state accounts
    (account :: others) hperm hcoherent
  obtain ⟨next', hstep', hafter⟩ :=
    remove_stored_claim_preserves_all_enumerated_coherence state
      account others bountyId count claims remaining found hnot
      hclaims hfind hcount hpositive hbefore
  rw [hstep] at hstep'
  have heq : next' = next := by
    injection hstep' with hpair
    exact (Prod.mk.inj hpair).1.symm
  subst next'
  exact bounty_coherence_permute_accounts next (account :: others)
    accounts hperm.symm hafter

theorem bounty_trie_step_preserves_covered_coherence
    (account : String) (accounts : List String)
    (raw nextRaw : BountyRawTrie)
    (state next : BountyStorageState)
    (hnodup : accounts.Nodup) (hmem : account ∈ accounts)
    (hcoherent : coherentAllBountyCounts state accounts)
    (hstep : BountyTrieStep account raw state nextRaw next) :
    coherentAllBountyCounts next accounts := by
  cases hstep with
  | add =>
      rename_i bountyId now deadline maxDeadline times bond hid hlogical
      exact bounty_add_preserves_coherence_in_nodup_accounts state next
        account accounts bountyId now deadline maxDeadline times bond
        hnodup hmem hcoherent hlogical
  | remove =>
      rename_i bountyId count claims remaining found hid hfind
        hpositive hcount hclaims hraw hlogical
      exact bounty_remove_preserves_coherence_in_nodup_accounts
        state next account accounts bountyId count claims remaining
        found hnodup hmem hclaims hfind hcount hpositive hcoherent
        hlogical
  | complete =>
      rename_i bountyId claims completed hcomplete hclaims hraw hlogical
      exact bounty_complete_preserves_all_coherence state next account
        bountyId accounts hcoherent hlogical

theorem bounty_covered_trace_invariants
    (accounts : List String) (raw : BountyRawTrie)
    (state : BountyStorageState)
    (hnodup : accounts.Nodup)
    (hreach : BountyTrieCoveredReachable accounts raw state) :
    bountyRawImage raw state ∧
      bountyStorageSerializable state ∧
      coherentAllBountyCounts state accounts := by
  induction hreach with
  | empty =>
      exact ⟨bounty_empty_valid_image.1,
        bounty_empty_valid_image.2,
        bounty_empty_counts_coherent accounts⟩
  | advance prior step hmem ih =>
      have hvalid := bounty_trie_step_preserves_valid_image
        _ _ _ _ _ ⟨ih.1, ih.2.1⟩ step
      have hcoherent := bounty_trie_step_preserves_covered_coherence
        _ accounts _ _ _ _ hnodup hmem ih.2.2 step
      exact ⟨hvalid.1, hvalid.2, hcoherent⟩

theorem bounty_trie_step_preserves_account_support
    (account : String) (accounts : List String)
    (raw nextRaw : BountyRawTrie)
    (state next : BountyStorageState)
    (hmem : account ∈ accounts)
    (hsupport : bountyAccountSupport state accounts)
    (hstep : BountyTrieStep account raw state nextRaw next) :
    bountyAccountSupport next accounts := by
  intro query houtside
  have hother : query ≠ account := by
    intro heq
    subst query
    exact houtside hmem
  cases hstep with
  | add =>
      rename_i bountyId now deadline maxDeadline times bond hid hlogical
      simp [addStoredClaim] at hlogical
      split at hlogical
      · contradiction
      · split at hlogical
        · contradiction
        · simp at hlogical
          subst next
          simpa [hother] using hsupport query houtside
  | remove =>
      rename_i bountyId count claims remaining found hid hfind
        hpositive hcount hclaims hraw hlogical
      have hkeys := remove_stored_claim_preserves_other_keys state next
        account query bountyId (bountyId + 1) found hlogical hother
        (by omega)
      rw [hkeys.1]
      exact hsupport query houtside
  | complete =>
      rename_i bountyId claims completed hcomplete hclaims hraw hlogical
      simp [completeStoredClaim, hclaims, hcomplete] at hlogical
      subst next
      simpa [hother] using hsupport query houtside

theorem bounty_covered_trace_account_support
    (accounts : List String) (raw : BountyRawTrie)
    (state : BountyStorageState)
    (hreach : BountyTrieCoveredReachable accounts raw state) :
    bountyAccountSupport state accounts := by
  induction hreach with
  | empty =>
      intro account _
      rfl
  | advance prior step hmem ih =>
      exact bounty_trie_step_preserves_account_support
        _ accounts _ _ _ _ hmem ih step

theorem bounty_covered_trace_reachable
    (accounts : List String) (raw : BountyRawTrie)
    (state : BountyStorageState)
    (hreach : BountyTrieCoveredReachable accounts raw state) :
    BountyTrieReachable raw state := by
  induction hreach with
  | empty => exact BountyTrieReachable.empty
  | advance prior step hmem ih =>
      exact BountyTrieReachable.advance ih step

theorem bounty_covered_trace_raw_account_support
    (accounts : List String) (raw : BountyRawTrie)
    (state : BountyStorageState)
    (hreach : BountyTrieCoveredReachable accounts raw state)
    (account : String) (houtside : account ∉ accounts) :
    raw (bountyClaimersKey account) = none := by
  have himage := (bounty_trie_reachable_valid_image raw state
    (bounty_covered_trace_reachable accounts raw state hreach)).1
  have hsupport := bounty_covered_trace_account_support accounts
    raw state hreach
  rw [himage.1 account, hsupport account houtside]
  rfl

end SputnikDAO2
