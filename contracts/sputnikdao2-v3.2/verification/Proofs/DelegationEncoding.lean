import Model.DelegationEncoding
import Proofs.BountyEncoding
import Proofs.Delegation

namespace SputnikDAO2

private theorem delegation_u128_width : 256 ^ 16 = maxU128 + 1 := by
  decide

theorem delegation_key_injective (left right : String)
    (heq : delegationKey left = delegationKey right) :
    left = right := by
  have hsuffix : bountyBorshString left = bountyBorshString right := by
    simpa [delegationKey] using heq
  exact bounty_claimers_key_injective left right (by
    simpa [bountyClaimersKey] using hsuffix)

theorem delegation_key_disjoint_from_bounty_claimers
    (account other : String) :
    delegationKey account ≠ bountyClaimersKey other := by
  simp [delegationKey, bountyClaimersKey]

theorem delegation_key_disjoint_from_bounty_count
    (account : String) (bountyId : Nat) :
    delegationKey account ≠ bountyCountKey bountyId := by
  simp [delegationKey, bountyCountKey]

theorem parse_delegation_balance_encoded (amount : Nat)
    (hbound : amount < 256 ^ 16) :
    parseDelegationBalance (encodeDelegationBalance amount) =
      some amount := by
  have h := bounty_parse_nat_encoded 16 amount [] hbound
  simp only [List.append_nil] at h
  simp [parseDelegationBalance, encodeDelegationBalance, h]

theorem delegation_empty_valid_image :
    delegationRawImage delegationEmptyRaw delegationEmptyState ∧
      delegationSerializable delegationEmptyState ∧
      coherentDelegation delegationEmptyState := by
  constructor
  · intro account
    rfl
  · constructor
    · constructor
      · decide
      · intro _ _ hbalance
        simp [delegationEmptyState, balanceOf] at hbalance
    · rfl

theorem delegation_raw_read_decodes
    (raw : DelegationRawTrie) (state : DelegationState)
    (account : String)
    (himage : delegationRawImage raw state)
    (hserial : delegationSerializable state) :
    delegationRawBalanceOf raw account =
      (balanceOf state.balances account).getD 0 := by
  cases hbalance : balanceOf state.balances account with
  | none =>
      simp [delegationRawBalanceOf, himage account, hbalance]
  | some amount =>
      have hbound := hserial.2 account amount hbalance
      simp [delegationRawBalanceOf, himage account, hbalance,
        parse_delegation_balance_encoded amount hbound]

theorem balance_of_set_same (balances : List (String × Nat))
    (account : String) (amount : Nat) :
    balanceOf (setBalance balances account amount) account =
      some amount := by
  induction balances with
  | nil => simp [setBalance, balanceOf]
  | cons entry rest ih =>
      obtain ⟨user, previous⟩ := entry
      by_cases hsame : user = account
      · subst user
        simp [setBalance, balanceOf]
      · simp [setBalance, balanceOf, hsame, ih]

theorem balance_of_set_other (balances : List (String × Nat))
    (account query : String) (amount : Nat)
    (hother : query ≠ account) :
    balanceOf (setBalance balances account amount) query =
      balanceOf balances query := by
  have hne : account ≠ query := Ne.symm hother
  induction balances with
  | nil => simp [setBalance, balanceOf, hne]
  | cons entry rest ih =>
      obtain ⟨user, previous⟩ := entry
      by_cases hsame : user = account
      · subst user
        simp [setBalance, balanceOf, hne]
      · by_cases hquery : user = query
        · subst user
          simp [setBalance, balanceOf, hsame]
        · simp [setBalance, balanceOf, hsame, hquery, ih]

theorem delegation_raw_register_preserves_valid_image
    (raw : DelegationRawTrie)
    (state next : DelegationState)
    (caller account : String) (deposit byteCost : Nat)
    (himage : delegationRawImage raw state)
    (hserial : delegationSerializable state)
    (hstep : registerDelegation state caller account deposit byteCost =
      some next) :
    delegationRawImage (delegationRawRegister raw account) next ∧
      delegationSerializable next := by
  simp [registerDelegation] at hstep
  rcases hstep with ⟨_, hnext⟩
  subst next
  constructor
  · intro query
    by_cases hsame : query = account
    · subst query
      simp [delegationRawRegister, bountyRawWrite,
        balance_of_set_same]
    · have hkey : delegationKey query ≠ delegationKey account := by
        intro heq
        exact hsame (delegation_key_injective query account heq)
      simp [delegationRawRegister, bountyRawWrite, hkey,
        balance_of_set_other, hsame, himage query]
  · constructor
    · exact hserial.1
    · intro query amount hbalance
      by_cases hsame : query = account
      · subst query
        have heq : amount = 0 := by
          simpa [balance_of_set_same] using hbalance.symm
        subst amount
        decide
      · have horig : balanceOf state.balances query = some amount := by
          simpa [balance_of_set_other, hsame] using hbalance
        exact hserial.2 query amount horig

theorem delegation_raw_set_preserves_image
    (raw : DelegationRawTrie) (state next : DelegationState)
    (account : String) (newAmount : Nat)
    (himage : delegationRawImage raw state)
    (hbalances : next.balances =
      setBalance state.balances account newAmount) :
    delegationRawImage
      (delegationRawDelegate raw account newAmount) next := by
  intro query
  by_cases hsame : query = account
  · subst query
    simp [delegationRawDelegate, bountyRawWrite, hbalances,
      balance_of_set_same]
  · have hkey : delegationKey query ≠ delegationKey account := by
      intro heq
      exact hsame (delegation_key_injective query account heq)
    simp [delegationRawDelegate, bountyRawWrite, hbalances,
      balance_of_set_other, hsame, hkey, himage query]

theorem delegation_set_preserves_serializable
    (state next : DelegationState)
    (account : String) (newAmount : Nat)
    (hserial : delegationSerializable state)
    (hbalances : next.balances =
      setBalance state.balances account newAmount)
    (htotal : next.total < 256 ^ 16)
    (hnew : newAmount < 256 ^ 16) :
    delegationSerializable next := by
  constructor
  · exact htotal
  · intro query amount hbalance
    by_cases hsame : query = account
    · subst query
      have heq : amount = newAmount := by
        simpa [hbalances, balance_of_set_same] using hbalance.symm
      subst amount
      exact hnew
    · have horig : balanceOf state.balances query = some amount := by
        simpa [hbalances, balance_of_set_other, hsame]
          using hbalance
      exact hserial.2 query amount horig

theorem delegation_raw_delegate_preserves_valid_image
    (raw : DelegationRawTrie) (state next : DelegationState)
    (caller account : String) (amount previous : Nat)
    (himage : delegationRawImage raw state)
    (hserial : delegationSerializable state)
    (hcaller : state.stakingId = some caller)
    (hregistered : balanceOf state.balances account = some previous)
    (hbalance : previous + amount ≤ maxU128)
    (htotal : state.total + amount ≤ maxU128)
    (hstep : delegate state caller account amount = some next) :
    delegationRawImage
      (delegationRawDelegate raw account (previous + amount)) next ∧
      delegationSerializable next := by
  let exactNext : DelegationState :=
    { state with
      balances := setBalance state.balances account (previous + amount)
      total := state.total + amount }
  have hexact : delegate state caller account amount = some exactNext := by
    simp [delegate, hcaller, hregistered, Nat.not_lt.mpr hbalance,
      Nat.not_lt.mpr htotal, exactNext]
  rw [hstep] at hexact
  have heq : exactNext = next := (Option.some.inj hexact).symm
  subst next
  constructor
  · exact delegation_raw_set_preserves_image raw state exactNext
      account (previous + amount) himage rfl
  · apply delegation_set_preserves_serializable state exactNext
      account (previous + amount) hserial rfl
    · change state.total + amount < 256 ^ 16
      rw [delegation_u128_width]
      omega
    · change previous + amount < 256 ^ 16
      rw [delegation_u128_width]
      omega

theorem delegation_raw_undelegate_preserves_valid_image
    (raw : DelegationRawTrie) (state next : DelegationState)
    (caller account : String) (amount : Nat)
    (himage : delegationRawImage raw state)
    (hserial : delegationSerializable state)
    (hcaller : state.stakingId = some caller)
    (hbalance : amount ≤ (balanceOf state.balances account).getD 0)
    (htotal : amount ≤ state.total)
    (hstep : undelegate state caller account amount = some next) :
    let previous := (balanceOf state.balances account).getD 0
    delegationRawImage
      (delegationRawDelegate raw account (previous - amount)) next ∧
      delegationSerializable next := by
  let previous := (balanceOf state.balances account).getD 0
  let exactNext : DelegationState :=
    { state with
      balances := setBalance state.balances account (previous - amount)
      total := state.total - amount }
  have hexact : undelegate state caller account amount = some exactNext := by
    simp [undelegate, hcaller, Nat.not_lt.mpr hbalance,
      Nat.not_lt.mpr htotal, previous, exactNext]
  rw [hstep] at hexact
  have heq : exactNext = next := (Option.some.inj hexact).symm
  subst next
  have hprevious : previous < 256 ^ 16 := by
    cases hfound : balanceOf state.balances account with
    | none =>
        simp [previous, hfound]
    | some value =>
        simpa [previous, hfound] using hserial.2 account value hfound
  constructor
  · exact delegation_raw_set_preserves_image raw state exactNext
      account (previous - amount) himage rfl
  · apply delegation_set_preserves_serializable state exactNext
      account (previous - amount) hserial rfl
    · change state.total - amount < 256 ^ 16
      have htotalBound := hserial.1
      omega
    · change previous - amount < 256 ^ 16
      omega

-- Exact arrays checked by the native delegation oracle.
theorem delegation_borsh_oracle_vectors :
    delegationKey "alice.near" =
      [2, 10, 0, 0, 0, 97, 108, 105, 99, 101, 46, 110, 101, 97, 114] ∧
    delegationKey "bob.near" =
      [2, 8, 0, 0, 0, 98, 111, 98, 46, 110, 101, 97, 114] ∧
    encodeDelegationBalance 0 =
      [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    encodeDelegationBalance 258 =
      [2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] ∧
    encodeDelegationBalance 256 =
      [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] := by
  decide

end SputnikDAO2
