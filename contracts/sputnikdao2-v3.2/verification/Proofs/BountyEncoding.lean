import Model.BountyEncoding

namespace SputnikDAO2

theorem bountyLE_length (width value : Nat) :
    (NearSdk.Borsh.leBytes width value).length = width :=
  NearSdk.Borsh.leBytes_length width value

theorem bountyFromLE_bountyLE (width value : Nat)
    (hbound : value < 256 ^ width) :
    NearSdk.Borsh.fromLE (NearSdk.Borsh.leBytes width value) = value :=
  NearSdk.Borsh.fromLE_leBytes width value hbound

theorem bounty_count_key_injective_bounded (left right : Nat)
    (hleft : left < 256 ^ 8) (hright : right < 256 ^ 8)
    (heq : bountyCountKey left = bountyCountKey right) :
    left = right := by
  have hbytes : NearSdk.Borsh.leBytes 8 left = NearSdk.Borsh.leBytes 8 right := by
    simpa [bountyCountKey] using heq
  have hparsed := congrArg NearSdk.Borsh.fromLE hbytes
  simpa [bountyFromLE_bountyLE, hleft, hright] using hparsed

theorem bounty_claimers_key_injective (left right : String)
    (heq : bountyClaimersKey left = bountyClaimersKey right) :
    left = right := by
  have hencoded : bountyBorshString left = bountyBorshString right := by
    simpa [bountyClaimersKey] using heq
  have hbytes : left.toUTF8.data.toList = right.toUTF8.data.toList := by
    have hdrop := congrArg (List.drop 4) hencoded
    simpa [bountyBorshString, List.drop_append, bountyLE_length]
      using hdrop
  have hl : String.fromUTF8? ⟨left.toUTF8.data.toList.toArray⟩ =
      some left := by
    cases left with
    | ofByteArray bytes valid =>
        simp [String.toUTF8_eq_toByteArray, String.fromUTF8?,
          String.fromUTF8, valid]
  have hr : String.fromUTF8? ⟨right.toUTF8.data.toList.toArray⟩ =
      some right := by
    cases right with
    | ofByteArray bytes valid =>
        simp [String.toUTF8_eq_toByteArray, String.fromUTF8?,
          String.fromUTF8, valid]
  rw [hbytes] at hl
  rw [hl] at hr
  exact Option.some.inj hr

theorem bounty_claimers_and_count_keys_disjoint
    (account : String) (bountyId : Nat) :
    bountyClaimersKey account ≠ bountyCountKey bountyId := by
  simp [bountyClaimersKey, bountyCountKey]

theorem bounty_claimers_key_disjoint_from_other_prefix
    (account : String) (tag : UInt8) (suffix : BountyBytes)
    (hother : tag ∈ otherDAOPrefixes) :
    bountyClaimersKey account ≠ tag :: suffix := by
  have htag : tag ≠ 5 := by
    simp [otherDAOPrefixes] at hother
    rcases hother with h | h | h | h | h | h <;> subst tag <;> decide
  simp [bountyClaimersKey, Ne.symm htag]

theorem bounty_count_key_disjoint_from_other_prefix
    (bountyId : Nat) (tag : UInt8) (suffix : BountyBytes)
    (hother : tag ∈ otherDAOPrefixes) :
    bountyCountKey bountyId ≠ tag :: suffix := by
  have htag : tag ≠ 6 := by
    simp [otherDAOPrefixes] at hother
    rcases hother with h | h | h | h | h | h <;> subst tag <;> decide
  simp [bountyCountKey, Ne.symm htag]

theorem encoded_claim_length (claim : StoredBountyClaim) :
    (encodeStoredBountyClaim claim).length = 25 := by
  simp [encodeStoredBountyClaim]

theorem encoded_claim_physical_fields_injective_bounded
    (left right : StoredBountyClaim)
    (hleftId : left.bountyId < 256 ^ 8)
    (hrightId : right.bountyId < 256 ^ 8)
    (hleftStart : left.start < 256 ^ 8)
    (hrightStart : right.start < 256 ^ 8)
    (hleftDeadline : left.deadline < 256 ^ 8)
    (hrightDeadline : right.deadline < 256 ^ 8)
    (heq : encodeStoredBountyClaim left =
      encodeStoredBountyClaim right) :
    left.bountyId = right.bountyId ∧
      left.start = right.start ∧
      left.deadline = right.deadline ∧
      left.completed = right.completed := by
  have hidBytes : NearSdk.Borsh.leBytes 8 left.bountyId =
      NearSdk.Borsh.leBytes 8 right.bountyId := by
    have htake := congrArg (List.take 8) heq
    simpa [encodeStoredBountyClaim, bountyLE_length,
      List.take_append] using htake
  have hstartBytes : NearSdk.Borsh.leBytes 8 left.start =
      NearSdk.Borsh.leBytes 8 right.start := by
    have htake := congrArg (fun bytes =>
      (bytes.drop 8).take 8) heq
    simpa [encodeStoredBountyClaim, bountyLE_length,
      List.drop_append, List.take_append] using htake
  have hdeadlineBytes : NearSdk.Borsh.leBytes 8 left.deadline =
      NearSdk.Borsh.leBytes 8 right.deadline := by
    have htake := congrArg (fun bytes =>
      ((bytes.drop 8).drop 8).take 8) heq
    simpa [encodeStoredBountyClaim, bountyLE_length,
      List.drop_append, List.take_append] using htake
  have hcompletedBytes :
      (if left.completed then (1 : UInt8) else 0) =
      (if right.completed then (1 : UInt8) else 0) := by
    have hdrop := congrArg (fun bytes =>
      ((bytes.drop 8).drop 8).drop 8) heq
    simpa [encodeStoredBountyClaim, bountyLE_length,
      List.drop_append] using hdrop
  have hid := congrArg NearSdk.Borsh.fromLE hidBytes
  have hstart := congrArg NearSdk.Borsh.fromLE hstartBytes
  have hdeadline := congrArg NearSdk.Borsh.fromLE hdeadlineBytes
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [bountyFromLE_bountyLE, hleftId, hrightId] using hid
  · simpa [bountyFromLE_bountyLE, hleftStart, hrightStart] using hstart
  · simpa [bountyFromLE_bountyLE, hleftDeadline, hrightDeadline]
      using hdeadline
  · cases hl : left.completed <;> cases hr : right.completed <;>
      simp_all

theorem encoded_claims_length (claims : List StoredBountyClaim) :
    (encodeStoredBountyClaims claims).length = 4 + 25 * claims.length := by
  induction claims with
  | nil => simp [encodeStoredBountyClaims]
  | cons claim rest ih =>
      simp [encodeStoredBountyClaims,
        encoded_claim_length] at ih ⊢
      omega

theorem encoded_claims_body_length (claims : List StoredBountyClaim) :
    (claims.flatMap encodeStoredBountyClaim).length =
      25 * claims.length := by
  induction claims with
  | nil => rfl
  | cons claim tail ih =>
      simp only [List.flatMap_cons, List.length_append,
        encoded_claim_length, List.length_cons]
      omega

theorem ghost_paid_bond_is_not_serialized
    (claim : StoredBountyClaim) (otherBond : Nat) :
    encodeStoredBountyClaim { claim with paidBond := otherBond } =
      encodeStoredBountyClaim claim := by
  rfl

theorem encoded_count_length (count : Nat) :
    (encodeBountyCount count).length = 4 := by
  simp [encodeBountyCount]

theorem bounty_parse_nat_encoded (width value : Nat)
    (rest : BountyBytes) (hbound : value < 256 ^ width) :
    NearSdk.BorshParse.natural width (NearSdk.Borsh.leBytes width value ++ rest) =
      some (value, rest) := by
  simp [NearSdk.BorshParse.natural, NearSdk.BorshParse.take,
    bountyFromLE_bountyLE, hbound]

theorem bounty_parse_claim_encoded (claim : StoredBountyClaim)
    (rest : BountyBytes)
    (hid : claim.bountyId < 256 ^ 8)
    (hstart : claim.start < 256 ^ 8)
    (hdeadline : claim.deadline < 256 ^ 8) :
    bountyParseClaim (encodeStoredBountyClaim claim ++ rest) =
      some (physicalBountyClaim claim, rest) := by
  cases claim with
  | mk bountyId start deadline completed paidBond =>
      cases completed <;>
        simp [bountyParseClaim, encodeStoredBountyClaim,
          physicalBountyClaim, bounty_parse_nat_encoded,
          bountyParseBool, hid, hstart, hdeadline,
          List.append_assoc]

theorem bounty_parse_count_encoded (count : Nat)
    (hcount : count < 256 ^ 4) :
    bountyParseCount (encodeBountyCount count) = some count := by
  have hparse := bounty_parse_nat_encoded 4 count [] hcount
  simp only [List.append_nil] at hparse
  simp [bountyParseCount, encodeBountyCount, hparse]

theorem bounty_parse_bool_rejects_invalid_byte (byte : UInt8)
    (hzero : byte ≠ 0) (hone : byte ≠ 1) (rest : BountyBytes) :
    bountyParseBool (byte :: rest) = none := by
  simp [bountyParseBool, hzero, hone]

theorem bounty_parse_count_rejects_trailing_bytes
    (count : Nat) (extra : UInt8) (rest : BountyBytes)
    (hcount : count < 256 ^ 4) :
    bountyParseCount (encodeBountyCount count ++ extra :: rest) = none := by
  simp [bountyParseCount, encodeBountyCount,
    bounty_parse_nat_encoded, hcount]

theorem bounty_parse_claims_n_encoded
    (claims : List StoredBountyClaim) (rest : BountyBytes)
    (hvalid : ∀ claim ∈ claims, validStoredBountyClaim claim) :
    bountyParseClaimsN claims.length
      (claims.flatMap encodeStoredBountyClaim ++ rest) =
      some (claims.map physicalBountyClaim, rest) := by
  induction claims with
  | nil => simp [bountyParseClaimsN]
  | cons claim tail ih =>
      have hclaim := hvalid claim (by simp)
      have htail : ∀ item ∈ tail, validStoredBountyClaim item := by
        intro item hmem
        exact hvalid item (by simp [hmem])
      rcases hclaim with ⟨hid, hstart, hdeadline⟩
      simp [bountyParseClaimsN, bounty_parse_claim_encoded,
        ih htail, hid, hstart, hdeadline, List.append_assoc]

theorem bounty_parse_claims_encoded
    (claims : List StoredBountyClaim)
    (hlen : claims.length < 256 ^ 4)
    (hvalid : ∀ claim ∈ claims, validStoredBountyClaim claim) :
    bountyParseClaims (encodeStoredBountyClaims claims) =
      some (claims.map physicalBountyClaim) := by
  have hbody : (claims.flatMap encodeStoredBountyClaim).length =
      25 * claims.length := encoded_claims_body_length claims
  have hprefix := bounty_parse_nat_encoded 4 claims.length
    (claims.flatMap encodeStoredBountyClaim) hlen
  have hrecords := bounty_parse_claims_n_encoded claims [] hvalid
  simp only [List.append_nil] at hrecords
  simp [bountyParseClaims, encodeStoredBountyClaims,
    hprefix, hrecords, hbody, Nat.mul_comm]

theorem bounty_parse_claims_rejects_trailing_byte
    (claims : List StoredBountyClaim) (extra : UInt8)
    (hlen : claims.length < 256 ^ 4)
    (hvalid : ∀ claim ∈ claims, validStoredBountyClaim claim) :
    bountyParseClaims (encodeStoredBountyClaims claims ++ [extra]) =
      none := by
  have hbody : (claims.flatMap encodeStoredBountyClaim).length =
      25 * claims.length := encoded_claims_body_length claims
  have hprefix := bounty_parse_nat_encoded 4 claims.length
    (claims.flatMap encodeStoredBountyClaim ++ [extra]) hlen
  have hrecords := bounty_parse_claims_n_encoded claims [extra] hvalid
  simp [bountyParseClaims, encodeStoredBountyClaims,
    hprefix, hrecords, hbody, Nat.mul_comm, List.append_assoc]

theorem bounty_parse_claims_rejects_truncated_record :
    bountyParseClaims (NearSdk.Borsh.leBytes 4 1) = none := by
  decide

-- Exact vectors consumed by oracle/bounty_borsh_test.rs. The native test
-- exercises the pinned Rust BountyClaim type and SDK LookupMap writes.
theorem bounty_borsh_oracle_vectors :
    bountyClaimersKey "alice.near" =
      [5, 10, 0, 0, 0, 97, 108, 105, 99, 101, 46, 110, 101, 97, 114] ∧
    bountyCountKey 7 = [6, 7, 0, 0, 0, 0, 0, 0, 0] ∧
    bountyCountKey 8 = [6, 8, 0, 0, 0, 0, 0, 0, 0] ∧
    encodeStoredBountyClaims [⟨7, 1, 10, false, 5⟩] =
      [1, 0, 0, 0,
       7, 0, 0, 0, 0, 0, 0, 0,
       1, 0, 0, 0, 0, 0, 0, 0,
       10, 0, 0, 0, 0, 0, 0, 0,
       0] ∧
    encodeStoredBountyClaims [⟨7, 1, 10, true, 5⟩] =
      [1, 0, 0, 0,
       7, 0, 0, 0, 0, 0, 0, 0,
       1, 0, 0, 0, 0, 0, 0, 0,
       10, 0, 0, 0, 0, 0, 0, 0,
       1] ∧
    encodeStoredBountyClaims [⟨8, 3, 10, false, 5⟩] =
      [1, 0, 0, 0,
       8, 0, 0, 0, 0, 0, 0, 0,
       3, 0, 0, 0, 0, 0, 0, 0,
       10, 0, 0, 0, 0, 0, 0, 0,
       0] ∧
    encodeBountyCount 1 = [1, 0, 0, 0] ∧
    encodeBountyCount 0 = [0, 0, 0, 0] := by
  decide

end SputnikDAO2
