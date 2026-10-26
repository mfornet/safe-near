import Model.ConfigPolicyDecoding
import Proofs.BountyEncoding
import Proofs.ConfigPolicyEncoding

namespace SputnikDAO2

set_option maxRecDepth 4096

theorem parse_wire_string_encoded (value : String) (rest : BountyBytes)
    (hsize : wireStringFits value) :
    parseWireString (bountyBorshString value ++ rest) =
      some (value, rest) := by
  have hutf8 : String.fromUTF8? value.toByteArray = some value := by
    cases value with
    | ofByteArray bytes valid =>
        simp [String.fromUTF8?, String.fromUTF8, valid]
  unfold parseWireString bountyBorshString
  simp only [List.append_assoc]
  rw [bounty_parse_nat_encoded 4 value.toUTF8.data.toList.length
    (value.toUTF8.data.toList ++ rest) hsize]
  simp [hutf8]

theorem parse_wire_config_encoded (config : WireConfig)
    (rest : BountyBytes) (hfits : wireConfigFits config) :
    parseWireConfig (encodeWireConfig config ++ rest) =
      some (config, rest) := by
  rcases hfits with ⟨hname, hpurpose, hmetadata⟩
  have hnameParse := parse_wire_string_encoded config.name
    (bountyBorshString config.purpose ++
      NearSdk.Borsh.leBytes 4 config.metadata.length ++ config.metadata ++ rest)
    hname
  have hpurposeParse := parse_wire_string_encoded config.purpose
    (NearSdk.Borsh.leBytes 4 config.metadata.length ++ config.metadata ++ rest)
    hpurpose
  have hmetadataParse := bounty_parse_nat_encoded 4
    config.metadata.length (config.metadata ++ rest) hmetadata
  unfold parseWireConfig encodeWireConfig
  simp only [List.append_assoc] at hnameParse hpurposeParse hmetadataParse ⊢
  simp [hnameParse, hpurposeParse, hmetadataParse]

theorem parse_wire_config_exact_encoded (config : WireConfig)
    (hfits : wireConfigFits config) :
    parseWireConfigExact (encodeWireConfig config) = some config := by
  have hparse := parse_wire_config_encoded config [] hfits
  simp only [List.append_nil] at hparse
  simp [parseWireConfigExact, hparse]

theorem parse_wire_config_rejects_trailing_byte (config : WireConfig)
    (extra : UInt8) (hfits : wireConfigFits config) :
    parseWireConfigExact (encodeWireConfig config ++ [extra]) = none := by
  have hparse := parse_wire_config_encoded config [extra] hfits
  simp [parseWireConfigExact, hparse]

theorem parse_wire_vec_n_encoded {α : Type}
    (encode : α → BountyBytes) (parse : BountyParser α)
    (entries : List α) (rest : BountyBytes)
    (hparse : ∀ item ∈ entries, ∀ tail,
      parse (encode item ++ tail) = some (item, tail)) :
    parseWireVecN parse entries.length
      (entries.flatMap encode ++ rest) = some (entries, rest) := by
  induction entries with
  | nil => simp [parseWireVecN]
  | cons item tail ih =>
      have hitem : ∀ suffix,
          parse (encode item ++ suffix) = some (item, suffix) :=
        hparse item (by simp)
      have htail : ∀ entry ∈ tail, ∀ suffix,
          parse (encode entry ++ suffix) = some (entry, suffix) := by
        intro entry hmem suffix
        exact hparse entry (by simp [hmem]) suffix
      simp [parseWireVecN, hitem, ih htail, List.append_assoc]

theorem parse_wire_vec_encoded {α : Type}
    (encode : α → BountyBytes) (parse : BountyParser α)
    (entries : List α) (rest : BountyBytes)
    (hlen : entries.length < 256 ^ 4)
    (hparse : ∀ item ∈ entries, ∀ tail,
      parse (encode item ++ tail) = some (item, tail)) :
    parseWireVec parse (encodeBorshVec encode entries ++ rest) =
      some (entries, rest) := by
  have hlength := bounty_parse_nat_encoded 4 entries.length
    (entries.flatMap encode ++ rest) hlen
  have hbody := parse_wire_vec_n_encoded encode parse entries rest hparse
  simpa [parseWireVec, encodeBorshVec, List.append_assoc,
    hlength] using hbody

theorem parse_wire_weight_kind_encoded (kind : WireWeightKind)
    (rest : BountyBytes) :
    parseWireWeightKind (encodeWireWeightKind kind ++ rest) =
      some (kind, rest) := by
  cases kind <;> rfl

theorem parse_wire_threshold_encoded (threshold : WireWeightOrRatio)
    (rest : BountyBytes) (hfits : wireThresholdFits threshold) :
    parseWireWeightOrRatio (encodeWireWeightOrRatio threshold ++ rest) =
      some (threshold, rest) := by
  cases threshold with
  | weight amount =>
      change (do
        let (read, tail) ← NearSdk.BorshParse.natural 16 (NearSdk.Borsh.leBytes 16 amount ++ rest)
        some (WireWeightOrRatio.weight read, tail)) =
          some (WireWeightOrRatio.weight amount, rest)
      rw [bounty_parse_nat_encoded 16 amount rest hfits]
      rfl
  | ratio numerator denominator =>
      rcases hfits with ⟨hnum, hdenpos, hden⟩
      have hnumParse := bounty_parse_nat_encoded 8 numerator
        (NearSdk.Borsh.leBytes 8 denominator ++ rest) hnum
      have hdenParse := bounty_parse_nat_encoded 8 denominator rest hden
      simp [parseWireWeightOrRatio, encodeWireWeightOrRatio,
        List.append_assoc, hnumParse, hdenParse, Nat.ne_of_gt hdenpos]

theorem parse_wire_role_kind_encoded (kind : WireRoleKind)
    (rest : BountyBytes) (hfits : wireRoleKindFits kind) :
    parseWireRoleKind (encodeWireRoleKind kind ++ rest) =
      some (kind, rest) := by
  cases kind with
  | everyone => rfl
  | member minimum =>
      change (do
        let (read, tail) ← NearSdk.BorshParse.natural 16 (NearSdk.Borsh.leBytes 16 minimum ++ rest)
        some (WireRoleKind.member read, tail)) =
          some (WireRoleKind.member minimum, rest)
      rw [bounty_parse_nat_encoded 16 minimum rest hfits]
      rfl
  | group accounts =>
      rcases hfits with ⟨hlen, hstrings⟩
      have hvec := parse_wire_vec_encoded bountyBorshString
        parseWireString accounts rest hlen (by
          intro account hmem tail
          exact parse_wire_string_encoded account tail
            (hstrings account hmem))
      simp [parseWireRoleKind, encodeWireRoleKind, hvec]

theorem parse_wire_vote_policy_encoded (policy : WireVotePolicy)
    (rest : BountyBytes) (hfits : wireVotePolicyFits policy) :
    parseWireVotePolicy (encodeWireVotePolicy policy ++ rest) =
      some (policy, rest) := by
  rcases hfits with ⟨hquorum, hthreshold⟩
  have hkind := parse_wire_weight_kind_encoded policy.weightKind
    (NearSdk.Borsh.leBytes 16 policy.quorum ++
      encodeWireWeightOrRatio policy.threshold ++ rest)
  have hquorumParse := bounty_parse_nat_encoded 16 policy.quorum
    (encodeWireWeightOrRatio policy.threshold ++ rest) hquorum
  have hthresholdParse := parse_wire_threshold_encoded policy.threshold
    rest hthreshold
  unfold parseWireVotePolicy encodeWireVotePolicy
  simp only [List.append_assoc] at hkind hquorumParse hthresholdParse ⊢
  simp [hkind, hquorumParse, hthresholdParse]

theorem parse_wire_policy_entry_encoded
    (entry : String × WireVotePolicy) (rest : BountyBytes)
    (hfits : wireStringFits entry.1 ∧ wireVotePolicyFits entry.2) :
    parseWirePolicyEntry
      (bountyBorshString entry.1 ++ encodeWireVotePolicy entry.2 ++ rest) =
        some (entry, rest) := by
  rcases entry with ⟨name, policy⟩
  rcases hfits with ⟨hname, hpolicy⟩
  have hnameParse := parse_wire_string_encoded name
    (encodeWireVotePolicy policy ++ rest) hname
  have hpolicyParse := parse_wire_vote_policy_encoded policy rest hpolicy
  unfold parseWirePolicyEntry
  simp only [List.append_assoc] at hnameParse hpolicyParse ⊢
  simp [hnameParse, hpolicyParse]

theorem parse_wire_role_encoded (role : WireRolePermission)
    (rest : BountyBytes) (hfits : wireRoleFits role) :
    parseWireRolePermission (encodeWireRolePermission role ++ rest) =
      some (role, rest) := by
  rcases hfits with
    ⟨hname, hkind, hplen, hpermissions, hmlen, hmap, _hordered⟩
  have hnameParse := parse_wire_string_encoded role.name
    (encodeWireRoleKind role.kind ++
      encodeBorshVec bountyBorshString role.permissions ++
      encodeBorshVec (fun entry =>
        bountyBorshString entry.1 ++ encodeWireVotePolicy entry.2)
        role.votePolicies ++ rest) hname
  have hkindParse := parse_wire_role_kind_encoded role.kind
    (encodeBorshVec bountyBorshString role.permissions ++
      encodeBorshVec (fun entry =>
        bountyBorshString entry.1 ++ encodeWireVotePolicy entry.2)
        role.votePolicies ++ rest) hkind
  have hpermissionsParse := parse_wire_vec_encoded bountyBorshString
    parseWireString role.permissions
    (encodeBorshVec (fun entry =>
      bountyBorshString entry.1 ++ encodeWireVotePolicy entry.2)
      role.votePolicies ++ rest) hplen (by
      intro permission hmem tail
      exact parse_wire_string_encoded permission tail
        (hpermissions permission hmem))
  have hmapParse := parse_wire_vec_encoded
    (fun entry => bountyBorshString entry.1 ++
      encodeWireVotePolicy entry.2)
    parseWirePolicyEntry role.votePolicies rest hmlen (by
      intro entry hmem tail
      exact parse_wire_policy_entry_encoded entry tail (hmap entry hmem))
  unfold parseWireRolePermission encodeWireRolePermission
  simp only [List.append_assoc] at hnameParse hkindParse hpermissionsParse hmapParse ⊢
  simp [hnameParse, hkindParse, hpermissionsParse, hmapParse]

theorem parse_wire_policy_encoded (policy : WirePolicy)
    (rest : BountyBytes) (hfits : wirePolicyFits policy) :
    parseWirePolicy (encodeWirePolicy policy ++ rest) =
      some (policy, rest) := by
  rcases hfits with
    ⟨hlen, hroles, hdefault, hproposalBond, hproposalPeriod,
      hbountyBond, hforgiveness⟩
  have hrolesParse := parse_wire_vec_encoded encodeWireRolePermission
    parseWireRolePermission policy.roles
    (encodeWireVotePolicy policy.defaultVotePolicy ++
      NearSdk.Borsh.leBytes 16 policy.proposalBond ++
      NearSdk.Borsh.leBytes 8 policy.proposalPeriod ++
      NearSdk.Borsh.leBytes 16 policy.bountyBond ++
      NearSdk.Borsh.leBytes 8 policy.bountyForgivenessPeriod ++ rest)
    hlen (by
      intro role hmem tail
      exact parse_wire_role_encoded role tail (hroles role hmem))
  have hdefaultParse := parse_wire_vote_policy_encoded
    policy.defaultVotePolicy
    (NearSdk.Borsh.leBytes 16 policy.proposalBond ++
      NearSdk.Borsh.leBytes 8 policy.proposalPeriod ++
      NearSdk.Borsh.leBytes 16 policy.bountyBond ++
      NearSdk.Borsh.leBytes 8 policy.bountyForgivenessPeriod ++ rest)
    hdefault
  have hproposalBondParse := bounty_parse_nat_encoded 16
    policy.proposalBond
    (NearSdk.Borsh.leBytes 8 policy.proposalPeriod ++
      NearSdk.Borsh.leBytes 16 policy.bountyBond ++
      NearSdk.Borsh.leBytes 8 policy.bountyForgivenessPeriod ++ rest)
    hproposalBond
  have hproposalPeriodParse := bounty_parse_nat_encoded 8
    policy.proposalPeriod
    (NearSdk.Borsh.leBytes 16 policy.bountyBond ++
      NearSdk.Borsh.leBytes 8 policy.bountyForgivenessPeriod ++ rest)
    hproposalPeriod
  have hbountyBondParse := bounty_parse_nat_encoded 16
    policy.bountyBond
    (NearSdk.Borsh.leBytes 8 policy.bountyForgivenessPeriod ++ rest)
    hbountyBond
  have hforgivenessParse := bounty_parse_nat_encoded 8
    policy.bountyForgivenessPeriod rest hforgiveness
  unfold parseWirePolicy encodeWirePolicy
  simp only [List.append_assoc] at hrolesParse hdefaultParse hproposalBondParse hproposalPeriodParse hbountyBondParse hforgivenessParse ⊢
  simp [hrolesParse, hdefaultParse, hproposalBondParse,
    hproposalPeriodParse, hbountyBondParse, hforgivenessParse]

theorem parse_wire_versioned_policy_encoded
    (value : WireVersionedPolicy) (rest : BountyBytes)
    (hfits : wireVersionedPolicyFits value) :
    parseWireVersionedPolicy
      (encodeWireVersionedPolicy value ++ rest) =
        some (value, rest) := by
  cases value with
  | default council =>
      rcases hfits with ⟨hlen, haccounts⟩
      have hvec := parse_wire_vec_encoded bountyBorshString
        parseWireString council rest hlen (by
          intro account hmem tail
          exact parse_wire_string_encoded account tail
            (haccounts account hmem))
      simp [parseWireVersionedPolicy,
        encodeWireVersionedPolicy, hvec]
  | current policy =>
      have hpolicy := parse_wire_policy_encoded policy rest hfits
      simp [parseWireVersionedPolicy,
        encodeWireVersionedPolicy, hpolicy]

theorem parse_wire_policy_exact_encoded
    (value : WireVersionedPolicy)
    (hfits : wireVersionedPolicyFits value) :
    parseWirePolicyExact (encodeWireVersionedPolicy value) =
      some value := by
  have hparse := parse_wire_versioned_policy_encoded value [] hfits
  simp only [List.append_nil] at hparse
  simp [parseWirePolicyExact, hparse]

theorem parse_wire_policy_rejects_trailing_byte
    (value : WireVersionedPolicy) (extra : UInt8)
    (hfits : wireVersionedPolicyFits value) :
    parseWirePolicyExact (encodeWireVersionedPolicy value ++ [extra]) =
      none := by
  have hparse := parse_wire_versioned_policy_encoded value [extra] hfits
  simp [parseWirePolicyExact, hparse]

theorem wire_fixture_config_roundtrip :
    parseWireConfigExact (encodeWireConfig wireTestConfig) =
      some wireTestConfig := by
  exact parse_wire_config_exact_encoded wireTestConfig wire_test_config_fits

theorem wire_fixture_policy_roundtrip :
    parseWirePolicyExact
      (encodeWireVersionedPolicy (.current wireSmallPolicy)) =
      some (.current wireSmallPolicy) := by
  exact parse_wire_policy_exact_encoded (.current wireSmallPolicy)
    wire_small_policy_fits

theorem wire_policy_invalid_tag_rejected (bytes : BountyBytes) :
    parseWirePolicyExact (2 :: bytes) = none := by
  simp [parseWirePolicyExact, parseWireVersionedPolicy]

theorem wire_policy_zero_denominator_rejected :
    parseWirePolicyExact
      (encodeWireVersionedPolicy (.current
        { wireSmallPolicy with defaultVotePolicy :=
          ⟨.role, 0, .ratio 1 0⟩ })) = none := by
  decide

def noncanonicalWireRole : WireRolePermission :=
  ⟨"test", .everyone, ["Z", "A", "A"],
    [("Z", { wireDefaultVote with quorum := 3 }),
     ("A", { wireDefaultVote with quorum := 5 }),
     ("A", { wireDefaultVote with quorum := 7 })]⟩

theorem mem_insert_string_sorted (entries : List String)
    (item query : String) :
    query ∈ insertStringSorted item entries ↔
      query = item ∨ query ∈ entries := by
  induction entries with
  | nil => simp [insertStringSorted]
  | cons head tail ih =>
      by_cases hlt : item < head
      · simp [insertStringSorted, hlt]
      · simp [insertStringSorted, hlt, ih, or_left_comm]

theorem mem_string_sort_fold (entries sorted : List String)
    (query : String) :
    query ∈ entries.foldl
      (fun acc item => insertStringSorted item acc) sorted ↔
        query ∈ sorted ∨ query ∈ entries := by
  induction entries generalizing sorted with
  | nil => simp
  | cons head tail ih =>
      simp [List.foldl_cons, ih, mem_insert_string_sorted,
        or_assoc, or_left_comm]

theorem canonical_string_set_preserves_membership
    (entries : List String) (value : String) :
    value ∈ canonicalStringSet entries ↔ value ∈ entries := by
  simp [canonicalStringSet, mem_string_sort_fold]

theorem last_wire_vote_policy_append_same_key
    (entries : List (String × WireVotePolicy))
    (key : String) (value : WireVotePolicy) :
    lastWireVotePolicy (entries ++ [(key, value)]) key = some value := by
  simp [lastWireVotePolicy]

theorem last_wire_vote_policy_append_other_key
    (entries : List (String × WireVotePolicy))
    (key query : String) (value : WireVotePolicy)
    (hneq : query ≠ key) :
    lastWireVotePolicy (entries ++ [(key, value)]) query =
      lastWireVotePolicy entries query := by
  have hother : key ≠ query := Ne.symm hneq
  simp [lastWireVotePolicy, hother]

theorem last_wire_vote_policy_cons
    (entries : List (String × WireVotePolicy))
    (key query : String) (value : WireVotePolicy) :
    lastWireVotePolicy ((key, value) :: entries) query =
      (lastWireVotePolicy entries query).or
        (if key == query then some value else none) := by
  simp [lastWireVotePolicy, List.find?_append]
  cases hfind : (List.find? (fun entry => entry.1 == query)
    entries.reverse) with
  | none =>
      by_cases hsame : key = query <;> simp [hsame]
  | some found => simp

theorem last_wire_vote_policy_materialized
    (keys : List String)
    (entries : List (String × WireVotePolicy))
    (query : String) :
    lastWireVotePolicy (materializeWireVoteMap keys entries) query =
      if query ∈ keys then lastWireVotePolicy entries query else none := by
  induction keys with
  | nil => simp [materializeWireVoteMap, lastWireVotePolicy]
  | cons key tail ih =>
      simp only [materializeWireVoteMap] at ih ⊢
      by_cases hsame : key = query
      · subst key
        cases hvalue : lastWireVotePolicy entries query with
        | none =>
            simp [hvalue, ih]
        | some value =>
            simp [hvalue, last_wire_vote_policy_cons, ih]
            by_cases hmem : query ∈ tail <;> simp [hmem]
      · cases hvalue : lastWireVotePolicy entries key with
        | none =>
            have hother : query ≠ key := Ne.symm hsame
            simp [hvalue, hother, ih]
        | some value =>
            have hother : query ≠ key := Ne.symm hsame
            simp [hvalue, hother, last_wire_vote_policy_cons, ih]
            simp [hsame]

theorem last_wire_vote_policy_none_of_absent_key
    (entries : List (String × WireVotePolicy))
    (query : String)
    (habsent : query ∉ entries.map Prod.fst) :
    lastWireVotePolicy entries query = none := by
  have hfind :
      (entries.reverse.find? (fun entry => entry.1 == query)) =
        none := by
    apply List.find?_eq_none.mpr
    intro entry hmem
    have horiginal : entry ∈ entries := by
      simpa using hmem
    have hkey : entry.1 ∈ entries.map Prod.fst := by
      exact List.mem_map.mpr ⟨entry, horiginal, rfl⟩
    have hneq : entry.1 ≠ query := by
      intro heq
      exact habsent (heq ▸ hkey)
    simp [hneq]
  simp [lastWireVotePolicy, hfind]

theorem canonical_vote_map_preserves_lookup
    (entries : List (String × WireVotePolicy))
    (query : String) :
    lastWireVotePolicy (canonicalWireVoteMap entries) query =
      lastWireVotePolicy entries query := by
  have hmaterialized := last_wire_vote_policy_materialized
    (canonicalStringSet (entries.map Prod.fst)) entries query
  simp only [canonicalWireVoteMap] at hmaterialized ⊢
  rw [hmaterialized]
  by_cases hmem : query ∈ entries.map Prod.fst
  · have hcanonical :
        query ∈ canonicalStringSet (entries.map Prod.fst) :=
      (canonical_string_set_preserves_membership _ _).2 hmem
    simp [hcanonical]
  · have hcanonical :
        query ∉ canonicalStringSet (entries.map Prod.fst) := by
      simpa [canonical_string_set_preserves_membership] using hmem
    have hnone := last_wire_vote_policy_none_of_absent_key
      entries query hmem
    simp [hcanonical, hnone]

theorem canonical_role_preserves_matching
    (role : WireRolePermission) (account : String)
    (balance : Nat) :
    wireRoleKindMatches (canonicalWireRole role).kind account balance ↔
      wireRoleKindMatches role.kind account balance := by
  cases hkind : role.kind with
  | everyone => simp [canonicalWireRole, wireRoleKindMatches, hkind]
  | member minimum =>
      simp [canonicalWireRole, wireRoleKindMatches, hkind]
  | group accounts =>
      simpa [canonicalWireRole, wireRoleKindMatches, hkind] using
        canonical_string_set_preserves_membership accounts account

theorem canonical_role_preserves_permission
    (role : WireRolePermission) (permission : String) :
    permission ∈ (canonicalWireRole role).permissions ↔
      permission ∈ role.permissions := by
  exact canonical_string_set_preserves_membership
    role.permissions permission

theorem canonical_role_preserves_vote_policy_lookup
    (role : WireRolePermission) (kindLabel : String) :
    lastWireVotePolicy (canonicalWireRole role).votePolicies kindLabel =
      lastWireVotePolicy role.votePolicies kindLabel := by
  exact canonical_vote_map_preserves_lookup role.votePolicies kindLabel

theorem noncanonical_role_is_not_ordered :
    ¬ wireRoleOrdered noncanonicalWireRole := by
  simp [wireRoleOrdered, wireStringsOrdered, noncanonicalWireRole]

theorem noncanonical_vote_map_last_write_wins :
    lastWireVotePolicy noncanonicalWireRole.votePolicies "A" =
      some { wireDefaultVote with quorum := 7 } := by
  decide

theorem noncanonical_role_normalizes_to_sorted_unique_fields :
    canonicalWireRole noncanonicalWireRole =
      ⟨"test", .everyone, ["A", "Z"],
        [("A", { wireDefaultVote with quorum := 7 }),
         ("Z", { wireDefaultVote with quorum := 3 })]⟩ := by
  decide

end SputnikDAO2
