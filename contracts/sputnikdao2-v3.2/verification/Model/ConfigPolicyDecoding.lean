import Model.ConfigPolicyEncoding

namespace SputnikDAO2

def parseWireString : BountyParser String := fun input => do
  let (size, rest) ← bountyParseNat 4 input
  if size > rest.length then none
  else do
    let text ← String.fromUTF8? ⟨(rest.take size).toArray⟩
    some (text, rest.drop size)

def parseWireVecN {α : Type} (parse : BountyParser α) :
    Nat → BountyParser (List α)
  | 0, input => some ([], input)
  | count + 1, input => do
      let (item, rest) ← parse input
      let (items, tail) ← parseWireVecN parse count rest
      some (item :: items, tail)

def parseWireVec {α : Type} (parse : BountyParser α) :
    BountyParser (List α) := fun input => do
  let (count, rest) ← bountyParseNat 4 input
  parseWireVecN parse count rest

def parseWireConfig : BountyParser WireConfig := fun input => do
  let (name, rest) ← parseWireString input
  let (purpose, rest) ← parseWireString rest
  let (size, rest) ← bountyParseNat 4 rest
  if size > rest.length then none
  else some (⟨name, purpose, rest.take size⟩, rest.drop size)

def parseWireRoleKind : BountyParser WireRoleKind
  | [] => none
  | tag :: rest =>
      if tag == 0 then some (.everyone, rest)
      else if tag == 1 then do
        let (minimum, tail) ← bountyParseNat 16 rest
        some (.member minimum, tail)
      else if tag == 2 then do
        let (accounts, tail) ← parseWireVec parseWireString rest
        some (.group accounts, tail)
      else none

def parseWireWeightKind : BountyParser WireWeightKind
  | [] => none
  | tag :: rest =>
      if tag == 0 then some (.token, rest)
      else if tag == 1 then some (.role, rest)
      else none

def parseWireWeightOrRatio : BountyParser WireWeightOrRatio
  | [] => none
  | tag :: rest =>
      if tag == 0 then do
        let (amount, tail) ← bountyParseNat 16 rest
        some (.weight amount, tail)
      else if tag == 1 then do
        let (numerator, tail) ← bountyParseNat 8 rest
        let (denominator, tail) ← bountyParseNat 8 tail
        if denominator == 0 then none
        else some (.ratio numerator denominator, tail)
      else none

def parseWireVotePolicy : BountyParser WireVotePolicy := fun input => do
  let (weightKind, rest) ← parseWireWeightKind input
  let (quorum, rest) ← bountyParseNat 16 rest
  let (threshold, rest) ← parseWireWeightOrRatio rest
  some (⟨weightKind, quorum, threshold⟩, rest)

def parseWirePolicyEntry : BountyParser (String × WireVotePolicy) :=
    fun input => do
  let (name, rest) ← parseWireString input
  let (policy, rest) ← parseWireVotePolicy rest
  some ((name, policy), rest)

def parseWireRolePermission : BountyParser WireRolePermission :=
    fun input => do
  let (name, rest) ← parseWireString input
  let (kind, rest) ← parseWireRoleKind rest
  let (permissions, rest) ← parseWireVec parseWireString rest
  let (votePolicies, rest) ← parseWireVec parseWirePolicyEntry rest
  some (⟨name, kind, permissions, votePolicies⟩, rest)

def parseWirePolicy : BountyParser WirePolicy := fun input => do
  let (roles, rest) ← parseWireVec parseWireRolePermission input
  let (defaultVotePolicy, rest) ← parseWireVotePolicy rest
  let (proposalBond, rest) ← bountyParseNat 16 rest
  let (proposalPeriod, rest) ← bountyParseNat 8 rest
  let (bountyBond, rest) ← bountyParseNat 16 rest
  let (bountyForgivenessPeriod, rest) ← bountyParseNat 8 rest
  some (⟨roles, defaultVotePolicy, proposalBond, proposalPeriod,
    bountyBond, bountyForgivenessPeriod⟩, rest)

def parseWireVersionedPolicy : BountyParser WireVersionedPolicy
  | [] => none
  | tag :: rest =>
      if tag == 0 then do
        let (council, tail) ← parseWireVec parseWireString rest
        some (.default council, tail)
      else if tag == 1 then do
        let (policy, tail) ← parseWirePolicy rest
        some (.current policy, tail)
      else none

def parseWireConfigExact (bytes : BountyBytes) : Option WireConfig := do
  let (config, rest) ← parseWireConfig bytes
  if rest.isEmpty then some config else none

def parseWirePolicyExact (bytes : BountyBytes) :
    Option WireVersionedPolicy := do
  let (policy, rest) ← parseWireVersionedPolicy bytes
  if rest.isEmpty then some policy else none

-- The resolved Borsh build has no `de_strict_order` feature. Rust collects
-- parsed Vecs into HashSet/HashMap: sets deduplicate, and a later duplicate
-- map key replaces the earlier value. Re-encoding sorts the surviving keys.
def insertStringSorted (item : String) : List String → List String
  | [] => [item]
  | head :: tail =>
      if item < head then item :: head :: tail
      else head :: insertStringSorted item tail

def canonicalStringSet (entries : List String) : List String :=
  (entries.foldl (fun sorted item => insertStringSorted item sorted) []).eraseDups

def lastWireVotePolicy (entries : List (String × WireVotePolicy))
    (key : String) : Option WireVotePolicy :=
  ((entries.reverse.find? (fun entry => entry.1 == key))).map Prod.snd

def materializeWireVoteMap (keys : List String)
    (entries : List (String × WireVotePolicy)) :
    List (String × WireVotePolicy) :=
  keys.filterMap (fun key =>
    (lastWireVotePolicy entries key).map (fun value => (key, value)))

def canonicalWireVoteMap (entries : List (String × WireVotePolicy)) :
    List (String × WireVotePolicy) :=
  let keys := canonicalStringSet (entries.map Prod.fst)
  materializeWireVoteMap keys entries

def canonicalWireRole (role : WireRolePermission) : WireRolePermission :=
  { role with
    kind := match role.kind with
      | .group accounts => .group (canonicalStringSet accounts)
      | other => other
    permissions := canonicalStringSet role.permissions
    votePolicies := canonicalWireVoteMap role.votePolicies }

def wireRoleKindMatches (kind : WireRoleKind)
    (account : String) (balance : Nat) : Prop :=
  match kind with
  | .everyone => True
  | .member minimum => minimum ≤ balance
  | .group accounts => account ∈ accounts

end SputnikDAO2
