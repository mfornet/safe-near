import Model.BountyEncoding

namespace SputnikDAO2

/-! Borsh projection of Config and VersionedPolicy at LazyOption keys 0 and 1.
Lists representing Rust HashSet/HashMap values must be in Rust `Ord` order;
the encoder does not infer that order from a hash table. -/

def encodeBorshVec {α : Type} (encode : α → BountyBytes)
    (entries : List α) : BountyBytes :=
  NearSdk.Borsh.leBytes 4 entries.length ++ entries.flatMap encode

structure WireConfig where
  name : String
  purpose : String
  metadata : BountyBytes
  deriving Repr, DecidableEq

def encodeWireConfig (config : WireConfig) : BountyBytes :=
  bountyBorshString config.name ++
  bountyBorshString config.purpose ++
  NearSdk.Borsh.leBytes 4 config.metadata.length ++ config.metadata

inductive WireRoleKind where
  | everyone
  | member (minimum : Nat)
  | group (accounts : List String)
  deriving Repr, DecidableEq

def encodeWireRoleKind : WireRoleKind → BountyBytes
  | .everyone => [0]
  | .member minimum => 1 :: NearSdk.Borsh.leBytes 16 minimum
  | .group accounts => 2 :: encodeBorshVec bountyBorshString accounts

inductive WireWeightKind where
  | token | role
  deriving Repr, DecidableEq

def encodeWireWeightKind : WireWeightKind → BountyBytes
  | .token => [0]
  | .role => [1]

inductive WireWeightOrRatio where
  | weight (amount : Nat)
  | ratio (numerator denominator : Nat)
  deriving Repr, DecidableEq

def encodeWireWeightOrRatio : WireWeightOrRatio → BountyBytes
  | .weight amount => 0 :: NearSdk.Borsh.leBytes 16 amount
  | .ratio numerator denominator =>
      1 :: (NearSdk.Borsh.leBytes 8 numerator ++ NearSdk.Borsh.leBytes 8 denominator)

structure WireVotePolicy where
  weightKind : WireWeightKind
  quorum : Nat
  threshold : WireWeightOrRatio
  deriving Repr, DecidableEq

def encodeWireVotePolicy (policy : WireVotePolicy) : BountyBytes :=
  encodeWireWeightKind policy.weightKind ++
  NearSdk.Borsh.leBytes 16 policy.quorum ++
  encodeWireWeightOrRatio policy.threshold

structure WireRolePermission where
  name : String
  kind : WireRoleKind
  permissions : List String
  votePolicies : List (String × WireVotePolicy)
  deriving Repr, DecidableEq

def encodeWireRolePermission (role : WireRolePermission) : BountyBytes :=
  bountyBorshString role.name ++
  encodeWireRoleKind role.kind ++
  encodeBorshVec bountyBorshString role.permissions ++
  encodeBorshVec (fun entry =>
    bountyBorshString entry.1 ++ encodeWireVotePolicy entry.2)
    role.votePolicies

structure WirePolicy where
  roles : List WireRolePermission
  defaultVotePolicy : WireVotePolicy
  proposalBond : Nat
  proposalPeriod : Nat
  bountyBond : Nat
  bountyForgivenessPeriod : Nat
  deriving Repr, DecidableEq

def encodeWirePolicy (policy : WirePolicy) : BountyBytes :=
  encodeBorshVec encodeWireRolePermission policy.roles ++
  encodeWireVotePolicy policy.defaultVotePolicy ++
  NearSdk.Borsh.leBytes 16 policy.proposalBond ++
  NearSdk.Borsh.leBytes 8 policy.proposalPeriod ++
  NearSdk.Borsh.leBytes 16 policy.bountyBond ++
  NearSdk.Borsh.leBytes 8 policy.bountyForgivenessPeriod

inductive WireVersionedPolicy where
  | default (council : List String)
  | current (policy : WirePolicy)
  deriving Repr, DecidableEq

def encodeWireVersionedPolicy : WireVersionedPolicy → BountyBytes
  | .default council => 0 :: encodeBorshVec bountyBorshString council
  | .current policy => 1 :: encodeWirePolicy policy

def upgradeWireVersionedPolicy (makeDefault : List String → WirePolicy) :
    WireVersionedPolicy → WireVersionedPolicy
  | .default council => .current (makeDefault council)
  | .current policy => .current policy

def wireStringsOrdered (entries : List String) : Prop :=
  entries.Pairwise (fun left right => left < right)

def wireRoleOrdered (role : WireRolePermission) : Prop :=
  (match role.kind with
   | .group accounts => wireStringsOrdered accounts
   | _ => True) ∧
  wireStringsOrdered role.permissions ∧
  (role.votePolicies.map Prod.fst).Pairwise (fun left right => left < right)

def wirePolicyOrdered (policy : WirePolicy) : Prop :=
  ∀ role ∈ policy.roles, wireRoleOrdered role

def wireStringFits (value : String) : Prop :=
  value.toUTF8.data.toList.length < 256 ^ 4

def wireConfigFits (config : WireConfig) : Prop :=
  wireStringFits config.name ∧
  wireStringFits config.purpose ∧
  config.metadata.length < 256 ^ 4

def wireThresholdFits : WireWeightOrRatio → Prop
  | .weight amount => amount < 256 ^ 16
  | .ratio numerator denominator =>
      numerator < 256 ^ 8 ∧ 0 < denominator ∧ denominator < 256 ^ 8

def wireVotePolicyFits (policy : WireVotePolicy) : Prop :=
  policy.quorum < 256 ^ 16 ∧ wireThresholdFits policy.threshold

def wireRoleKindFits : WireRoleKind → Prop
  | .everyone => True
  | .member minimum => minimum < 256 ^ 16
  | .group accounts =>
      accounts.length < 256 ^ 4 ∧ ∀ account ∈ accounts, wireStringFits account

def wireRoleFits (role : WireRolePermission) : Prop :=
  wireStringFits role.name ∧
  wireRoleKindFits role.kind ∧
  role.permissions.length < 256 ^ 4 ∧
  (∀ permission ∈ role.permissions, wireStringFits permission) ∧
  role.votePolicies.length < 256 ^ 4 ∧
  (∀ entry ∈ role.votePolicies,
    wireStringFits entry.1 ∧ wireVotePolicyFits entry.2) ∧
  wireRoleOrdered role

def wirePolicyFits (policy : WirePolicy) : Prop :=
  policy.roles.length < 256 ^ 4 ∧
  (∀ role ∈ policy.roles, wireRoleFits role) ∧
  wireVotePolicyFits policy.defaultVotePolicy ∧
  policy.proposalBond < 256 ^ 16 ∧
  policy.proposalPeriod < 256 ^ 8 ∧
  policy.bountyBond < 256 ^ 16 ∧
  policy.bountyForgivenessPeriod < 256 ^ 8

def wireVersionedPolicyFits : WireVersionedPolicy → Prop
  | .default council =>
      council.length < 256 ^ 4 ∧
      ∀ account ∈ council, wireStringFits account
  | .current policy => wirePolicyFits policy

def wireTestConfig : WireConfig :=
  ⟨"Test", "to test", [0, 255, 1]⟩

def wireDefaultVote : WireVotePolicy :=
  ⟨.role, 0, .ratio 1 2⟩

def wireSmallPolicy : WirePolicy :=
  ⟨[], wireDefaultVote, 17, 123, 19, 456⟩

def wireRoleFixture : WireRolePermission :=
  ⟨"council", .group ["a.near", "z.near"],
    ["X:VoteApprove", "X:VoteReject"],
    [("A", wireDefaultVote), ("Z", wireDefaultVote)]⟩

end SputnikDAO2
