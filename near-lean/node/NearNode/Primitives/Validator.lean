import NearNode.Primitives.Basic

/-!
# Validators and epoch ids in headers

`near-primitives::types` at `=0.37.4`: `EpochId`, `ValidatorStakeV1`, the versioned `ValidatorStake`
(only V1 exists), `SlashedValidator`, `SpiceChunkEndorsementStats`, `TrieSplit` and the
block-producer-set hash.
-/

namespace Near.Node

open Borsh

/-- `EpochId`: the hash of the epoch's first block's predecessor. -/
structure EpochId where
  hash : CryptoHash
  deriving BEq, Inhabited

instance : Codec EpochId :=
  .iso CryptoHash .mk EpochId.hash

/-- `ValidatorStakeV1`: the unversioned form, still used in old headers and chunks. -/
structure ValidatorStakeV1 where
  accountId : AccountId
  publicKey : PublicKey
  stake : Balance
  deriving BEq, Inhabited

instance : Codec ValidatorStakeV1 :=
  .iso (AccountId × PublicKey × Balance) (fun (a, k, s) => ⟨a, k, s⟩) fun x =>
    (x.accountId, x.publicKey, x.stake)

/-- `ValidatorStake`: a tagged `ValidatorStakeV1`. No other version exists. -/
inductive ValidatorStake where
  | v1 (v : ValidatorStakeV1)
  deriving BEq, Inhabited

instance : Codec ValidatorStake :=
  .enum "ValidatorStake"
    [.variant 0 ValidatorStakeV1 .v1 fun
        | .v1 v => some v]

/-- `ValidatorStake::into_v1`. -/
def ValidatorStake.intoV1 : ValidatorStake → ValidatorStakeV1
  | .v1 v => v

/-- `compute_bp_hash_from_validator_stakes` with the versioned format: the hash of the Borsh
`Vec<ValidatorStake>`. -/
def bpHash (stakes : Array ValidatorStake) : CryptoHash :=
  CryptoHash.hashBorsh stakes

/-- `compute_bp_hash_from_validator_stakes` without the versioned format: the hash of the Borsh
`Vec<ValidatorStakeV1>`. -/
def bpHashV1 (stakes : Array ValidatorStake) : CryptoHash :=
  CryptoHash.hashBorsh (stakes.map ValidatorStake.intoV1)

/-- `SlashedValidator`. -/
structure SlashedValidator where
  accountId : AccountId
  isDoubleSign : Bool
  deriving BEq, Inhabited

instance : Codec SlashedValidator :=
  .iso (AccountId × Bool) (fun (a, d) => ⟨a, d⟩) fun x => (x.accountId, x.isDoubleSign)

/-- `SpiceChunkEndorsementStats`. -/
structure SpiceChunkEndorsementStats where
  produced : UInt32
  expected : UInt32
  deriving BEq, Inhabited

instance : Codec SpiceChunkEndorsementStats :=
  .iso (UInt32 × UInt32) (fun (p, e) => ⟨p, e⟩) fun x => (x.produced, x.expected)

/-- `TrieSplit`: a proposed shard split. -/
structure TrieSplit where
  boundaryAccount : AccountId
  leftMemory : UInt64
  rightMemory : UInt64
  deriving BEq, Inhabited

instance : Codec TrieSplit :=
  .iso (AccountId × UInt64 × UInt64) (fun (b, l, r) => ⟨b, l, r⟩) fun x =>
    (x.boundaryAccount, x.leftMemory, x.rightMemory)

end Near.Node
