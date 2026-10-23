import NearNode.Primitives.Validator
import NearNode.Primitives.Congestion

/-!
# Chunk extra

`near-primitives::types::chunk_extra` at `=0.37.4`: what a node stores about an applied chunk
(`ChunkExtra`, V1 to V5), also carried by spice execution results.
-/

namespace Near.Node

open Borsh

/-- `ChunkExtraV1`. -/
structure ChunkExtraV1 where
  stateRoot : CryptoHash
  outcomeRoot : CryptoHash
  validatorProposals : Array ValidatorStakeV1
  gasUsed : Gas
  gasLimit : Gas
  balanceBurnt : Balance
  deriving BEq, Inhabited

instance : Codec ChunkExtraV1 :=
  .iso (CryptoHash × CryptoHash × Array ValidatorStakeV1 × Gas × Gas × Balance)
    (fun (s, o, v, u, l, b) => ⟨s, o, v, u, l, b⟩) fun x =>
    (x.stateRoot, x.outcomeRoot, x.validatorProposals, x.gasUsed, x.gasLimit, x.balanceBurnt)

/-- `ChunkExtraV2`: versioned `ValidatorStake`. -/
structure ChunkExtraV2 where
  stateRoot : CryptoHash
  outcomeRoot : CryptoHash
  validatorProposals : Array ValidatorStake
  gasUsed : Gas
  gasLimit : Gas
  balanceBurnt : Balance
  deriving BEq, Inhabited

instance : Codec ChunkExtraV2 :=
  .iso (CryptoHash × CryptoHash × Array ValidatorStake × Gas × Gas × Balance)
    (fun (s, o, v, u, l, b) => ⟨s, o, v, u, l, b⟩) fun x =>
    (x.stateRoot, x.outcomeRoot, x.validatorProposals, x.gasUsed, x.gasLimit, x.balanceBurnt)

/-- `ChunkExtraV3`: adds congestion info. -/
structure ChunkExtraV3 where
  stateRoot : CryptoHash
  outcomeRoot : CryptoHash
  validatorProposals : Array ValidatorStake
  gasUsed : Gas
  gasLimit : Gas
  balanceBurnt : Balance
  congestionInfo : CongestionInfo
  deriving BEq, Inhabited

instance : Codec ChunkExtraV3 :=
  .iso (CryptoHash × CryptoHash × Array ValidatorStake × Gas × Gas × Balance × CongestionInfo)
    (fun (s, o, v, u, l, b, c) => ⟨s, o, v, u, l, b, c⟩) fun x =>
    (x.stateRoot, x.outcomeRoot, x.validatorProposals, x.gasUsed, x.gasLimit, x.balanceBurnt,
      x.congestionInfo)

/-- `ChunkExtraV4`: adds bandwidth requests. -/
structure ChunkExtraV4 where
  stateRoot : CryptoHash
  outcomeRoot : CryptoHash
  validatorProposals : Array ValidatorStake
  gasUsed : Gas
  gasLimit : Gas
  balanceBurnt : Balance
  congestionInfo : CongestionInfo
  bandwidthRequests : BandwidthRequests
  deriving BEq, Inhabited

instance : Codec ChunkExtraV4 :=
  .iso
    (CryptoHash ×
      CryptoHash × Array ValidatorStake × Gas × Gas × Balance × CongestionInfo × BandwidthRequests)
    (fun (s, o, v, u, l, b, c, r) => ⟨s, o, v, u, l, b, c, r⟩) fun x =>
    (x.stateRoot, x.outcomeRoot, x.validatorProposals, x.gasUsed, x.gasLimit, x.balanceBurnt,
      x.congestionInfo, x.bandwidthRequests)

/-- `ChunkExtraV5`: adds the proposed split. -/
structure ChunkExtraV5 where
  stateRoot : CryptoHash
  outcomeRoot : CryptoHash
  validatorProposals : Array ValidatorStake
  gasUsed : Gas
  gasLimit : Gas
  balanceBurnt : Balance
  congestionInfo : CongestionInfo
  bandwidthRequests : BandwidthRequests
  proposedSplit : Option TrieSplit
  deriving BEq, Inhabited

instance : Codec ChunkExtraV5 :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      Array ValidatorStake ×
      Gas × Gas × Balance × CongestionInfo × BandwidthRequests × Option TrieSplit)
    (fun (s, o, v, u, l, b, c, r, p) => ⟨s, o, v, u, l, b, c, r, p⟩) fun x =>
    (x.stateRoot, x.outcomeRoot, x.validatorProposals, x.gasUsed, x.gasLimit, x.balanceBurnt,
      x.congestionInfo, x.bandwidthRequests, x.proposedSplit)

/-- `ChunkExtra`. -/
inductive ChunkExtra where
  | v1 (c : ChunkExtraV1)
  | v2 (c : ChunkExtraV2)
  | v3 (c : ChunkExtraV3)
  | v4 (c : ChunkExtraV4)
  | v5 (c : ChunkExtraV5)
  deriving BEq, Inhabited

instance : Codec ChunkExtra :=
  .enum "ChunkExtra"
    [.variant 0 ChunkExtraV1 .v1 fun
        | .v1 c => some c
        | _ => none,
      .variant 1 ChunkExtraV2 .v2 fun
        | .v2 c => some c
        | _ => none,
      .variant 2 ChunkExtraV3 .v3 fun
        | .v3 c => some c
        | _ => none,
      .variant 3 ChunkExtraV4 .v4 fun
        | .v4 c => some c
        | _ => none,
      .variant 4 ChunkExtraV5 .v5 fun
        | .v5 c => some c
        | _ => none]

end Near.Node
