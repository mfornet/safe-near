import NearNode.Rpc.Tx
import NearNode.Epoch

/-!
# `validators`

`EpochManager::get_validator_info` for the latest epoch (`EpochReference::Latest`, or the id of the
current epoch): the validators of the epoch with what each produced so far (the aggregate over the blocks
of the epoch up to the head, `EpochInfoAggregator`), the validators of the next epoch, the proposals, the
kickouts of the previous epoch and the rewards paid at its start.
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Network Near.Node.Validator
  Near.Node.Epoch

private def kickoutJson : ValidatorKickoutReason → Json
  | .unusedSlashed => Json.str "_UnusedSlashed"
  | .notEnoughBlocks p e =>
    tagged "NotEnoughBlocks" (Json.mkObj [("produced", jn p.toNat), ("expected", jn e.toNat)])
  | .notEnoughChunks p e =>
    tagged "NotEnoughChunks" (Json.mkObj [("produced", jn p.toNat), ("expected", jn e.toNat)])
  | .unstaked => Json.str "Unstaked"
  | .notEnoughStake s t =>
    tagged "NotEnoughStake" (Json.mkObj [("stake_u128", jbal s), ("threshold_u128", jbal t)])
  | .didNotGetASeat => Json.str "DidNotGetASeat"
  | .notEnoughChunkEndorsements p e =>
    tagged "NotEnoughChunkEndorsements"
      (Json.mkObj [("produced", jn p.toNat), ("expected", jn e.toNat)])
  | .protocolVersionTooOld v n =>
    tagged "ProtocolVersionTooOld"
      (Json.mkObj [("version", jn v.toNat), ("network_version", jn n.toNat)])

private def sortedNats (xs : List Nat) : List Nat :=
  xs.mergeSort (· ≤ ·)

def validators (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let ok : Except String Unit :=
    match params with
    | .arr #[x] => if x == Json.null then pure () else throw "unsupported"
    | .arr #[] | .null => pure ()
    | .obj _ => pure ()
    | _ => throw "invalid type"
  -- an explicit epoch must be the current one
  let current : Bool :=
    match params with
    | .obj _ =>
      match field? params "epoch_id" with
      | some h =>
        (parseHash h).toOption.any fun h =>
          s.st.block s.tip |>.toOption.any fun t => t.view.epochId.hash == h
      | none => true
    | _ => true
  let unknownEpoch := RpcError.handler "UNKNOWN_EPOCH" none (Json.str "Unknown Epoch")
  match ok, current with
  | .error _, _ =>
    -- an epoch given by block: the node tells it has no such summary
    return .error
        (RpcError.handler "VALIDATOR_INFO_UNAVAILABLE" none (Json.str "Validator info unavailable"))
  | _, false =>
    return .error unknownEpoch
  | _, _ =>
    let some tip := (s.st.block s.tip).toOption | return .error (RpcError.internal "no tip")
    let some epoch :=
      (s.st.epoch tip.info.epochId).toOption | return .error (RpcError.internal "no epoch")
    let view := epoch.info.view
    -- the aggregate over the blocks of the epoch
    let mut agg : Aggregator := {}
    match s.st.epochBlocks tip with
    | .error e =>
      return .error (RpcError.internal e.kind)
    | .ok blocks =>
      for (b, prevHeight) in blocks do
        match agg.updateTail b.info epoch.info epoch.layout prevHeight with
        | .ok a =>
          agg := a
        | .error m =>
          return .error (RpcError.internal m)
    let nextId := (s.st.nextEpochIdOfInfo tip.info).toOption
    let some next := nextId.bind fun id => (s.st.epoch id).toOption | return .error unknownEpoch
    let nextView := next.info.view
    let current : Array Json :=
      view.validators.mapIdx fun i v =>
        let (bp, be) := (agg.blockTracker[i]?).getD (0, 0)
        let perShard : List (UInt64 × ChunkSt) :=
          agg.shardTracker.toList.filterMap fun (shard, tracker) => (tracker[i]?).map (shard, ·)
        let producedShards :=
          (perShard.filter fun (_, st) => st.expected > 0).map (·.1) |>.toArray.qsort (· < ·)
        let endorsedShards :=
          (perShard.filter fun (_, st) => st.endorsementExpected > 0).map (·.1) |>.toArray.qsort
            (· < ·)
        let stat (shard : UInt64) : ChunkSt := (perShard.find? (·.1 == shard)).map (·.2) |>.getD {}
        let sum (f : ChunkSt → Nat) : Nat := perShard.foldl (fun n (_, st) => n + f st) 0
        Json.mkObj
          [("account_id", jacc v.accountId), ("public_key", jkey v.publicKey),
            ("is_slashed", Json.bool false), ("stake", jbal v.stake),
            ("shards", jarr (fun (x : UInt64) => jn x.toNat) producedShards),
            ("num_produced_blocks", jn bp), ("num_expected_blocks", jn be),
            ("num_produced_chunks", jn (sum (·.produced))),
            ("num_expected_chunks", jn (sum (·.expected))),
            ("num_produced_chunks_per_shard",
              jarr (fun (x : UInt64) => jn (stat x).produced) producedShards),
            ("num_expected_chunks_per_shard",
              jarr (fun (x : UInt64) => jn (stat x).expected) producedShards),
            ("num_produced_endorsements", jn (sum (·.endorsementProduced))),
            ("num_expected_endorsements", jn (sum (·.endorsementExpected))),
            ("num_produced_endorsements_per_shard",
              jarr (fun (x : UInt64) => jn (stat x).endorsementProduced) endorsedShards),
            ("num_expected_endorsements_per_shard",
              jarr (fun (x : UInt64) => jn (stat x).endorsementExpected) endorsedShards),
            ("shards_endorsed", jarr (fun (x : UInt64) => jn x.toNat) endorsedShards)]
    let nextValidators : Array Json :=
      nextView.validators.mapIdx fun i v =>
        let shards : List Nat :=
          (nextView.chunkProducers.toList.zipIdx.filterMap fun (vs, idx) =>
            if vs.contains i.toUInt64 then (next.layout.getShardId idx).map (·.toNat) else none)
        Json.mkObj
          [("account_id", jacc v.accountId), ("public_key", jkey v.publicKey),
            ("stake", jbal v.stake), ("shards", Json.arr (sortedNats shards |>.map jn |>.toArray))]
    let proposals := (agg.allProposals.qsort fun a b => a.1.val < b.1.val).map (·.2)
    let kickout := nextView.validatorKickout.qsort fun a b => a.1.val < b.1.val
    let rewards := view.validatorReward.qsort fun a b => a.1.val < b.1.val
    let first := (s.st.block tip.info.epochFirstBlock).toOption
    return .ok
        (Json.mkObj
          [("current_validators", Json.arr current), ("next_validators", Json.arr nextValidators),
            ("current_fishermen", Json.arr #[]), ("next_fishermen", Json.arr #[]),
            ("current_proposals", jarr validatorStakeView proposals),
            ("prev_epoch_kickout",
              jarr
                (fun (k : AccountId × ValidatorKickoutReason) =>
                  Json.mkObj [("account_id", jacc k.1), ("reason", kickoutJson k.2)])
                kickout),
            ("epoch_start_height", jn ((first.map (·.view.height.toNat)).getD 0)),
            ("epoch_height", jn view.epochHeight),
            ("validator_reward_paid_prev_epoch",
              Json.mkObj (rewards.toList.map fun (a, b) => (a.val, jbal b)))])

end Near.Node.Rpc
