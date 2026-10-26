import NearNode.Rpc.Tx
import NearNode.Epoch

/-!
# `validators`

`EpochManager::get_validator_info` (`chain/epoch-manager/src/lib.rs`) behind `GetValidatorInfo` of the view
client:

* `EpochReference::Latest`, or the id of the epoch the head is in: the validators of the epoch with what each
  produced so far (the aggregate over the blocks of the epoch up to the head, `EpochInfoAggregator`);
* the id of an epoch that is over, or the block that ended one: the validators of that epoch with the statistics
  of its summary (`EpochSummary`, recomputed from the blocks of the epoch) and, as nearcore does, zeros for the
  per-shard numbers;
* the validators of the next epoch, the proposals, the kickouts of the previous epoch and the rewards paid at its
  start.
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

/-- What the validator did, per validator: the numbers of `CurrentEpochValidatorInfo`. -/
private structure Numbers where
  blocks : Nat × Nat := (0, 0)
  chunks : Nat × Nat := (0, 0)
  endorsements : Nat × Nat := (0, 0)
  /-- (shard, produced, expected) of the shards the validator produced in. -/
  producedShards : Array (UInt64 × Nat × Nat) := #[]
  /-- (shard, produced, expected) of the shards the validator endorsed in. -/
  endorsedShards : Array (UInt64 × Nat × Nat) := #[]
  deriving Inhabited

private def currentJson (v : ValidatorStake) (shards : Array UInt64) (n : Numbers) : Json :=
  Json.mkObj
    [("account_id", jacc v.accountId), ("public_key", jkey v.publicKey),
      ("is_slashed", Json.bool false), ("stake", jbal v.stake),
      ("shards", jarr (fun (x : UInt64) => jn x.toNat) shards),
      ("num_produced_blocks", jn n.blocks.1), ("num_expected_blocks", jn n.blocks.2),
      ("num_produced_chunks", jn n.chunks.1), ("num_expected_chunks", jn n.chunks.2),
      ("num_produced_chunks_per_shard",
        jarr (fun (x : UInt64 × Nat × Nat) => jn x.2.1) n.producedShards),
      ("num_expected_chunks_per_shard",
        jarr (fun (x : UInt64 × Nat × Nat) => jn x.2.2) n.producedShards),
      ("num_produced_endorsements", jn n.endorsements.1),
      ("num_expected_endorsements", jn n.endorsements.2),
      ("num_produced_endorsements_per_shard",
        jarr (fun (x : UInt64 × Nat × Nat) => jn x.2.1) n.endorsedShards),
      ("num_expected_endorsements_per_shard",
        jarr (fun (x : UInt64 × Nat × Nat) => jn x.2.2) n.endorsedShards),
      ("shards_endorsed", jarr (fun (x : UInt64 × Nat × Nat) => jn x.1.toNat) n.endorsedShards)]

/-- The shards a validator is a chunk producer of, from the settlement of the epoch. -/
private def shardsOf (view : EpochInfoView) (layout : ShardLayout) (i : Nat) : Array UInt64 :=
  (view.chunkProducers.toList.zipIdx.filterMap fun (vs, idx) =>
        if vs.contains i.toUInt64 then layout.getShardId idx else none).toArray.qsort
    (· < ·)

/-- The epoch a request names. -/
private inductive Which where
  | latest
  | epoch (id : EpochId)
  | block (b : BlockRec)

private def unavailable : RpcError :=
  RpcError.handler "VALIDATOR_INFO_UNAVAILABLE" none (Json.str "Validator info unavailable")

private def parseWhich (s : VState) (params : Json) : Except RpcError Which := do
  let ofBlockId (j : Json) : Except RpcError Which :=
    match parseBlockId j with
    | .error m => .error (RpcError.parse s!"Failed parsing args: {m}")
    | .ok r =>
      match resolve s r with
      | some b => pure (.block b)
      | none => throw (RpcError.handler "UNKNOWN_EPOCH" none (Json.str "Unknown Epoch"))
  match params with
  | .arr #[x] =>
    if x == Json.null then
      pure .latest
    else
      match x with
      | .str _ =>
        do
          pure (.epoch ⟨← liftParse (parseHash x)⟩)
      | _ =>
        ofBlockId x
  | .arr #[] | .null =>
    pure .latest
  | .obj _ =>
    if let some h := field? params "epoch_id" then
      do
        pure (.epoch ⟨← liftParse (parseHash h)⟩)
    else if let some b := field? params "block_id" then
      ofBlockId b
    else
      pure .latest
  | _ =>
    throw (RpcError.parse "Failed parsing args: invalid type, expected an epoch reference")

/-- The first and the last block of an epoch, on the chain the node holds. -/
private def epochEnds (s : VState) (id : EpochId) : Option (BlockRec × BlockRec) :=
  s.st.blocks.fold (init := none) fun best _ r =>
    if r.info.epochId == id && r.hash != CryptoHash.zero then
      match best with
      | none => some (r, r)
      | some (lo, hi) =>
        some
          (if r.view.height < lo.view.height then r else lo,
            if r.view.height > hi.view.height then r else hi)
    else best

def validators (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let unknownEpoch := RpcError.handler "UNKNOWN_EPOCH" none (Json.str "Unknown Epoch")
  let some tip := (s.st.block s.tip).toOption | return .error (RpcError.internal "no tip")
  match parseWhich s params with
  | .error e =>
    return .error e
  | .ok which =>
    let epochId? : Except RpcError (EpochId × Bool) :=
      match which with
      | .latest => pure (tip.view.epochId, true)
      | .epoch id => pure (id, id == tip.view.epochId)
      | .block b =>
        match s.canon[b.view.height + 1]? with
        | some next =>
          match s.st.block ⟨next⟩ with
          | .ok n =>
            if n.view.epochId != b.view.epochId && n.view.epochId == b.view.nextEpochId then
              pure (b.view.epochId, false)
            else throw unavailable
          | .error _ => throw unavailable
        | none => throw unavailable
    match epochId? with
    | .error e =>
      return .error e
    | .ok (id, isCurrent) =>
      let some epoch := (s.st.epoch id).toOption | return .error unknownEpoch
      let view := epoch.info.view
      let mut numbers : Array Numbers := Array.replicate view.validators.size {}
      let mut proposals : Array ValidatorStake := #[]
      let mut nextId : EpochId := tip.view.nextEpochId
      let some (_, last) := epochEnds s id | return .error unknownEpoch
      let first := (s.st.block last.info.epochFirstBlock).toOption.getD last
      if isCurrent then
        -- the aggregate over the blocks of the epoch so far
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
        nextId := (s.st.nextEpochIdOfInfo tip.info).toOption.getD tip.view.nextEpochId
        numbers :=
          view.validators.mapIdx fun i _ =>
            let perShard : List (UInt64 × ChunkSt) :=
              agg.shardTracker.toList.filterMap fun (shard, tracker) => (tracker[i]?).map (shard, ·)
            let produced :=
              (perShard.filter fun (_, st) => st.expected > 0).toArray.qsort fun a b => a.1 < b.1
            let endorsed :=
              (perShard.filter fun (_, st) => st.endorsementExpected > 0).toArray.qsort fun a b =>
                a.1 < b.1
            let sum (f : ChunkSt → Nat) : Nat := perShard.foldl (fun n (_, st) => n + f st) 0
            { blocks := (agg.blockTracker[i]?).getD (0, 0),
              chunks := (sum (·.produced), sum (·.expected)),
              endorsements := (sum (·.endorsementProduced), sum (·.endorsementExpected)),
              producedShards := produced.map fun (sh, st) => (sh, st.produced, st.expected),
              endorsedShards :=
                endorsed.map fun (sh, st) => (sh, st.endorsementProduced, st.endorsementExpected) }
        proposals := (agg.allProposals.qsort fun a b => a.1.val < b.1.val).map (·.2)
      else
        -- the summary of an epoch that is over; the numbers per shard are zeros, as nearcore's
        match collectBlocksInfo c.env.setup s.st last with
        | .error e =>
          return .error (RpcError.internal e.kind)
        | .ok summary =>
          nextId := ⟨summary.prevEpochLastBlockHash⟩
          proposals := summary.allProposals
          numbers :=
            view.validators.mapIdx fun i v =>
              let st := ((summary.stats.find? (·.1 == v.accountId)).map (·.2)).getD {}
              { blocks := (st.blockProduced, st.blockExpected),
                chunks := (st.chunkProduced, st.chunkExpected),
                endorsements := (st.endorsementProduced, st.endorsementExpected),
                producedShards := (shardsOf view epoch.layout i).map fun sh => (sh, 0, 0) }
      let some next := (s.st.epoch nextId).toOption | return .error unknownEpoch
      let nextView := next.info.view
      let current : Array Json :=
        view.validators.mapIdx fun i v =>
          let n := numbers[i]!
          let shards :=
            if isCurrent then n.producedShards.map (·.1) else shardsOf view epoch.layout i
          currentJson v shards n
      let nextValidators : Array Json :=
        nextView.validators.mapIdx fun i v =>
          Json.mkObj
            [("account_id", jacc v.accountId), ("public_key", jkey v.publicKey),
              ("stake", jbal v.stake),
              ("shards", jarr (fun (x : UInt64) => jn x.toNat) (shardsOf nextView next.layout i))]
      let kickout := nextView.validatorKickout.qsort fun a b => a.1.val < b.1.val
      let rewards := view.validatorReward.qsort fun a b => a.1.val < b.1.val
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
              ("epoch_start_height", jn first.view.height.toNat),
              ("epoch_height", jn view.epochHeight),
              ("validator_reward_paid_prev_epoch",
                Json.mkObj (rewards.toList.map fun (a, b) => (a.val, jbal b)))])

end Near.Node.Rpc
