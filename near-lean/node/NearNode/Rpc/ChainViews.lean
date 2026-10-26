import NearNode.Rpc.Views
import NearNode.Validator.Drive

/-!
# Blocks, chunks and the chain they are read from

`BlockView`, `BlockHeaderView`, `ChunkHeaderView` and `ChunkView` of `near-primitives::views`, the block
references of `near_primitives::types::BlockReference` (`block_id`, `finality`, `sync_checkpoint`), and
the lookups of `ViewClientActor` over the validator's state.
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Chain Near.Node.Network Near.Node.Validator

/-! ### Dates -/

/-- `YYYY-MM-DDTHH:MM:SS.nnnnnnnnnZ` (`near_time::serde_utc_as_iso`) of nanoseconds since the epoch. -/
def isoOfNanos (ns : Nat) : String :=
  let secs := ns / 1_000_000_000
  let nanos := ns % 1_000_000_000
  let days := secs / 86400
  let rem := secs % 86400
  -- civil from days (Howard Hinnant)
  let z := days + 719468
  let era := z / 146097
  let doe := z % 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let y := yoe + era * 400
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let m := if mp < 10 then mp + 3 else mp - 9
  let y := if m ≤ 2 then y + 1 else y
  let pad (n w : Nat) : String :=
    let s := toString n
    String.ofList (List.replicate (w - s.length) '0') ++ s
  s!"{pad y 4}-{pad m 2}-{pad d 2}T{pad (rem / 3600) 2}:{pad (rem % 3600 / 60) 2}:{pad (rem % 60) 2}.{pad nanos 9}Z"

/-! ### Views -/

def congestionView (c : CongestionInfo) : Json :=
  let .v1 i := c
  Json.mkObj
    [("delayed_receipts_gas", jbal i.delayedReceiptsGas),
      ("buffered_receipts_gas", jbal i.bufferedReceiptsGas),
      ("receipt_bytes", jn i.receiptBytes.toNat), ("allowed_shard", jn i.allowedShard.toNat)]

def bandwidthView (r : BandwidthRequests) : Json :=
  let .v1 x := r
  tagged "V1"
    (Json.mkObj
      [("requests",
          jarr
            (fun (q : BandwidthRequest) =>
              Json.mkObj
                [("to_shard", jn q.toShard.toNat),
                  ("requested_values_bitmap",
                    Json.mkObj
                      [("data",
                          jarr (fun (b : UInt8) => jn b.toNat)
                            (q.requestedValuesBitmap.data.toList.toArray))])])
            x.requests)])

def splitView (s : TrieSplit) : Json :=
  Json.mkObj
    [("boundary_account", jacc s.boundaryAccount), ("left_memory", jn s.leftMemory.toNat),
      ("right_memory", jn s.rightMemory.toNat)]

/-- `ChunkHeaderView`. -/
def chunkHeaderView (h : ShardChunkHeader) : Json :=
  let inner : Option (CongestionInfo × BandwidthRequests × Option (Option TrieSplit) × UInt64) :=
    match h with
    | .v3 ⟨.v5 i, _, _⟩ =>
      some (i.congestionInfo, i.bandwidthRequests, some i.proposedSplit, i.encodedLength)
    | .v3 ⟨.v4 i, _, _⟩ => some (i.congestionInfo, i.bandwidthRequests, none, i.encodedLength)
    | _ => none
  let base : List (String × Json) :=
    [("chunk_hash", jhash h.chunkHash.hash), ("prev_block_hash", jhash h.prevBlockHash),
      ("outcome_root", jhash h.prevOutcomeRoot), ("prev_state_root", jhash h.prevStateRoot),
      ("encoded_merkle_root", jhash h.encodedMerkleRoot),
      ("encoded_length", jn ((inner.map (·.2.2.2.toNat)).getD 0)),
      ("height_created", jn h.heightCreated.toNat), ("height_included", jn h.heightIncluded.toNat),
      ("shard_id", jn h.shardId.toNat), ("gas_used", jn h.prevGasUsed.toNat),
      ("gas_limit", jn h.gasLimit.toNat), ("rent_paid", Json.str "0"),
      ("validator_reward", Json.str "0"), ("balance_burnt", jbal h.prevBalanceBurnt),
      ("outgoing_receipts_root", jhash h.prevOutgoingReceiptsRoot), ("tx_root", jhash h.txRoot),
      ("validator_proposals", jarr validatorStakeView h.prevValidatorProposals),
      ("congestion_info",
        jopt (fun (c : CongestionInfo × _) => congestionView c.1) (inner.map fun x => (x.1, ()))),
      ("bandwidth_requests",
        jopt (fun (r : BandwidthRequests × _) => bandwidthView r.1)
          (inner.map fun x => (x.2.1, ()))),
      ("signature", jsig h.signature)]
  let split : List (String × Json) :=
    match inner with
    | some (_, _, some s, _) => [("proposed_split", jopt splitView s)]
    | _ => []
  Json.mkObj (base ++ split)

/-- `BlockHeaderView`. -/
def headerView (hash : CryptoHash) (v : HeaderView) : Json :=
  let chunksIncluded := v.chunkMask.foldl (fun n b => if b then n + 1 else n) 0
  Json.mkObj
    [("height", jn v.height.toNat), ("prev_height", jn v.prevHeight.toNat),
      ("epoch_id", jhash v.epochId.hash), ("next_epoch_id", jhash v.nextEpochId.hash),
      ("hash", jhash hash), ("prev_hash", jhash v.prevHash),
      ("prev_state_root", jhash v.prevStateRoot), ("block_body_hash", jhash v.blockBodyHash),
      ("chunk_receipts_root", jhash v.prevChunkOutgoingReceiptsRoot),
      ("chunk_headers_root", jhash v.chunkHeadersRoot), ("chunk_tx_root", jhash v.chunkTxRoot),
      ("outcome_root", jhash v.prevOutcomeRoot), ("chunks_included", jn chunksIncluded),
      ("challenges_root", jhash CryptoHash.zero), ("timestamp", jn v.timestamp.toNat),
      ("timestamp_nanosec", Json.str (toString v.timestamp)), ("random_value", jhash v.randomValue),
      ("validator_proposals", jarr validatorStakeView v.prevValidatorProposals),
      ("chunk_mask", jarr Json.bool v.chunkMask), ("gas_price", jbal v.nextGasPrice),
      ("block_ordinal", if v.blockOrdinal == 0 then Json.null else jn v.blockOrdinal.toNat),
      ("rent_paid", Json.str "0"), ("validator_reward", Json.str "0"),
      ("total_supply", jbal v.totalSupply), ("challenges_result", Json.arr #[]),
      ("last_final_block", jhash v.lastFinalBlock),
      ("last_ds_final_block", jhash v.lastDsFinalBlock), ("next_bp_hash", jhash v.nextBpHash),
      ("block_merkle_root", jhash v.blockMerkleRoot),
      ("epoch_sync_data_hash", jopt jhash v.epochSyncDataHash),
      ("approvals", jarr (jopt jsig) v.approvals), ("signature", jsig v.signature),
      ("latest_protocol_version", jn v.latestProtocolVersion.toNat),
      ("chunk_endorsements",
        jopt
          (fun (b : ChunkEndorsementsBitmap) =>
            jarr (fun (x : ByteArray) => jarr (fun (y : UInt8) => jn y.toNat) x.toList.toArray)
              b.inner)
          v.chunkEndorsements),
      ("shard_split",
        jopt (fun (p : ShardId × AccountId) => Json.arr #[jn p.1.toNat, jacc p.2]) v.shardSplit)]

/-! ### Looking things up -/

/-- A reference to a block in a request. -/
inductive BlockRef where
  | optimistic
  | nearFinal
  | final
  | height (h : Nat)
  | hash (h : CryptoHash)
  | genesis
  | earliest
  deriving BEq

/-- Why a block could not be found, as `GetBlockError::UnknownBlock` words it. -/
def BlockRef.unknownMessage : BlockRef → String
  | .height h => s!"BLOCK HEIGHT: {h}"
  | .hash h => s!"BLOCK: {base58Encode h.bytes}"
  | _ => "BLOCK"

/-- The applied block a reference names, on the chain of the tip. -/
def resolve (s : VState) (r : BlockRef) : Option BlockRec :=
  let ofHash (h : CryptoHash) : Option BlockRec :=
    if s.applied.contains h.bytes then (s.st.block h).toOption else none
  match r with
  | .optimistic => ofHash s.tip
  | .nearFinal => (ofHash s.tip).bind fun b => ofHash b.view.lastDsFinalBlock
  | .final => (ofHash s.tip).bind fun b => ofHash b.view.lastFinalBlock
  | .height n => (s.canon[n.toUInt64]?).bind fun h => ofHash ⟨h⟩
  | .hash h => ofHash h
  | .genesis | .earliest => ofHash s.st.genesisHash

/-- `BlockView` of an applied block. -/
def blockView (s : VState) (b : Block) : Json :=
  match b.header.view? with
  | none => Json.null
  | some v =>
    let author : Json :=
      match s.st.blockProducer v.epochId v.height with
      | .ok p => jacc p.accountId
      | .error _ => Json.null
    Json.mkObj
      [("author", author), ("header", headerView b.header.hash v),
        ("chunks", jarr chunkHeaderView b.chunks)]

/-- The author of a chunk: its producer at the height it was created. -/
def chunkAuthor (s : VState) (h : ShardChunkHeader) : Json :=
  match s.st.epochIdFromPrevBlock h.prevBlockHash with
  | .ok epoch =>
    match s.st.chunkProducer epoch h.heightCreated h.shardId with
    | .ok p => jacc p.accountId
    | .error _ => Json.null
  | .error _ =>
    -- the genesis chunks
    match s.st.chunkProducer ⟨CryptoHash.zero⟩ h.heightCreated h.shardId with
    | .ok p => jacc p.accountId
    | .error _ => Json.null

end Near.Node.Rpc
