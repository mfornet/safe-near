import NearNode.Rpc.Errors
import NearNode.Rpc.StateViews
import NearNode.Protocol

/-!
# The read methods of the JSON-RPC API

`status`, `health`, `gas_price`, `block`, `chunk`, `query` (the view requests),
`EXPERIMENTAL_genesis_config`, `EXPERIMENTAL_protocol_config`, over a snapshot of the validator's state
(`VState` is immutable: a request sees one consistent state). The shapes are those of
`chain/jsonrpc/src/api/*.rs` and `chain/jsonrpc-primitives/src/types/*.rs` at the pinned nearcore.
-/

namespace Near.Node.Rpc

open Lean Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Network Near.Node.Validator
  Near.Node.Apply

/-- What the methods need from the running node. -/
structure Ctx where
  env : Validator.Env
  rpcAddr : String
  startedMs : Nat
  /-- `genesis.json` without the records: `EXPERIMENTAL_genesis_config`. -/
  genesisConfig : Json
  /-- The `runtime_config` of `EXPERIMENTAL_protocol_config`. -/
  runtimeConfig : Json
  /-- The node's peer public key and validator key text. -/
  nodeKey : PublicKey

/-! ### Block references -/

/-- `BlockReference` from the members of a request object; `flattened` when it is a part of a larger request
(a query), which changes the words of the error when it is missing. -/
def parseBlockRef (o : Json) (flattened : Bool := false) : Except String BlockRef := do
  if let some f := field? o "finality" then
    match f with
    | .str "final" =>
      pure .final
    | .str "near-final" =>
      pure .nearFinal
    | .str "optimistic" =>
      pure .optimistic
    | _ =>
      throw "unknown variant of finality, expected one of `optimistic`, `near-final`, `final`"
  else if let some b := field? o "block_id" then
    match b with
    | .num n =>
      match b.getNat? with
      | .ok k =>
        pure (.height k)
      | .error _ =>
        throw s!"invalid value: {n}, expected u64"
    | .str _ =>
      match parseHash b with
      | .ok h =>
        pure (.hash h)
      | .error _ =>
        throw "data did not match any variant of untagged enum BlockId"
    | _ =>
      throw "data did not match any variant of untagged enum BlockId"
  else if let some c := field? o "sync_checkpoint" then
    match c with
    | .str "genesis" =>
      pure .genesis
    | .str "earliest_available" =>
      pure .earliest
    | _ =>
      throw "unknown variant of sync_checkpoint"
  else if flattened then
    throw "no variant of enum BlockReference found in flattened data"
  else
    match o with
    | .obj kvs =>
      match kvs.toList.head? with
      | some (k, _) =>
        if kvs.size == 1 then
          throw s!"unknown variant `{k}`, expected one of `block_id`, `finality`, `sync_checkpoint`"
        else
          throw "invalid value: map, expected map with a single key"
      | none =>
        throw "invalid value: map, expected map with a single key"
    | _ =>
      throw "invalid type, expected a block reference"

/-- `BlockId` from a bare value (the `[block_id]` form). -/
def parseBlockId (j : Json) : Except String BlockRef :=
  match j with
  | .num _ =>
    match j.getNat? with
    | .ok k => pure (.height k)
    | .error _ => throw "data did not match any variant of untagged enum BlockId"
  | .str _ => do
    pure (.hash (← parseHash j))
  | _ => throw "data did not match any variant of untagged enum BlockId"

/-- The status 422 that goes with an unknown block below the head (`handle_unknown_block`). -/
def unknownBlockStatus (s : VState) (params : Json) : Nat :=
  match field? params "block_id" with
  | some b =>
    match b.getNat? with
    | .ok h => if h < s.tipHeight.toNat then 422 else 200
    | .error _ => 200
  | none => 200

def unknownBlock (s : VState) (params : Json) (r : BlockRef) : RpcError :=
  RpcError.handler "UNKNOWN_BLOCK" (some (Json.mkObj []))
    (Json.str s!"DB Not Found Error: {r.unknownMessage} \n Cause: Unknown")
    (unknownBlockStatus s params)

/-! ### status, health, gas_price -/

private def versionJson : Json :=
  Json.mkObj
    [("version", nearcoreRelease), ("build", "near-lean-node"),
      ("commit", "44f7ae6cd7ef08bab604e20a473bf77e35d4c993"), ("rustc_version", "lean-4.34.1")]

def epochDataOf (s : VState) (b : BlockRec) : Option EpochData :=
  (s.st.epoch b.view.epochId).toOption

def status (c : Ctx) : IO Json := do
  let s ← c.env.get
  let some tip := (s.st.block s.tip).toOption | return Json.null
  let v := tip.view
  let now ← IO.monoMsNow
  let epochStart : Json :=
    match s.st.block tip.info.epochFirstBlock with
    | .ok first => jn first.view.height.toNat
    | .error _ => Json.null
  let validators : Json :=
    match s.st.blockProducersOrdered v.epochId with
    | .ok vs => jarr (fun (x : ValidatorStake) => Json.mkObj [("account_id", jacc x.accountId)]) vs
    | .error _ => Json.arr #[]
  let genesis := (s.st.block s.st.genesisHash).toOption
  let protocol := (epochDataOf s tip).map fun e => e.info.protocolVersion.toNat
  return Json.mkObj
      [("version", versionJson), ("chain_id", c.env.params.chainId),
        ("protocol_version", jn (protocol.getD Near.Node.protocolVersion)),
        ("latest_protocol_version", jn Near.Node.protocolVersion), ("rpc_addr", c.rpcAddr),
        ("validators", validators),
        ("sync_info",
          Json.mkObj
            [("latest_block_hash", jhash tip.hash), ("latest_block_height", jn v.height.toNat),
              ("latest_state_root", jhash v.prevStateRoot),
              ("latest_block_time", isoOfNanos v.timestamp.toNat), ("syncing", Json.bool false),
              ("earliest_block_hash", jopt (fun (g : BlockRec) => jhash g.hash) genesis),
              ("earliest_block_height",
                jopt (fun (g : BlockRec) => jn g.view.height.toNat) genesis),
              ("earliest_block_time",
                jopt (fun (g : BlockRec) => Json.str (isoOfNanos g.view.timestamp.toNat)) genesis),
              ("epoch_id", jhash v.epochId.hash), ("epoch_start_height", epochStart)]),
        ("validator_account_id", jacc c.env.me),
        ("validator_public_key", jkey c.env.signer.publicKey), ("node_public_key", jkey c.nodeKey),
        ("node_key", jkey c.env.signer.publicKey), ("uptime_sec", jn ((now - c.startedMs) / 1000)),
        ("genesis_hash", jhash s.st.genesisHash)]

def gasPrice (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let ref : Except String (Option BlockRef) :=
    match params with
    | .arr #[x] => if x == Json.null then pure none else some <$> parseBlockId x
    | .arr #[] => pure none
    | .obj _ =>
      match field? params "block_id" with
      | some x => if x == Json.null then pure none else some <$> parseBlockId x
      | none => pure none
    | _ => throw "invalid type: expected a sequence or a map"
  match liftParse ref with
  | .error e =>
    return .error e
  | .ok r =>
    let r' := r.getD .optimistic
    match resolve s r' with
    | some b =>
      return .ok (Json.mkObj [("gas_price", jbal b.view.nextGasPrice)])
    | none =>
      let e := unknownBlock s params r'
      let fix (m : String) : String :=
        match r' with
        | .hash _ => m.replace "BLOCK:" "BLOCK HEADER:"
        | _ => m
      return .error
          { e with
            error :=
              e.error.setObjVal! "data"
                (Json.str (fix ((e.error.getObjValD "data").getStr?.toOption.getD ""))) }

/-! ### block and chunk -/

def block (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let ref : Except String BlockRef :=
    match params with
    | .arr #[x] => parseBlockId x
    | .obj _ => parseBlockRef params
    | .null => throw "invalid type: null, expected string or map"
    | _ => throw "invalid type: sequence, expected string or map"
  match liftParse ref with
  | .error e =>
    return .error e
  | .ok r =>
    match resolve s r with
    | some b =>
      match s.blocks[b.hash.bytes]? with
      | some full =>
        return .ok (blockView s full)
      | none =>
        return .error (unknownBlock s params r)
    | none =>
      return .error (unknownBlock s params r)

private def chunkViewJson (s : VState) (header : ShardChunkHeader) (body : TransactionReceipt) :
    Json :=
  Json.mkObj
    [("author", chunkAuthor s header), ("header", chunkHeaderView header),
      ("transactions", jarr signedTransactionView body.transactions),
      ("receipts", jarr receiptView body.receipts)]

def chunk (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  -- the reference: a chunk hash, or a block and a shard
  let parsed : Except String (Sum CryptoHash (BlockRef × Nat)) :=
    match params with
    | .arr #[.arr #[b, sh]] => do
      pure (.inr (← parseBlockId b, ← parseU64 sh))
    | .arr #[h] => do
      pure (.inl (← parseHash h))
    | .obj _ =>
      match field? params "chunk_id" with
      | some h => do
        pure (.inl (← parseHash h))
      | none =>
        match field? params "block_id", field? params "shard_id" with
        | some b, some sh => do
          pure (.inr (← parseBlockId b, ← parseU64 sh))
        | _, _ => throw "data did not match any variant of untagged enum ChunkReference"
    | _ => throw "invalid type, expected a chunk reference"
  match liftParse parsed with
  | .error e =>
    return .error e
  | .ok (.inl h) =>
    match s.chunks[h.bytes]? with
    | some entry =>
      match entry.header, entry.body with
      | some header, some body =>
        return .ok (chunkViewJson s (header.withHeightIncluded 0) body)
      | _, _ =>
        return .error
            (RpcError.handler "UNKNOWN_CHUNK" (some (Json.mkObj [("chunk_hash", jhash h)]))
              (Json.str
                s!"Chunk Missing (unavailable on the node): ChunkHash(`{base58Encode h.bytes}`) \n Cause: Unknown"))
    | none =>
      -- the chunks of the genesis block have no body
      match s.st.genesisChunks.find? (·.chunkHash.hash == h) with
      | some header =>
        return .ok (chunkViewJson s (header.withHeightIncluded 0) ⟨#[], #[]⟩)
      | none =>
        return .error
            (RpcError.handler "UNKNOWN_CHUNK" (some (Json.mkObj [("chunk_hash", jhash h)]))
              (Json.str
                s!"Chunk Missing (unavailable on the node): ChunkHash(`{base58Encode h.bytes}`) \n Cause: Unknown"))
  | .ok (.inr (r, shard)) =>
    match resolve s r with
    | none =>
      return .error (unknownBlock s params r)
    | some b =>
      match (epochDataOf s b).bind fun e => e.layout.getShardIndex shard.toUInt64 with
      | none =>
        return .error
            (RpcError.handler "INVALID_SHARD_ID" (some (Json.mkObj [("shard_id", jn shard)]))
              (Json.str s!"Shard id {shard} does not exist"))
      | some i =>
        match b.chunks[i]? with
        | none =>
          return .error
              (RpcError.handler "INVALID_SHARD_ID" (some (Json.mkObj [("shard_id", jn shard)]))
                (Json.str s!"Shard id {shard} does not exist"))
        | some header =>
          match (s.chunks[header.chunkHash.hash.bytes]?).bind (·.body) with
          | some body =>
            return .ok (chunkViewJson s header body)
          | none =>
            -- a chunk of the genesis, or one that was not new: an empty body
            if header.isGenesis || header.heightIncluded != b.view.height then
              return .ok (chunkViewJson s header ⟨#[], #[]⟩)
            else
              return .error
                  (RpcError.handler "UNKNOWN_CHUNK"
                    (some (Json.mkObj [("chunk_hash", jhash header.chunkHash.hash)]))
                    (Json.str
                      s!"Chunk Missing (unavailable on the node): ChunkHash(`{base58Encode header.chunkHash.hash.bytes}`) \n Cause: Unknown"))

/-! ### Genesis and protocol configuration -/

def genesisConfig (c : Ctx) : Json :=
  c.genesisConfig

def protocolConfig (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let ref : Except String BlockRef :=
    match params with
    | .obj _ => parseBlockRef params
    | .arr #[x] => parseBlockId x
    | _ => throw "invalid type, expected a block reference"
  match liftParse ref with
  | .error e =>
    return .error e
  | .ok r =>
    match resolve s r with
    | none =>
      let e := unknownBlock s params r
      return .error
          { e with
            error := e.error.setObjVal! "data" (Json.str s!"Block Not Found: {r.unknownMessage}") }
    | some _ =>
      let keep :=
        ["block_producer_kickout_threshold", "chain_id", "chunk_producer_kickout_threshold",
          "chunk_validator_only_kickout_threshold", "dynamic_resharding", "epoch_length",
          "fishermen_threshold", "gas_limit", "gas_price_adjustment_rate", "genesis_height",
          "genesis_time", "max_gas_price", "max_inflation_rate", "max_kickout_stake_perc",
          "min_gas_price", "minimum_stake_divisor", "minimum_stake_ratio",
          "minimum_validators_per_shard", "num_block_producer_seats", "num_blocks_per_year",
          "online_max_threshold", "online_min_threshold", "protocol_reward_rate",
          "protocol_treasury_account", "protocol_upgrade_stake_threshold", "protocol_version",
          "shard_layout", "shuffle_shard_assignment_for_chunk_producers",
          "target_validator_mandates_per_shard", "transaction_validity_period"]
      let fields := keep.filterMap fun k => (field? c.genesisConfig k).map fun v => (k, v)
      return .ok (Json.mkObj (fields ++ [("runtime_config", c.runtimeConfig)]))

end Near.Node.Rpc
