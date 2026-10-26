import NearNode.Rpc.Errors
import NearNode.Chain.StateChanges
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

/-! ### EXPERIMENTAL_changes_in_block, EXPERIMENTAL_changes -/

/-- `RpcStateChangesError::UnknownBlock` as `HandlerError`: the cause and the data are both `{"info": {}, "name": "UNKNOWN_BLOCK"}`. -/
private def unknownStateChangesBlock (s : VState) (params : Json) : RpcError :=
  let cause := Json.mkObj [("info", Json.mkObj []), ("name", "UNKNOWN_BLOCK")]
  RpcError.handler "UNKNOWN_BLOCK" (some (Json.mkObj [])) cause (unknownBlockStatus s params)

/-- Every committed change of the block's chunks, over all shards, in the order of the raw trie keys (the keys of the
`StateChanges` column are `block hash ++ raw key`). -/
def blockChanges (s : VState) (b : BlockRec) : Array RawStateChangesWithTrieKey :=
  let shards :=
    ((epochDataOf s b).map fun e => e.layout.shardIds.map (blockShardKey b.hash e.layout ·)).getD #[]
  let all :=
    shards.foldl
      (fun acc key =>
        match s.pr.tables.get .stateChanges key with
        | some bytes => acc ++ (stateChangesOfBytes? bytes).getD #[]
        | none => acc)
      (#[] : Array RawStateChangesWithTrieKey)
  (all.map fun r => (TrieKey.toVec r.trieKey, r)).qsort (fun a b => keyLt a.1 b.1) |>.map (·.2)

/-- `EXPERIMENTAL_changes_in_block` / `block_effects` (`changes_in_block`, `GetStateChangesInBlock`,
`ChainStore::get_state_changes_in_block`): one entry for every trie key of the account, contract code, access key and contract data
kinds that the block's chunks committed, in key order (`StateChangesKinds::from_changes`). -/
def changesInBlock (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let ref : Except String BlockRef :=
    match params with
    | .obj _ => parseBlockRef params (flattened := true)
    | .null => throw "invalid type: null, expected struct RpcStateChangesInBlockRequest"
    | .arr _ => throw "invalid type: sequence, expected struct RpcStateChangesInBlockRequest"
    | _ => throw "invalid type, expected struct RpcStateChangesInBlockRequest"
  match liftParse ref with
  | .error e =>
    return .error e
  | .ok r =>
    match resolve s r with
    | none =>
      return .error (unknownStateChangesBlock s params)
    | some b =>
      let changes :=
        (blockChanges s b).filterMap fun r =>
          (kindOfTrieKey? r.trieKey).map fun (kind, account) =>
            Json.mkObj
              [("type",
                  match kind with
                  | .account => "account_touched"
                  | .accessKey => "access_key_touched"
                  | .data => "data_touched"
                  | .contractCode => "contract_code_touched"),
                ("account_id", jacc account)]
      return .ok (Json.mkObj [("block_hash", jhash b.hash), ("changes", Json.arr changes)])

/-- `StateChangesRequestView`. -/
inductive ChangesRequest where
  | account (ids : Array AccountId)
  | singleAccessKey (keys : Array (AccountId × PublicKey))
  | allAccessKeys (ids : Array AccountId)
  | contractCode (ids : Array AccountId)
  | data (ids : Array AccountId) (prefix_ : ByteArray)

private def accountList (o : Json) : Except String (Array AccountId) :=
  match field? o "account_ids" with
  | none => throw "missing field `account_ids`"
  | some (.arr xs) => xs.mapM parseAccount
  | some j => throw s!"invalid type: {serdeFound j}, expected a sequence"

private def keyList (o : Json) : Except String (Array (AccountId × PublicKey)) :=
  match field? o "keys" with
  | none => throw "missing field `keys`"
  | some (.arr xs) =>
    xs.mapM fun x =>
      match x with
      | .obj _ => do
        let some a := field? x "account_id" | throw "missing field `account_id`"
        let some k := field? x "public_key" | throw "missing field `public_key`"
        pure (← parseAccount a, ← parseKey k)
      | j => throw s!"invalid type: {serdeFound j}, expected struct AccountWithPublicKey"
  | some j => throw s!"invalid type: {serdeFound j}, expected a sequence"

/-- The `changes_type` of a request (`StateChangesRequestView`, tagged by `changes_type`). -/
def parseChangesRequest (o : Json) : Except String ChangesRequest := do
  let some t := field? o "changes_type" | throw "missing field `changes_type`"
  let variants := #["account_changes", "single_access_key_changes", "all_access_key_changes", "contract_code_changes", "data_changes"]
  -- serde reads a variant from its name or from its index
  let t ←
    match t with
    | .num n =>
      if n.exponent == 0 && n.mantissa ≥ 0 then
        match variants[n.mantissa.toNat]? with
        | some name => pure (Json.str name)
        | none => throw s!"invalid value: integer `{n.mantissa}`, expected variant index 0 <= i < {variants.size}"
      else throw s!"invalid type: {serdeFound t}, expected variant identifier"
    | .str _ => pure t
    | j => throw s!"invalid type: {serdeFound j}, expected variant identifier"
  match t with
  | .str "account_changes" => .account <$> accountList o
  | .str "single_access_key_changes" => .singleAccessKey <$> keyList o
  | .str "all_access_key_changes" => .allAccessKeys <$> accountList o
  | .str "contract_code_changes" => .contractCode <$> accountList o
  | .str "data_changes" =>
    let ids ← accountList o
    match field? o "key_prefix_base64" with
    | some (.str p) => pure (.data ids (← base64Decode p))
    | some j => throw s!"invalid type: {serdeFound j}, expected a string"
    | none => throw "missing field `key_prefix_base64`"
  | .str other =>
    throw
      s!"unknown variant `{other}`, expected one of `account_changes`, `single_access_key_changes`, `all_access_key_changes`, `contract_code_changes`, `data_changes`"
  | _ => throw "unreachable"

/-- `StateChangeCauseView`. -/
def causeView : StateChangeCause → Json
  | .notWritableToDisk => Json.mkObj [("type", "not_writable_to_disk")]
  | .initialState => Json.mkObj [("type", "initial_state")]
  | .transactionProcessing h => Json.mkObj [("type", "transaction_processing"), ("tx_hash", jhash h)]
  | .actionReceiptProcessingStarted h =>
    Json.mkObj [("type", "action_receipt_processing_started"), ("receipt_hash", jhash h)]
  | .actionReceiptGasReward h =>
    Json.mkObj [("type", "action_receipt_gas_reward"), ("receipt_hash", jhash h)]
  | .receiptProcessing h => Json.mkObj [("type", "receipt_processing"), ("receipt_hash", jhash h)]
  | .postponedReceipt h => Json.mkObj [("type", "postponed_receipt"), ("receipt_hash", jhash h)]
  | .updatedDelayedReceipts => Json.mkObj [("type", "updated_delayed_receipts")]
  | .validatorAccountsUpdate => Json.mkObj [("type", "validator_accounts_update")]
  | .migration => Json.mkObj [("type", "migration")]
  | .unusedReshardingV2 | .bandwidthSchedulerStateUpdate =>
    Json.mkObj [("type", "bandwidth_scheduler_state_update")]

private def handleKey : PublicKeyHandle → PublicKey
  | .ed25519 k => .ed25519 k
  | .secp256k1 k => .secp256k1 k
  | .mldsa65 k => .mldsa65 k

/-- The object of a change: the `account_id` and the fields of `view` (`#[serde(flatten)]` of an `AccountView`). -/
private def withFields (base : List (String × Json)) (view : Json) : Json :=
  match view with
  | .obj kvs => Json.mkObj (base ++ kvs.toList)
  | _ => Json.mkObj base

/-- `StateChangeWithCauseView` of one committed change of a key (`StateChanges::from_changes`): `none` for a key the RPC does not
serve, a deletion of a gas key nonce (only its deletion together with the key is possible, and it is not reported) or a value that
does not decode. -/
def changeView (key : TrieKey) (c : RawStateChange) : Option Json :=
  let wrap (type : String) (change : Json) : Json :=
    Json.mkObj [("cause", causeView c.cause), ("type", type), ("change", change)]
  match key with
  | .account a =>
    match c.data with
    | some d =>
      match Codec.decodeAll (α := Account) d with
      | .ok acc => some (wrap "account_update" (withFields [("account_id", jacc a)] (accountView acc)))
      | .error _ => none
    | none => some (wrap "account_deletion" (Json.mkObj [("account_id", jacc a)]))
  | .accessKey a h =>
    match c.data with
    | some d =>
      match Codec.decodeAll (α := AccessKey) d with
      | .ok k =>
        some
          (wrap "access_key_update"
            (Json.mkObj
              [("account_id", jacc a), ("public_key", jkey (handleKey h)), ("access_key", accessKeyView k)]))
      | .error _ => none
    | none =>
      some
        (wrap "access_key_deletion"
          (Json.mkObj [("account_id", jacc a), ("public_key", jkey (handleKey h))]))
  | .gasKeyNonce a h i =>
    match c.data with
    | some d =>
      match Codec.decodeAll (α := UInt64) d with
      | .ok n =>
        some
          (wrap "gas_key_nonce_update"
            (Json.mkObj
              [("account_id", jacc a), ("public_key", jkey (handleKey h)), ("index", jn i.toNat),
                ("nonce", jn n.toNat)]))
      | .error _ => none
    | none => none
  | .contractData a k =>
    match c.data with
    | some v =>
      some
        (wrap "data_update"
          (Json.mkObj [("account_id", jacc a), ("key_base64", base64Encode k), ("value_base64", base64Encode v)]))
    | none =>
      some (wrap "data_deletion" (Json.mkObj [("account_id", jacc a), ("key_base64", base64Encode k)]))
  | .contractCode a =>
    match c.data with
    | some v =>
      some (wrap "contract_code_update" (Json.mkObj [("account_id", jacc a), ("code_base64", base64Encode v)]))
    | none => some (wrap "contract_code_deletion" (Json.mkObj [("account_id", jacc a)]))
  | _ => none

/-- Whether `p` is a prefix of `k`. -/
private def hasPrefix (k p : ByteArray) : Bool :=
  k.size ≥ p.size && k.extract 0 p.size == p

/-- `ChainStore::get_state_changes`: for each member of the request in order, the changes of the keys it selects, key by key in key
order and each key's changes in the order of the commits. -/
def selectChanges (records : Array RawStateChangesWithTrieKey) (req : ChangesRequest) : Array Json :=
  let keyed := records.map fun r => (TrieKey.toVec r.trieKey, r)
  let render (rs : Array (ByteArray × RawStateChangesWithTrieKey)) : Array Json :=
    rs.foldl
      (fun acc (_, r) => acc ++ r.changes.filterMap (changeView r.trieKey))
      #[]
  let exact (k : ByteArray) := render (keyed.filter fun (rk, _) => rk == k)
  let byPrefix (p : ByteArray) := render (keyed.filter fun (rk, _) => hasPrefix rk p)
  let accessPrefix (a : AccountId) : ByteArray :=
    (TrieKey.toVec (.accessKey a (.ed25519 (ByteArray.mk (Array.replicate 32 0))))).extract 0
      (a.val.toUTF8.size + 2)
  match req with
  | .account ids => ids.foldl (fun acc a => acc ++ exact (TrieKey.toVec (.account a))) #[]
  | .contractCode ids => ids.foldl (fun acc a => acc ++ exact (TrieKey.toVec (.contractCode a))) #[]
  | .allAccessKeys ids => ids.foldl (fun acc a => acc ++ byPrefix (accessPrefix a)) #[]
  | .singleAccessKey keys =>
    keys.foldl
      (fun acc (a, pk) =>
        match handleOfKey pk with
        | some h => acc ++ byPrefix (TrieKey.toVec (.accessKey a h))
        | none => acc)
      #[]
  | .data ids p =>
    ids.foldl
      (fun acc a => acc ++ byPrefix (TrieKey.toVec (.contractData a ByteArray.empty) ++ p))
      #[]

/-- `EXPERIMENTAL_changes` / `changes` (`changes_in_block_by_type`, `GetStateChanges`): the values of the account, access key, contract
code and contract data keys that the block's chunks committed, each with the cause of the commit. -/
def changesByType (c : Ctx) (params : Json) : IO R := do
  let s ← c.env.get
  let parsed : Except String (BlockRef × ChangesRequest) :=
    match params with
    | .obj _ => do
      let r ← parseBlockRef params (flattened := true)
      pure (r, ← parseChangesRequest params)
    | .null => throw "invalid type: null, expected struct RpcStateChangesInBlockByTypeRequest"
    | .arr _ => throw "invalid type: sequence, expected struct RpcStateChangesInBlockByTypeRequest"
    | _ => throw "invalid type, expected struct RpcStateChangesInBlockByTypeRequest"
  match liftParse parsed with
  | .error e =>
    return .error e
  | .ok (r, req) =>
    match resolve s r with
    | none =>
      return .error (unknownStateChangesBlock s params)
    | some b =>
      let changes := selectChanges (blockChanges s b) req
      return .ok (Json.mkObj [("block_hash", jhash b.hash), ("changes", Json.arr changes)])

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
