import NearNode.Chain.StateDecode
import NearNode.Trie
import NearNode.Chain.Profile
import ChainReplay.ShardChunk
import ChainReplay.DelegateSignature
import ChainReplay.HostCrypto
import NearRuntime.TransactionRegistry
import NearRuntime.ReceiptRegistry

/-!
# Applying a chunk with the runtime

One chunk of one shard: the shard's entries and the chunk's transactions, incoming receipts and
block context go through the runtime as `ChainReplay.Registered.run` runs a block (the validator
accounts update, the transaction registry, `Near.step`, the receipt queues, the bandwidth scheduler
and the receipt sink), and what `Runtime::apply` returns comes out: outcomes, outgoing receipts,
the new entries, gas, proposals, congestion info and bandwidth requests.
-/

namespace Near.Node.Apply

open Near.Node Near.Node.Borsh

/-- The block-level inputs of a chunk (`ApplyChunkBlockContext`, `ApplyState`). -/
structure ChunkContext where
  protocol : Nat
  height : Nat
  timestamp : Nat
  epochHeight : Nat
  gasPrice : Nat
  gasLimit : Nat
  randomSeed : List UInt8
  chainId : String
  shardId : Nat
  shardIds : List Nat
  epochInfo : Near.EpochInfo
  update : Option Near.ValidatorAccountsUpdate
  /-- The scheduler's view of the network (`ChainReplay.ShardChunk.Input`). -/
  scheduler : ChainReplay.ShardChunk.Input

/-- The failure of an outcome: the runtime's model says that the execution failed (and why, in its own words), and
the outcome root only depends on that (`PartialExecutionStatus::Failure`). The `TxExecutionError` tree of nearcore
(which action failed and with what) is not reproduced; this value stands for it and survives a round trip through
Borsh, unlike `default` (whose account id is empty). -/
def placeholderFailure : TxExecutionError :=
  .actionError
    ⟨none, .functionCallError (.executionError "the failure is not detailed by the node")⟩

/-- What applying a chunk produced. -/
structure ChunkResult where
  /-- The entries of the shard after the chunk. -/
  entries : Array (ByteArray × ByteArray)
  /-- The Borsh `ExecutionOutcomeWithId` fields needed for the outcome root and the checks. -/
  outcomes : Array ExecutionOutcomeWithId
  /-- The outgoing receipts as Borsh, in `ApplyResult` order. -/
  outgoing : Array ByteArray
  gasBurnt : Nat
  balanceBurnt : Nat
  proposals : Array ValidatorStake
  congestion : CongestionInfo
  requests : BandwidthRequests
  delayedCount : Nat
  schedulerHash : ByteArray
  /-- The hashes of the chunk's transactions, in order. -/
  txHashes : Array ByteArray

private def bytesOf (l : List UInt8) : ByteArray :=
  ⟨l.toArray⟩

/-- Borsh of `Vec<ValidatorStake>` (`ApplyResult::validator_proposals`). -/
private def proposalsOf (proposals : List Near.ValidatorProposal) :
    Except String (Array ValidatorStake) := do
  let mut out : Array ValidatorStake := #[]
  for p in proposals do
    unless p.stake < 2 ^ 128 do
      throw "validator stake exceeds u128"
    let key ←
      match Codec.decodeAll (α := PublicKey) (bytesOf p.publicKey) with
      | .ok k =>
        pure k
      | .error e =>
        throw s!"proposal key: {repr e}"
    out := out.push (.v1 ⟨⟨p.account⟩, key, ⟨p.stake⟩⟩)
  return out

/-- The trie of a shard's stored state as the runtime's storage accounting reads it
(`TrieOverlay.start` builds the same from the entries; this reads the objects the node holds). -/
def overlayOf (src : Near.Node.Trie.NodeSource) (root : CryptoHash)
    (entries : Array (ByteArray × ByteArray)) : Except String Near.TrieOverlay.State := do
  let (usage, objects) ← Near.Node.Trie.objects src root
  pure
      { entries := entries.toList.map fun (k, v) => (k.toList, v.toList),
        base :=
          { root := root.bytes.toList, memoryUsage := usage.toNat,
            witness := objects.toList.map fun (h, b) => (h.bytes.toList, b.toList) } }

/-- Everything the runtime consumes for one chunk, converted. -/
structure Prepared where
  codes : ChainReplay.Catalogue
  initial : Near.Snapshot
  context : Near.QueueEncoding.Context
  shard : ChainReplay.ShardChunk.State
  block : Near.Block
  hashes : List (List UInt8)

/-- The context of the conversion for the `QueueEncoding`. -/
def contextOf (conv : Conv) (delayed : Option Near.QueueEncoding.Delayed) :
    Except String Near.QueueEncoding.Context := do
  let data ←
    conv.dataBindings.toList.mapM fun (id, hash) => do
        let some receiver := conv.dataReceivers[hash]?
          | throw "data identity ownership is unavailable"
        pure ({ id, hash := hash.toList, receiver } : Near.QueueEncoding.DataIdentity)
  pure
      { receipts := conv.receiptBindings.toList.map fun (id, h) => (id, h.toList), data,
        formats := conv.formats.toList, delayed }

/-- Convert a chunk's inputs. `pending` are the incoming receipts in apply order. -/
def prepare (entries : Array (ByteArray × ByteArray)) (txs : Array SignedTransaction)
    (pending : Array Receipt) (claimed : Array ByteArray) (ctx : ChunkContext) (cache : CodeCache) :
    Except String (Prepared × CodeCache) := do
  let (result, conv) ←
    (do
            let d ← decodeState entries
            let mut transactions : List Near.Transaction := []
            let mut hashes : List (List UInt8) := []
            for t in txs do
              let (tx, h) ← transaction t
              transactions := transactions ++ [tx]
              hashes := hashes ++ [h]
            let mut incoming : List Near.Receipt := []
            for r in pending do
              incoming := incoming ++ [(← receipt r).1]
            pure (d, transactions, hashes, incoming) : M _).run
        { cache }
  let (d, transactions, hashes, incoming) := result
  let context ← contextOf conv d.delayed
  let scheduler ←
    match d.scheduler with
    | none =>
      pure ({} : Near.Bandwidth.State)
    | some raw =>
      Near.Bandwidth.State.ofBorsh raw
  let buffers ← Near.ShardSink.Buffers.ofEntries d.buffers
  -- Code a contract deploys from its own memory is in no input; the receipts the chunk's producer
  -- says it sent carry it, and the runtime must produce the same receipts.
  let mut scratch := conv
  for raw in claimed do
    if let .ok r := Codec.decodeAll (α := Receipt) raw then
      if let .ok (_, c) := (receipt r).run scratch then
        scratch :=
          { scratch with
            cache := c.cache, used := c.used }
  let cache := scratch.cache
  -- the catalogue holds the code this chunk uses, not every code seen so far: the encoders look
  -- codes up by hash
  let codes : ChainReplay.Catalogue := scratch.used.toList.filterMap (cache[·]?)
  let state := { d.state with nextId := conv.next }
  let ap : Near.ApplyState :=
    { blockHeight := ctx.height, blockTimestamp := ctx.timestamp, epochHeight := ctx.epochHeight,
      gasPrice := ctx.gasPrice, randomSeed := ctx.randomSeed, gasLimit := some ctx.gasLimit,
      chainId := ctx.chainId, epochInfo := ctx.epochInfo, shardId := ctx.shardId,
      shardIds := ctx.shardIds }
  pure
      ({ codes, initial := { state, pending := incoming }, context, shard := { scheduler, buffers },
         block := { ap, txs := transactions }, hashes },
        conv.cache)

/-- The entries a prepared chunk encodes back to: the round trip of the conversion. -/
def reencode (cfg : Wasm.Near.RuntimeConfig) (p : Prepared) :
    Except String (List (List UInt8 × List UInt8)) := do
  let catalogue := p.codes.map fun c => (c.code.hash, c.bytes)
  let entries ← Near.QueueEncoding.encode p.initial.state catalogue p.context (some cfg) digest
  let shard ← p.shard.entries
  pure (entries ++ shard)

/-- Run a prepared chunk (one block of `Registered.run`). Each stage is charged to `prof` under the
name `run/...`. -/
def runChunk (prof : Option Prof) (cfg : Wasm.Near.RuntimeConfig)
    (congestion : Near.Congestion.Config) (ctx : ChunkContext) (p : Prepared)
    (overlay : Option Near.TrieOverlay.State) : AM ChunkResult := do
  let catalogue := p.codes.map fun c => (c.code.hash, c.bytes)
  let mut snapshot := p.initial
  if let some update := ctx.update then
    snapshot ←
      timed prof "run/accounts-update" fun _ => do
          pure { snapshot with state := ← update.apply snapshot.state }
  -- the trie of the state the chunk starts from: the node's own when the state is the one it stores
  -- (not after the epoch's accounts update), otherwise built from the encoded state
  let trie ←
    timed prof "run/shard-start" fun _ =>
        match overlay with
        | some o => pure o
        | none => do
          Near.TrieOverlay.start
              ((← Near.QueueEncoding.encode snapshot.state catalogue p.context (some cfg) digest) ++
                (← p.shard.entries))
  let inputs :=
    (p.block.txs.zip p.hashes).map fun (transaction, blockHash) =>
      ({ transaction, blockHash } : Near.TransactionRegistry.Input)
  let admitted ←
    timed prof "run/transaction-registry" fun _ =>
        Near.TransactionRegistry.observe cfg p.block.ap catalogue snapshot.state inputs p.context
          (preflight := false)
  let block :=
    { p.block with
      ap :=
        { p.block.ap with
          nativeReceiptHashes := some admitted.context.receipts, storageAccounting := some trie,
          verifyDelegate := ChainReplay.DelegateSignature.verify catalogue } }
  let (next, result) ←
    timed prof "run/interpreter" fun _ =>
        match Near.step cfg (ChainReplay.codeOf p.codes) snapshot block with
        | .error e => throw s!"invalid receipt schedule: {repr e}"
        | .ok r => pure r
  if let some issue := result.issue then
    throw s!"model execution issue: {issue.2.message}"
  let context ←
    timed prof "run/observe-queues" fun _ =>
        Near.ReceiptRegistry.observeQueues cfg catalogue block.ap.blockHeight snapshot.state result
          admitted.context
  let sent ←
    timed prof "run/outgoing-receipts" fun _ =>
        result.outgoing.mapM fun receipt => do
          pure
              (receipt.receiptId,
                ({  bytes := ← Near.QueueEncoding.receiptBytes context catalogue receipt
                    gas := Near.QueueEncoding.congestionGas cfg receipt } :
                  ChainReplay.ShardChunk.Sent))
  let change ←
    timed prof "run/delayed-queue" fun _ => do
        let oldForms := (p.context.delayed.map (·.forms)).getD []
        let mut change : ChainReplay.ShardChunk.DelayedChange := {}
        for (receipt, form) in (snapshot.state.delayed.zip oldForms).take result.delayedConsumed do
          let (gas, size) ←
            match form with
            | .storedV0 gas size | .storedV1 gas size =>
              pure (gas, size)
            | .receipt =>
              pure
                  (Near.QueueEncoding.congestionGas cfg receipt,
                    (← Near.QueueEncoding.receiptBytes p.context catalogue receipt).length)
            | .newStored =>
              throw "a pre-state delayed receipt cannot be newly stored"
          change :=
            { change with
              removedGas := change.removedGas + gas, removedBytes := change.removedBytes + size }
        let newForms :=
          ((context.delayed.map (·.forms)).getD []).drop (oldForms.length - result.delayedConsumed)
        for form in newForms do
          match form with
          | .storedV0 gas size | .storedV1 gas size =>
            change :=
              { change with
                addedGas := change.addedGas + gas, addedBytes := change.addedBytes + size }
          | _ =>
            throw "an appended delayed receipt must be stored with its metadata"
        pure change
  let outcome ←
    timed prof "run/scheduler" fun _ =>
        ChainReplay.ShardChunk.finish congestion ctx.scheduler block.ap.shardId block.ap.blockHeight
          p.shard (sent.map (·.2)) change
  let stateEntries ←
    timed prof "run/encode-state" fun _ =>
        Near.QueueEncoding.encode next.state catalogue context (some cfg) digest
  let shardEntries ← timed prof "run/encode-shard" fun _ => outcome.state.entries
  timed prof "run/results" fun _ => do
      -- the outcomes with the native ids of their receipts
      let native (id : Nat) : Except String CryptoHash :=
        match context.receipts.find? (·.1 == id) with
        | some (_, h) => pure ⟨bytesOf h⟩
        | none => throw s!"outcome of receipt {id} has no native id"
      let txHashes := admitted.attempts.toArray.map fun a => bytesOf a.hash
      let mut outcomes : Array ExecutionOutcomeWithId := #[]
      for ((id, o), index) in result.outcomes.zipIdx do
        let identity ←
          if h : index < txHashes.size then
            pure (CryptoHash.mk txHashes[index])
          else
            native id
        let status : ExecutionStatus ←
          match o.status with
          | .successValue v =>
            pure (.successValue (bytesOf v))
          | .successReceiptId r =>
            pure (.successReceiptId (← native r))
          | .failure _ =>
            pure (.failure placeholderFailure)
        outcomes :=
          outcomes.push
            { id := identity,
              outcome :=
                { logs := o.logs.toArray, receiptIds := (← o.receiptIds.mapM native).toArray,
                  gasBurnt := o.gasBurnt.toUInt64, tokensBurnt := ⟨o.tokensBurnt⟩,
                  executorId := ⟨o.executorId⟩, status, metadata := default } }
      let info ←
        match Codec.decodeAll (α := CongestionInfo) (bytesOf outcome.info.toBorsh) with
        | .ok i =>
          pure i
        | .error e =>
          throw s!"congestion info: {repr e}"
      let requests ←
        match
          Codec.decodeAll (α := BandwidthRequests)
            (bytesOf (Near.Bandwidth.requestsToBorsh outcome.requests)) with
        | .ok i =>
          pure i
        | .error e =>
          throw s!"bandwidth requests: {repr e}"
      let proposals ← proposalsOf (Near.uniqueProposals result.proposals)
      pure
          {
            entries :=
              (stateEntries ++ shardEntries).toArray.map fun (k, v) => (bytesOf k, bytesOf v),
            outcomes, outgoing := outcome.outgoing.toArray.map bytesOf,
            gasBurnt := result.outcomes.foldl (fun s (_, o) => s + o.gasBurnt) 0,
            balanceBurnt := result.tokensBurnt - result.subsidizedAmount, proposals,
            congestion := info, requests, delayedCount := next.state.delayed.length,
            schedulerHash := bytesOf outcome.schedulerHash, txHashes }

/-- A chunk that is not new (`apply_old_chunk`): no transaction or receipt is applied, but the
epoch's validator accounts update and the bandwidth scheduler still run
(`Runtime::apply` with `is_new_chunk = false`). Returns the entries of the shard afterwards. -/
def runOldChunk (cfg : Wasm.Near.RuntimeConfig) (congestion : Near.Congestion.Config)
    (ctx : ChunkContext) (p : Prepared) : Except String (Array (ByteArray × ByteArray)) := do
  let catalogue := p.codes.map fun c => (c.code.hash, c.bytes)
  let mut snapshot := p.initial
  unless snapshot.pending.isEmpty && p.block.txs.isEmpty do
    throw "an old chunk applies no transactions or receipts"
  if let some update := ctx.update then
    snapshot := { snapshot with state := ← update.apply snapshot.state }
  let input := ctx.scheduler
  let layout := input.layout
  let params := Near.Bandwidth.Params.protocol layout.numShards congestion.maxReceiptSize
  let status :=
    input.congestion.map fun (id, c) => (id, ChainReplay.ShardChunk.shardStatus congestion layout c)
  let scheduled :=
    Near.Bandwidth.schedule layout p.shard.scheduler params input.requests status
      input.prevBlockHash
  let stateEntries ← Near.QueueEncoding.encode snapshot.state catalogue p.context (some cfg) digest
  let shardEntries ←
    ({ p.shard with scheduler := scheduled.state } : ChainReplay.ShardChunk.State).entries
  pure ((stateEntries ++ shardEntries).toArray.map fun (k, v) => (bytesOf k, bytesOf v))

end Near.Node.Apply
