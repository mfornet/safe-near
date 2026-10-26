import NearNode.Chain.StateDecode
import NearNode.Trie
import NearNode.Chain.Profile
import NearNode.Chain.FastEngine
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

/-- The `TxExecutionError` of a failed receipt, for the errors of an action that nearcore's views render by value
(`ActionError` with the failed action's index); `placeholderFailure` for the others, which the RPC marks as not rendered. -/
def failureOf (index : Option Nat) (e : Near.RuntimeError) : TxExecutionError :=
  let acc (a : Near.AccountId) : AccountId := ⟨a⟩
  let key (k : Near.PublicKey) : Option PublicKey :=
    match Codec.decodeAll (α := PublicKey) (ByteArray.mk k.toArray) with
    | .ok p => some p
    | .error _ => none
  let kind? : Option ActionErrorKind :=
    match e with
    | .accountAlreadyExists id => some (.accountAlreadyExists (acc id))
    | .accountDoesNotExist id => some (.accountDoesNotExist (acc id))
    | .createAccountNotAllowed id p => some (.createAccountNotAllowed (acc id) (acc p))
    | .createAccountOnlyByRegistrar id r p =>
      some (.createAccountOnlyByRegistrar (acc id) (acc r) (acc p))
    | .actorNoPermission id a => some (.actorNoPermission (acc id) (acc a))
    | .deleteKeyDoesNotExist id k => (key k).map (.deleteKeyDoesNotExist (acc id) ·)
    | .addKeyAlreadyExists id k => (key k).map (.addKeyAlreadyExists (acc id) ·)
    | .deleteAccountStaking id => some (.deleteAccountStaking (acc id))
    | .lackBalanceForState id n => some (.lackBalanceForState (acc id) ⟨n⟩)
    | .triesToUnstake id => some (.triesToUnstake (acc id))
    | .triesToStake id s l b => some (.triesToStake (acc id) ⟨s⟩ ⟨l⟩ ⟨b⟩)
    | .insufficientStake id s m => some (.insufficientStake (acc id) ⟨s⟩ ⟨m⟩)
    | .deleteAccountWithLargeState id => some (.deleteAccountWithLargeState (acc id))
    | .onlyImplicitAccountCreationAllowed id => some (.onlyImplicitAccountCreationAllowed (acc id))
    | .delegateActionInvalidSignature => some .delegateActionInvalidSignature
    | .delegateActionSenderDoesNotMatchTxReceiver s r =>
      some (.delegateActionSenderDoesNotMatchTxReceiver (acc s) (acc r))
    | .delegateActionExpired => some .delegateActionExpired
    | .delegateActionInvalidNonce d a => some (.delegateActionInvalidNonce d.toUInt64 a.toUInt64)
    | .delegateActionNonceTooLarge d u => some (.delegateActionNonceTooLarge d.toUInt64 u.toUInt64)
    | .functionCallError (.methodResolveError m) =>
      some
        (.functionCallError
          (.methodResolveError
            (match m with
            | .methodEmptyName => .methodEmptyName
            | .methodNotFound => .methodNotFound
            | .methodInvalidSignature => .methodInvalidSignature)))
    | .functionCallError (.hostError .badUTF16) =>
      -- the model's text lacks the final full stop of `HostError::BadUTF16`
      some (.functionCallError (.executionError "String encoding is bad UTF-16 sequence."))
    | .functionCallError (.hostError h) =>
      some (.functionCallError (.executionError (Wasm.Near.FunctionCallError.hostError h).message))
    | .functionCallError (.wasmTrap t) =>
      some (.functionCallError (.executionError (Wasm.Near.FunctionCallError.wasmTrap t).message))
    | _ => none
  match kind?, index with
  | some k, some i => .actionError ⟨some i.toUInt64, k⟩
  | _, _ => placeholderFailure

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
  /-- The yielded receipts the chunk stored (`promise_yield_create`), which no chunk sends: the RPC serves
  them as the receipts of the outcomes they get later. -/
  yielded : Array ByteArray := #[]
  /-- The code a contract deployed from its own memory in this chunk (`stepLearning`). -/
  learned : Array ChainReplay.LoadedCode := #[]
  /-- The commits of the chunk that touch an account, access key, contract code or contract data key, in the order
  `Runtime::apply` makes them: the epoch's validator accounts update, then what `Near.apply` logged. -/
  changes : List Near.StateChange := []

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
    (entries : Array (ByteArray × ByteArray)) (cache : CodeCache) :
    Except String (Near.TrieOverlay.State × CodeCache) := do
  let (usage, objects) ← Near.Node.Trie.objects src root
  let mut c := cache
  let mut es : Array (List UInt8 × List UInt8) := #[]
  for (k, v) in entries do
    let (l, c') := c.list v
    c := c'
    es := es.push (k.toList, l)
  let mut witness : Array (List UInt8 × List UInt8) := #[]
  for (h, b) in objects do
    let (l, c') := c.list b
    c := c'
    witness := witness.push (h.bytes.toList, l)
  pure
      ({ entries := es.toList,
         base :=
           { root := root.bytes.toList, memoryUsage := usage.toNat, witness := witness.toList } },
        c)

/-! ### Code a contract deploys from its own memory

A function call can emit `DeployContract` with bytes it assembled in its own memory. They are in no input
of the chunk: not in the state, not in the incoming receipts, and the receipt that carries them is only
produced by this very call. A follower has them from the next chunk (`claimed`), but a validator applying
a block at the head does not. The runtime hands the decoder (`Bytes → ContractCode`) those bytes and keeps
only its answer, so the decoder is the one place where they are visible, and a pure function has no other
way out than the value it returns.

The step therefore runs with a decoder that knows the catalogue and, for bytes it does not know, answers
with a code that carries a model issue (the runtime then rejects the whole attempt atomically, `Near.apply`)
whose text holds the bytes. The node reads them off the issue, adds them to the catalogue exactly as it adds
the code of an incoming receipt (`Model.code`), and runs the step again; bytes already known are answered
from the catalogue, so each run gets one deployment further. -/

/-- Starts the text of the issue that hands bytes to the node. -/
def undeclaredMarker : String :=
  "safe-near undeclared contract code:"

private def hexDigit (n : UInt8) : Char :=
  if n < 10 then Char.ofNat (48 + n.toNat) else Char.ofNat (87 + n.toNat)

/-- Lowercase hexadecimal text of bytes. -/
def hexOfBytes (b : List UInt8) : String :=
  b.foldl (fun (s : String) (x : UInt8) => (s.push (hexDigit (x >>> 4))).push (hexDigit (x &&& 15)))
    ""

private def hexValue? (c : Char) : Option UInt8 :=
  if '0' ≤ c && c ≤ '9' then some (UInt8.ofNat (c.toNat - 48))
  else if 'a' ≤ c && c ≤ 'f' then some (UInt8.ofNat (c.toNat - 87)) else none

/-- The bytes of the hexadecimal digits that start `s` (up to the first other character). -/
def bytesOfHexPrefix (s : String) : ByteArray :=
  Id.run do
    let mut out : ByteArray := ByteArray.empty
    let mut high : Option UInt8 := none
    for c in s.toList do
      match hexValue? c with
      | none =>
        break
      | some d =>
        match high with
        | none =>
          high := some d
        | some h =>
          out := out.push (h <<< 4 ||| d)
          high := none
    return out

/-- The decoder of a run that learns the code a contract deploys: the catalogue's code for bytes it holds, an
issue that carries the bytes otherwise. -/
def learningCodeOf (codes : ChainReplay.Catalogue) (blob : Near.Bytes) : Near.ContractCode :=
  match codes.find? (·.bytes == blob) with
  | some entry => entry.code
  | none =>
    { module := default, size := blob.length, hash := "",
      decodeIssue := some (.interpreterError (undeclaredMarker ++ hexOfBytes blob)) }

/-- The bytes an issue of `learningCodeOf` carries, if it is one. -/
def undeclaredBytes? (message : String) : Option ByteArray :=
  match message.splitOn undeclaredMarker with
  | [_, rest] => some (bytesOfHexPrefix rest)
  | _ => none

/-- The most deployments of distinct code one chunk may make from contract memory. -/
def maxLearnedCodes : Nat :=
  256

/-- `Near.step` with `learningCodeOf`: whenever the run stops at bytes it has not seen, they join the
catalogue (and the cache) and the step runs again. Returns the catalogue it ended with and the codes it
learned. -/
def stepLearning [Near.VmEngine] (cfg : Wasm.Near.RuntimeConfig) (codes : ChainReplay.Catalogue)
    (cache : CodeCache) (snapshot : Near.Snapshot) (block : Near.Block) :
    Nat →
      Except String
        (ChainReplay.Catalogue × Array ChainReplay.LoadedCode × Near.Snapshot × Near.ApplyResult)
  | 0 => throw "a chunk deploys too many contracts from contract memory"
  | fuel + 1 =>
    match Near.step cfg (learningCodeOf codes) snapshot block with
    | .error e => throw s!"invalid receipt schedule: {repr e}"
    | .ok (next, result) =>
      match result.issue.bind (fun (_, issue) => undeclaredBytes? issue.message) with
      | none => pure (codes, #[], next, result)
      | some blob =>
        match (code blob).run { cache } with
        | .error e => throw e
        | .ok (entry, conv) => do
          let (codes', learned, next, result) ←
            stepLearning cfg (codes ++ [entry]) conv.cache snapshot block fuel
          pure (codes', #[entry] ++ learned, next, result)

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
  let codes : ChainReplay.Catalogue := scratch.used.toList.filterMap (cache.byLabel[·]?)
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
  let entries ←
    Near.QueueEncoding.encode p.initial.state catalogue p.context (some cfg) (digestFor catalogue)
  let shard ← p.shard.entries
  pure (entries ++ shard)

/-- Run a prepared chunk (one block of `Registered.run`). Each stage is charged to `prof` under the
name `run/...`. -/
def runChunk (prof : Option Prof) (cfg : Wasm.Near.RuntimeConfig)
    (congestion : Near.Congestion.Config) (ctx : ChunkContext) (p : Prepared)
    (overlay : Option Near.TrieOverlay.State) (cache : CodeCache := {}) : AM ChunkResult := do
  let catalogue := p.codes.map fun c => (c.code.hash, c.bytes)
  let known := cache.lists.toArray
  let mut snapshot := p.initial
  let mut updateChanges : List Near.StateChange := []
  if let some update := ctx.update then
    let before := snapshot.state
    snapshot ←
      timed prof "run/accounts-update" fun _ => do
          pure { snapshot with state := ← update.apply snapshot.state }
    updateChanges := update.changes before snapshot.state
  -- the trie of the state the chunk starts from: the node's own when the state is the one it stores
  -- (not after the epoch's accounts update), otherwise built from the encoded state
  let trie ←
    timed prof "run/shard-start" fun _ =>
        match overlay with
        | some o => pure o
        | none => do
          Near.TrieOverlay.start
              ((←
                  Near.QueueEncoding.encode snapshot.state catalogue p.context (some cfg)
                      (digestFor catalogue)) ++
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
  let (codes, learned, next, result) ←
    timed prof "run/interpreter" fun _ =>
        stepLearning cfg p.codes cache snapshot block maxLearnedCodes
  if let some issue := result.issue then
    throw s!"model execution issue: {issue.2.message}"
  -- the code the contracts of this chunk deployed from their memory is in the catalogue from here on
  let catalogue := codes.map fun c => (c.code.hash, c.bytes)
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
  -- the yielded receipts this chunk created (they are not in the outgoing receipts)
  let yielded : Array ByteArray :=
    ((next.state.yieldReceipts.filter fun (k, _) =>
            (snapshot.state.yieldReceipts.find? (·.1 == k)).isNone).filterMap
        fun (_, receipt) =>
        match Near.QueueEncoding.receiptBytes context catalogue receipt with
        | .ok b => some (bytesOf b)
        | .error _ => none).toArray
  let outcome ←
    timed prof "run/scheduler" fun _ =>
        ChainReplay.ShardChunk.finish congestion ctx.scheduler block.ap.shardId block.ap.blockHeight
          p.shard (sent.map (·.2)) change
  let stateEntries ←
    timed prof "run/encode-state" fun _ =>
        Near.QueueEncoding.encode next.state catalogue context (some cfg) (digestFor catalogue)
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
          | .failure e =>
            pure (.failure (failureOf o.failureIndex e))
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
              (stateEntries ++ shardEntries).toArray.map fun (k, v) =>
                (bytesOf k, CodeCache.bytesOf known v),
            outcomes, outgoing := outcome.outgoing.toArray.map bytesOf,
            gasBurnt := result.outcomes.foldl (fun s (_, o) => s + o.gasBurnt) 0,
            balanceBurnt := result.tokensBurnt - result.subsidizedAmount, proposals,
            congestion := info, requests, delayedCount := next.state.delayed.length,
            schedulerHash := bytesOf outcome.schedulerHash, txHashes, yielded, learned,
            changes := updateChanges ++ result.changes }

/-- A chunk that is not new (`apply_old_chunk`): no transaction or receipt is applied, but the
epoch's validator accounts update and the bandwidth scheduler still run
(`Runtime::apply` with `is_new_chunk = false`). Returns the entries of the shard afterwards. -/
def runOldChunk (cfg : Wasm.Near.RuntimeConfig) (congestion : Near.Congestion.Config)
    (ctx : ChunkContext) (p : Prepared) :
    Except String (Array (ByteArray × ByteArray) × List Near.StateChange) := do
  let catalogue := p.codes.map fun c => (c.code.hash, c.bytes)
  let mut snapshot := p.initial
  unless snapshot.pending.isEmpty && p.block.txs.isEmpty do
    throw "an old chunk applies no transactions or receipts"
  let mut updateChanges : List Near.StateChange := []
  if let some update := ctx.update then
    let before := snapshot.state
    snapshot := { snapshot with state := ← update.apply snapshot.state }
    updateChanges := update.changes before snapshot.state
  let input := ctx.scheduler
  let layout := input.layout
  let params := Near.Bandwidth.Params.protocol layout.numShards congestion.maxReceiptSize
  let status :=
    input.congestion.map fun (id, c) => (id, ChainReplay.ShardChunk.shardStatus congestion layout c)
  let scheduled :=
    Near.Bandwidth.schedule layout p.shard.scheduler params input.requests status
      input.prevBlockHash
  let stateEntries ←
    Near.QueueEncoding.encode snapshot.state catalogue p.context (some cfg) (digestFor catalogue)
  let shardEntries ←
    ({ p.shard with scheduler := scheduled.state } : ChainReplay.ShardChunk.State).entries
  pure ((stateEntries ++ shardEntries).toArray.map fun (k, v) => (bytesOf k, bytesOf v), updateChanges)

end Near.Node.Apply
