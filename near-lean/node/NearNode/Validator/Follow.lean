import NearNode.Validator.Endorse

/-!
# Following the chain and producing chunks

Blocks from the peer are validated and recorded in the order they come; a block is applied as soon as
its parent is and the bodies of its new chunks are in. Applying a block moves the Doomslug tip, and the
node then produces the chunks it is the producer of at the next height, distributes them and their
witnesses.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh Near.Node.ReedSolomon

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

private def decodeReceipts (rs : Array ByteArray) : Except String (Array Receipt) :=
  rs.mapM fun r =>
    match Codec.decodeAll (α := Receipt) r with
    | .ok v => pure v
    | .error err => throw s!"receipt does not decode: {repr err}"

/-- The new chunks of a block. -/
def newChunksOf (b : Block) : Array ShardChunkHeader :=
  match b.header.view? with
  | some v => b.chunks.filter (·.isNewChunk v.height)
  | none => #[]

def _root_.Near.Node.EncodedShardChunk.header : EncodedShardChunk → ShardChunkHeader
  | .v1 c => .v1 c.header
  | .v2 c => c.header

/-! ### Producing a chunk -/

/-- `distribute_encoded_chunk`: every part owner gets its parts with the receipt proofs, and the block
producers of the next epoch the proofs alone. -/
def Env.distributeChunk (e : Env) (epoch : EpochId) (nextEpoch : EpochId) (p : Produced)
    (proofs : Array ReceiptProof) : IO Unit := do
  let s ← e.get
  let mut owners : Array (AccountId × Array UInt64) := #[]
  for ord in [0:e.code.total] do
    match partOwner s.st epoch ord with
    | .ok a =>
      match owners.findIdx? (·.1 == a) with
      | some i => owners := owners.modify i fun (a, os) => (a, os.push ord.toUInt64)
      | none => owners := owners.push (a, #[ord.toUInt64])
    | .error err => e.log s!"part owner: {err.kind}"
  match s.st.blockProducersOrdered nextEpoch with
  | .ok bps =>
    for v in bps do
      if !owners.any (·.1 == v.accountId) then
        owners := owners.push (v.accountId, #[])
  | .error _ => pure ()
  for (dest, ords) in owners do
    if dest != e.me then
      match partialEncodedChunk p.encoded ords proofs p.paths with
      | .ok msg => e.toPeer (.versionedPartialEncodedChunk msg)
      | .error err => e.log s!"partial chunk: {err}"

/-- The state witness of the chunk to its validators; the node endorses its own chunk at once. -/
def Env.distributeWitness (e : Env) (header : ShardChunkHeader) (txs : Array SignedTransaction) :
    IO Unit := do
  let s ← e.get
  let started ← e.nowMs
  match chunkValidatorsOf s.st header.prevBlockHash header.shardId header.heightCreated with
  | .error err => e.log s!"witness: {err.kind}"
  | .ok (epoch, assignments) =>
    let validators := assignments.map (·.1)
    match createWitness s header txs with
    | .error m => e.log s!"witness of shard {header.shardId}: {m}"
    | .ok w =>
      let encoded := encodeWitness w
      match witnessParts e.signer epoch header encoded validators with
      | .error m => e.log s!"witness parts: {m}"
      | .ok parts =>
        for (account, part) in parts do
          if account != e.me then
            e.toPeer (.partialEncodedStateWitness part)
        if validators.contains e.me then
          e.endorse header
        e.bump "witnessesSent"
        let took := (← e.nowMs) - started
        e.log s!"witness of shard {header.shardId} height {header.heightCreated}: {encoded.bytes.size} bytes, {parts.size} parts, {took} ms"

/-- What producing a chunk gives, before it is stored and sent. -/
structure ProducedChunk where
  produced : Produced
  epoch : EpochId
  nextEpoch : EpochId
  proofs : Array ReceiptProof
  txs : Array SignedTransaction
  outgoing : Array Receipt

/-- `produce_chunk_internal`: the chunk of `shard` on top of the applied block `b`. -/
def Env.buildChunk (e : Env) (s : VState) (b : Block) (shard : ShardId) : Except String ProducedChunk := do
  let some v := b.header.view? | throw "header version"
  let rec_ ← lift (s.st.block b.header.hash)
  let epoch ← lift (s.st.epochIdFromPrevBlock b.header.hash)
  let nextEpoch ← lift (s.st.nextEpochIdFromPrevBlock b.header.hash)
  let epochData ← lift (s.st.epoch epoch)
  let layout := epochData.layout
  let some index := layout.getShardIndex shard | throw "shard is not in the layout"
  let some (.v5 x) := s.pr.extras[(b.header.hash.bytes, shard)]? | throw "no chunk extra"
  let some prevChunk := rec_.chunks[index]? | throw "previous chunk missing"
  let included ← lift (ancestorAt s.st b.header.hash prevChunk.heightIncluded)
  let outgoing ← decodeReceipts (s.pr.outgoing.getD (included.hash.bytes, shard) #[])
  let (root, proofs) ← receiptProofs layout shard outgoing
  let txs : Array SignedTransaction := #[]
  let inputs : ChunkInputs :=
    { prevBlockHash := b.header.hash, prevStateRoot := x.stateRoot, prevOutcomeRoot := x.outcomeRoot,
      height := v.height + 1, shardId := shard, prevGasUsed := x.gasUsed, gasLimit := x.gasLimit,
      prevBalanceBurnt := x.balanceBurnt, prevValidatorProposals := x.validatorProposals,
      transactions := txs, outgoingReceipts := outgoing, outgoingReceiptsRoot := root,
      txRoot := (merklize txs).1, congestionInfo := x.congestionInfo,
      bandwidthRequests := x.bandwidthRequests, proposedSplit := x.proposedSplit }
  let produced ← produceChunk e.signer epochData.info.protocolVersion.toNat e.code inputs
  pure { produced, epoch, nextEpoch, proofs, txs, outgoing }

/-- Produces, stores and sends the chunk of `shard` at the height after `b`. -/
def Env.produceChunk (e : Env) (b : Block) (shard : ShardId) : IO Unit := do
  let s ← e.get
  let some v := b.header.view? | return
  match e.buildChunk s b shard with
  | .error m => e.log s!"chunk of shard {shard} at height {v.height + 1}: {m}"
  | .ok c =>
    let header := c.produced.encoded.header
    let parts : Std.HashMap UInt64 PartialEncodedChunkPart :=
      (c.produced.encoded.content.parts.zip c.produced.paths).zipIdx.foldl
        (fun m ((p, path), i) =>
          match p with
          | some part => m.insert i.toUInt64 ⟨i.toUInt64, part, path⟩
          | none => m) {}
    let body : TransactionReceipt := ⟨c.txs, c.outgoing⟩
    let now ← e.nowMs
    e.state.modify fun s =>
      let s :=
        s.withChunk header.chunkHash fun x =>
          { x with header := some header, parts, receipts := c.proofs, body := some body, verified := true }
      { s with
        bodies := s.bodies.insert header.chunkHash.hash.bytes body,
        producedChunks := s.producedChunks.insert (shard, v.height + 1),
        inclusion := s.inclusion.markReady header e.me now }
    e.bump "chunksProduced"
    e.log s!"produced the chunk of shard {shard} at height {v.height + 1} ({c.produced.encoded.content.parts.size} parts, {c.txs.size} transactions)"
    e.distributeChunk c.epoch c.nextEpoch c.produced c.proofs
    e.distributeWitness header c.txs

/-- `Client::produce_chunks`: the chunks this node produces at the height after `b`. -/
def Env.produceChunks (e : Env) (b : Block) : IO Unit := do
  let s ← e.get
  let some v := b.header.view? | return
  match lift (s.st.epochIdFromPrevBlock b.header.hash) with
  | .error m => e.log s!"produce chunks: {m}"
  | .ok epoch =>
    match lift (s.st.epoch epoch) with
    | .error m => e.log s!"produce chunks: {m}"
    | .ok data =>
      for shard in data.layout.shardIds do
        match s.st.chunkProducerAfter b.header.hash shard with
        | .ok p =>
          if p.accountId == e.me && !s.producedChunks.contains (shard, v.height + 1) then
            e.produceChunk b shard
        | .error _ => pure ()

end Near.Node.Validator
