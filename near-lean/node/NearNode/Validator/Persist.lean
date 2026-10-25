import NearNode.Validator.Node
import NearNode.Chain.Persist

/-!
# What a validator keeps across a restart

The chain store of the observer (`NearNode.Chain.Persist`: blocks, `BlockInfo`, epochs, trie nodes, chunk extras,
receipts, the heads, committed with every applied block) and, next to it,

* the bodies of the chunks the blocks included, the receipts each chunk applied, the execution outcomes with their
  proofs, the receipts by id and the transactions by hash (what the RPC serves, and what the state witnesses are made
  from), committed in the same record as the block;
* the validator's safety state, committed *before* the act it guards: the largest target height of an approval
  (`save_largest_target_height`), the last block produced, the chunks produced and the chunks endorsed. A node that
  restarts never signs a second approval for a height, a second block for a height it produced, a second chunk for a
  (height, shard) or a second endorsement.

`resume` rebuilds the `VState` from the store; `appliedOps` is what applying a block adds.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Apply Near.Node.Borsh Near.Node.Store

def largestTargetKey : ByteArray :=
  "LARGEST_TARGET_HEIGHT".toUTF8

def lastProducedBlockKey : ByteArray :=
  "LAST_PRODUCED_BLOCK".toUTF8

def producedChunkKey (height shard : UInt64) : ByteArray :=
  le64 (le64 "PRODUCED_CHUNK".toUTF8 height) shard

def endorsedKey (chunk : ByteArray) : ByteArray :=
  "ENDORSED".toUTF8 ++ chunk

def u64Bytes (x : UInt64) : ByteArray :=
  le64 ByteArray.empty x

def u64Of (b : ByteArray) : UInt64 :=
  (List.range 8).foldl (fun acc i => acc ||| (b.get! i).toUInt64 <<< (8 * i).toUInt64) 0

def deliveredKey (block : CryptoHash) (shard : UInt64) : ByteArray :=
  le64 block.bytes shard

/-- The operations that record the data of an applied block beside the chain store's own. -/
def appliedOps (s : VState) (b : Block) (reports : Array ShardReport) : Array Op × VState :=
  Id.run do
    let some v := b.header.view? | return (#[], s)
    let hash := b.header.hash
    let mut ops : Array Op := #[]
    let mut s := s
    for r in reports do
      ops := ops.push (.set .delivered (deliveredKey hash r.shard) (Codec.encode r.incoming))
      let (_, paths) := merklizeHashes (r.outcomes.map (·.leafHash))
      for (o, path) in r.outcomes.zip paths do
        let rec_ : OutcomeRec := { block := hash, shard := r.shard, proof := path, outcome := o }
        s := { s with outcomes := s.outcomes.insert o.id.bytes rec_ }
        ops := ops.push (.set .outcome o.id.bytes (Codec.encode (hash, r.shard, path, o)))
      for raw in r.outgoing do
        if let .ok rc := Codec.decodeAll (α := Receipt) raw then
          let .v0 r0 := rc
          s := { s with receiptsById := s.receiptsById.insert r0.receiptId.bytes rc }
          ops := ops.push (.set .receipt r0.receiptId.bytes raw)
      if let some c := b.chunks.find? (·.shardId == r.shard) then
        if c.isNewChunk v.height then
          if let some body := s.chunks[c.chunkHash.hash.bytes]?.bind (·.body) then
            ops := ops.push (.set .chunkBody c.chunkHash.hash.bytes (Codec.encode body))
            for t in body.transactions do
              s := { s with txIndex := s.txIndex.insert t.hash.bytes (hash, c.chunkHash) }
              ops := ops.push (.set .txIndex t.hash.bytes (Codec.encode (hash, c.chunkHash.hash)))
    return (ops,
        { s with
          deliveredAt :=
            reports.foldl (fun m r => m.insert (hash.bytes, r.shard) r.incoming) s.deliveredAt })

private def keys (t : Tables) (c : Col) : Array ByteArray :=
  (t.plain[c.id.toNat]!).fold (fun acc k _ => acc.push k) #[]

private def decodeAs (α : Type) [Codec α] (what : String) (b : ByteArray) : Except String α :=
  match Codec.decodeAll (α := α) b with
  | .ok a => pure a
  | .error e => throw s!"{what} does not decode: {repr e}"

/-- The validator's safety state read from the store. -/
structure Safety where
  largestTarget : UInt64 := 0
  lastProducedBlock : UInt64 := 0
  producedChunks : Std.HashSet (UInt64 × UInt64) := {}
  endorsed : Std.HashSet ByteArray := {}

def readSafety (t : Tables) : Safety :=
  Id.run do
    let mut out : Safety := {}
    if let some b := t.get .blockMisc largestTargetKey then
      out := { out with largestTarget := u64Of b }
    if let some b := t.get .blockMisc lastProducedBlockKey then
      out := { out with lastProducedBlock := u64Of b }
    let chunkPrefix := "PRODUCED_CHUNK".toUTF8
    let endorsedPrefix := "ENDORSED".toUTF8
    for k in keys t .blockMisc do
      if k.size == chunkPrefix.size + 16 && k.extract 0 chunkPrefix.size == chunkPrefix then
        out :=
          { out with
            producedChunks :=
              out.producedChunks.insert
                (u64Of (k.extract chunkPrefix.size (chunkPrefix.size + 8)),
                  u64Of (k.extract (chunkPrefix.size + 8) k.size)) }
      else if
        k.size == endorsedPrefix.size + 32 && k.extract 0 endorsedPrefix.size == endorsedPrefix then
        out := { out with endorsed := out.endorsed.insert (k.extract endorsedPrefix.size k.size) }
    return out

/-- What a validator restarts from. -/
structure Resumed where
  state : VState
  safety : Safety

/-- Rebuilds the state of a validator from a store that holds a chain; `none` for a store without one. -/
def resume (config : Chain.Config) (t : Tables) (delays : Delays) (now : Nat) :
    Except String (Option Resumed) := do
  let some (st, pr0) ← Apply.load config t | return none
  let safety := readSafety t
  -- the chunk extras of every block, the outgoing receipts are loaded by `Apply.load`
  let mut pr := pr0
  for k in keys t .chunkExtra do
    let some b := t.get .chunkExtra k | continue
    let extra ← decodeAs ChunkExtra "chunk extra" b
    let shard := (k.extract 36 40).toList.foldr (fun x acc => acc * 256 + x.toNat) 0
    pr := { pr with extras := pr.extras.insert (k.extract 0 32, shard.toUInt64) extra }
  -- the blocks
  let mut blocks : Std.HashMap ByteArray Block := {}
  let mut applied : Std.HashMap ByteArray BlockHeight := {}
  let mut latest : BlockHeight := 0
  for h in keys t .block do
    let some b := t.get .block h | continue
    let block ← decodeAs Block "block" b
    let some v := block.header.view? | throw "header version"
    blocks := blocks.insert h block
    applied := applied.insert h v.height
    if v.height > latest then
      latest := v.height
  let mut chunks : Std.HashMap ByteArray ChunkEntry := {}
  let mut bodies : Std.HashMap ByteArray TransactionReceipt := {}
  for k in keys t .chunkBody do
    let some b := t.get .chunkBody k | continue
    let body ← decodeAs TransactionReceipt "chunk body" b
    bodies := bodies.insert k body
  for (_, block) in blocks.toList do
    for c in block.chunks do
      let key := c.chunkHash.hash.bytes
      if let some body := bodies[key]? then
        chunks :=
          chunks.insert key
            { header := some (c.withHeightIncluded 0), body := some body, verified := true }
  let mut deliveredAt : Std.HashMap (ByteArray × UInt64) (Array ByteArray) := {}
  for k in keys t .delivered do
    let some b := t.get .delivered k | continue
    deliveredAt :=
      deliveredAt.insert (k.extract 0 32, u64Of (k.extract 32 40))
        (← decodeAs (Array ByteArray) "delivered receipts" b)
  let mut outcomes : Std.HashMap ByteArray OutcomeRec := {}
  for k in keys t .outcome do
    let some b := t.get .outcome k | continue
    let (block, shard, proof, outcome) ←
      decodeAs (CryptoHash × UInt64 × Array MerklePathItem × ExecutionOutcomeWithId) "outcome" b
    outcomes := outcomes.insert k { block, shard, proof, outcome }
  let mut receipts : Std.HashMap ByteArray Receipt := {}
  for k in keys t .receipt do
    let some b := t.get .receipt k | continue
    receipts := receipts.insert k (← decodeAs Receipt "receipt" b)
  let mut txIndex : Std.HashMap ByteArray (CryptoHash × ChunkHash) := {}
  for k in keys t .txIndex do
    let some b := t.get .txIndex k | continue
    let (block, chunk) ← decodeAs (CryptoHash × CryptoHash) "transaction index" b
    txIndex := txIndex.insert k (block, ⟨chunk⟩)
  let tipRec := st.blocks[st.head.bytes]!
  let tipHeight := tipRec.view.height
  let lastFinal : BlockHeight :=
    match st.block tipRec.view.lastFinalBlock with
    | .ok r => r.view.height
    | .error _ => st.config.genesisHeight
  let ds := ((Doomslug.new now safety.largestTarget delays).setTip st.head tipHeight lastFinal now)
  let s : VState :=
    { st, pr, blocks, applied, tip := st.head, tipHeight, ds,
      latestKnown := max latest safety.lastProducedBlock, chunks, bodies, deliveredAt, outcomes,
      receiptsById := receipts, txIndex, producedChunks := safety.producedChunks,
      endorsed := safety.endorsed }
  return some { state := { s with canon := s.canonWith st.head tipHeight }, safety }

end Near.Node.Validator
