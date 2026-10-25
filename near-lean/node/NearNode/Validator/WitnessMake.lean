import NearNode.Validator.State
import NearNode.Trie.Witness

/-!
# Creating and checking a chunk state witness

`create_state_witness` (`chain/chain/src/stateless_validation/state_witness.rs`) from what the node
stored while it applied the chain. For the chunk `C` created on top of block `B` for `shard`:

* `X` is the block that included the shard's last new chunk (`B.chunks[shard].height_included`); the
  **main transition** is the application of that chunk at `X`: the state before it, the root after,
  and the hash of the receipts it applied;
* every block after `X` up to `B` is an **implicit transition**: the old chunk applied there takes the
  state to the root of `B`'s `ChunkExtra`;
* the **source receipt proofs** have, for each new chunk of the blocks after the one that included the
  shard's chunk before `X`, up to `X`, the proof of the receipts that chunk's predecessor sent to the
  shard; the **transactions** are the ones of the chunk at `X`; the **new transactions** those of `C`.

The state before a transition is proved by *every node and value of the shard's trie* at that root
(M8 design decisions): a superset of what applying the chunk reads.

`skeleton` is the witness without those states. A witness received from another producer is accepted
when its skeleton equals ours, the header of `C` agrees with the `ChunkExtra` of `B`, and `C`'s
transactions and encoding check: the node has executed the same blocks, so what
`validate_chunk_state_witness_impl` re-executes on the partial trie it compares with its own results.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh

/-- Where the transitions of a witness start: the state root before each. -/
structure Skeleton where
  witness : ChunkStateWitnessV2
  /-- The shard and the state root before the main transition, and before each implicit one. -/
  rootBefore : Array CryptoHash
  /-- The state root the header of the chunk must have (`ChunkExtra` of `B`). -/
  extra : ChunkExtra
  /-- The receipts the chunk before `C` sent and their root. -/
  outgoing : Array Receipt

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

private def decodeReceipts (rs : Array ByteArray) : Except String (Array Receipt) :=
  rs.mapM fun r =>
    match Codec.decodeAll (α := Receipt) r with
    | .ok v => pure v
    | .error e => throw s!"receipt does not decode: {repr e}"

private def extraOf (s : VState) (block : CryptoHash) (shard : ShardId) : Except String ChunkExtra :=
  match s.pr.extras[(block.bytes, shard)]? with
  | some e => pure e
  | none => throw s!"no chunk extra of shard {shard} at block {block.bytes.size}"

private def stateRootOf : ChunkExtra → CryptoHash
  | .v5 e => e.stateRoot
  | _ => CryptoHash.zero

/-- The witness of the chunk `header` (with `newTransactions`) created on top of `prev`. -/
def skeleton (s : VState) (header : ShardChunkHeader) (newTransactions : Array SignedTransaction) :
    Except String Skeleton := do
  let st := s.st
  let prevHash := header.prevBlockHash
  let shard := header.shardId
  let prevRec ← lift (st.block prevHash)
  let epoch ← lift (st.epochIdFromPrevBlock prevHash)
  let layout := (← lift (st.epoch epoch)).layout
  let some index := layout.getShardIndex shard | throw "shard is not in the layout"
  let some prevChunk := prevRec.chunks[index]? | throw "the previous chunk is missing"
  -- the block that included the last new chunk
  let x ← lift (ancestorAt st prevHash prevChunk.heightIncluded)
  -- the implicit transitions: the blocks after it up to the previous block, oldest first
  let mut implicit : Array ChunkStateTransition := #[]
  let mut roots : Array CryptoHash := #[]
  let mut chain : Array BlockRec := #[]
  let mut cur := prevRec
  for _ in [0:100000] do
    if cur.view.height ≤ x.view.height then
      break
    chain := chain.push cur
    cur ← lift (st.block cur.view.prevHash)
  for y in chain.reverse do
    let before ← extraOf s y.view.prevHash shard
    let after ← extraOf s y.hash shard
    implicit := implicit.push ⟨y.hash, .trieValues #[], stateRootOf after⟩
    roots := roots.push (stateRootOf before)
  -- the main transition
  let xExtra ← extraOf s x.hash shard
  let (main, mainRoot, appliedHash, transactions, proofs) ←
    if prevChunk.isGenesis then
      pure
        (ChunkStateTransition.mk x.hash (.trieValues #[]) (stateRootOf xExtra), CryptoHash.zero,
          CryptoHash.hashBorsh (#[] : Array Receipt), (#[] : Array SignedTransaction),
          (#[] : Array (ChunkHash × ReceiptProof)))
    else do
      let before ← extraOf s x.view.prevHash shard
      let delivered := s.deliveredAt.getD (x.hash.bytes, shard) #[]
      let receipts ← decodeReceipts delivered
      let some body := s.bodies[prevChunk.chunkHash.hash.bytes]?
        | throw "the body of the last chunk is missing"
      -- the receipts each new chunk of the blocks after the chunk before sent to this shard
      let some beforeX := (← lift (st.block x.view.prevHash)).chunks[index]? | throw "chunk missing"
      let low := beforeX.heightIncluded
      let mut proofs : Array (ChunkHash × ReceiptProof) := #[]
      let mut z := x
      for _ in [0:100000] do
        if z.view.height ≤ low then
          break
        for c in z.chunks do
          if c.isNewChunk z.view.height then
            let some cb := s.bodies[c.chunkHash.hash.bytes]?
              | throw s!"the body of a chunk of shard {c.shardId} is missing"
            let (_, ps) ← receiptProofs layout c.shardId cb.receipts
            let some p := ps[index]? | throw "receipt proof of the shard"
            proofs := proofs.push (c.chunkHash, p)
        z ← lift (st.block z.view.prevHash)
      let sorted := proofs.qsort fun a b => compareHash a.1.hash b.1.hash == .lt
      pure
        (ChunkStateTransition.mk x.hash (.trieValues #[]) (stateRootOf xExtra),
          stateRootOf before, CryptoHash.hashBorsh receipts, body.transactions, sorted)
  let extra ← extraOf s prevHash shard
  -- what the chunk before `C` sent: the outgoing receipts at `X`
  let outgoing ← decodeReceipts (s.pr.outgoing.getD (x.hash.bytes, shard) #[])
  pure
    { witness :=
        { epochId := epoch, chunkHeader := header, mainStateTransition := main,
          sourceReceiptProofs := ⟨proofs⟩, appliedReceiptsHash := appliedHash, transactions,
          implicitTransitions := implicit, newTransactions },
      rootBefore := #[mainRoot] ++ roots, extra, outgoing }

/-- Every node and value of the trie at `root` of `shard`, as the state of a transition. -/
def baseState (s : VState) (layout : ShardLayout) (shard : ShardId) (root : CryptoHash) :
    Except String PartialState := do
  if root == CryptoHash.zero then
    return .trieValues #[]
  let src := s.pr.tables.nodeSource (shardKey layout shard)
  let (_, objs) ← Trie.objects src root
  pure (.trieValues (objs.map (·.2)))

/-- `create_state_witness`: the skeleton with the states filled in. -/
def createWitness (s : VState) (header : ShardChunkHeader) (newTransactions : Array SignedTransaction) :
    Except String ChunkStateWitness := do
  let sk ← skeleton s header newTransactions
  let epoch ← (s.st.epochIdFromPrevBlock header.prevBlockHash).mapError (·.kind)
  let layout := (← (s.st.epoch epoch).mapError (·.kind)).layout
  let w := sk.witness
  let isGenesis := sk.rootBefore[0]! == CryptoHash.zero
  let main ←
    if isGenesis then pure w.mainStateTransition
    else do
      pure { w.mainStateTransition with baseState := ← baseState s layout header.shardId sk.rootBefore[0]! }
  let mut implicit := #[]
  for i in [0:w.implicitTransitions.size] do
    let t := w.implicitTransitions[i]!
    implicit := implicit.push { t with baseState := ← baseState s layout header.shardId sk.rootBefore[i + 1]! }
  pure (.v2 { w with mainStateTransition := main, implicitTransitions := implicit })

/-- `validate_chunk_with_chunk_extra_and_receipts_root`: the header of the chunk against the
`ChunkExtra` of its previous block and the root of the receipts sent. -/
def headerAgrees (h : ShardChunkHeader) (extra : ChunkExtra) (outgoingRoot : CryptoHash) :
    Except String Unit := do
  match extra, h with
  | .v5 e, .v3 ⟨inner, _, _⟩ =>
    let check (name : String) (ok : Bool) : Except String Unit :=
      unless ok do throw s!"the chunk header's {name} differs from the node's"
    match inner with
    | .v5 i =>
      check "prev_state_root" (i.prevStateRoot == e.stateRoot)
      check "prev_outcome_root" (i.prevOutcomeRoot == e.outcomeRoot)
      check "prev_gas_used" (i.prevGasUsed == e.gasUsed)
      check "gas_limit" (i.gasLimit == e.gasLimit)
      check "prev_balance_burnt" (i.prevBalanceBurnt == e.balanceBurnt)
      check "prev_validator_proposals" (i.prevValidatorProposals == e.validatorProposals)
      check "congestion_info" (i.congestionInfo == e.congestionInfo)
      check "bandwidth_requests" (i.bandwidthRequests == e.bandwidthRequests)
      check "proposed_split" (i.proposedSplit == e.proposedSplit)
      check "prev_outgoing_receipts_root" (i.prevOutgoingReceiptsRoot == outgoingRoot)
    | .v4 i =>
      check "prev_state_root" (i.prevStateRoot == e.stateRoot)
      check "prev_outcome_root" (i.prevOutcomeRoot == e.outcomeRoot)
      check "prev_gas_used" (i.prevGasUsed == e.gasUsed)
      check "gas_limit" (i.gasLimit == e.gasLimit)
      check "prev_balance_burnt" (i.prevBalanceBurnt == e.balanceBurnt)
      check "prev_validator_proposals" (i.prevValidatorProposals == e.validatorProposals)
      check "congestion_info" (i.congestionInfo == e.congestionInfo)
      check "bandwidth_requests" (i.bandwidthRequests == e.bandwidthRequests)
      check "prev_outgoing_receipts_root" (i.prevOutgoingReceiptsRoot == outgoingRoot)
    | _ => throw "unsupported chunk header inner version"
  | _, _ => throw "unsupported chunk extra or header version"

/-- Accepts a witness produced by someone else: it equals the node's own skeleton (the states aside),
the header agrees with the node's results, and the new transactions and the encoding of the chunk
check out. -/
def checkWitness (s : VState) (code : ReedSolomon.Code) (w : ChunkStateWitness) : Except String Unit := do
  let .v2 w := w
  let sk ← skeleton s w.chunkHeader w.newTransactions
  let mine := sk.witness
  let noState (t : ChunkStateTransition) : ChunkStateTransition := { t with baseState := .trieValues #[] }
  unless w.epochId == mine.epochId do throw "witness: epoch id"
  unless noState w.mainStateTransition == mine.mainStateTransition do
    throw "witness: the main transition differs from the node's"
  unless w.implicitTransitions.map noState == mine.implicitTransitions do
    throw "witness: the implicit transitions differ from the node's"
  unless w.sourceReceiptProofs == mine.sourceReceiptProofs do throw "witness: source receipt proofs"
  unless w.appliedReceiptsHash == mine.appliedReceiptsHash do throw "witness: applied receipts hash"
  unless w.transactions == mine.transactions do throw "witness: transactions"
  -- the header of the chunk
  let (outRoot, _) ← (receiptProofs (← (s.st.epoch w.epochId).mapError (·.kind)).layout w.chunkHeader.shardId sk.outgoing)
  headerAgrees w.chunkHeader sk.extra outRoot
  let (txRoot, _) := merklize w.newTransactions
  unless txRoot == w.chunkHeader.txRoot do throw "witness: the new transactions do not hash to tx_root"
  let body : TransactionReceipt := ⟨w.newTransactions, sk.outgoing⟩
  unless checkEncoding code w.chunkHeader body do throw "witness: the chunk's encoding differs from its header"

end Near.Node.Validator
