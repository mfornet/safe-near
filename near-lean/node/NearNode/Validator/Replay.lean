import NearNode.Validator.WitnessMake
import NearNode.Validator.Prepare

/-!
# Validating a chunk state witness by replay

`pre_validate_chunk_state_witness` and `validate_chunk_state_witness_impl`
(`chain/chain/src/stateless_validation/chunk_validation.rs`) for a node that does not hold the shard's state:
everything is computed from the headers of the chain and the witness.

1. **The block range** (`get_state_witness_block_range`): walking back from the chunk's previous block, the blocks
   whose chunk of the shard is not new are the implicit transitions; the block with the last new chunk `X` is where the
   main transition happens; the blocks from `X` back to (excluding) the second last new chunk's block are the sources of
   the receipts.
2. **The source receipts** (`validate_source_receipt_proofs`): one proof for every new chunk of those blocks, each
   against the `prev_outgoing_receipts_root` of its chunk, shuffled per block with the block's salt; their hash is the
   witness's `applied_receipts_hash`; the witness's transactions hash to the `tx_root` of the chunk at `X`.
3. **The main transition**: the chunk at `X` is applied to the trie the witness proves (`base_state`) with the
   transactions (the ones inside their validity period) and the receipts, and must reach the witness's post state root.
4. **The implicit transitions**: for each later block the chunk is applied as an old chunk to the next base state, and
   must reach the witness's post state root.
5. **The header**: the `ChunkExtra` the replay ends with, and the root of the receipts the main transition sent, must
   agree with the chunk header; the new transactions hash to its `tx_root` and the chunk re-encodes to its merkle root.

The runtime of the node (`Apply.runChunk`) computes from a whole shard state, so the trie a witness proves is read as
the entries that are reachable in it: a partial trie holds what the chunk read (the keys the runtime reads are the keys
nearcore recorded), and the contract code that the witness leaves out comes from the code cache of the node
(`decodeState` with `proved`). The new root is `Trie.update` on the partial trie, which reads the same nodes
nearcore's update does; whatever the replay needed and the witness lacks is an error, never a guess, and the final
agreement with the chunk header is what makes the result a validation.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Apply Near.Node.Borsh Near.Node.Trie

/-- The trie a witness proves: its nodes and values by hash. -/
structure PartialTrie where
  nodes : Std.HashMap CryptoHash ByteArray := {}

def PartialTrie.ofState : PartialState → PartialTrie
  | .trieValues vs => ⟨vs.foldl (fun m v => m.insert (CryptoHash.hash v) v) {}⟩

def PartialTrie.source (t : PartialTrie) : NodeSource :=
  ⟨fun h => t.nodes[h]?⟩

/-- Every entry reachable from `root` through nodes and values the witness holds, in key order. A subtree whose root
the witness does not hold was not read. -/
partial def PartialTrie.entries (t : PartialTrie) (root : CryptoHash) :
    Except String (Array (ByteArray × ByteArray)) := do
  if root == emptyRoot then
    return #[]
  let mut out : Array (ByteArray × ByteArray) := #[]
  let mut stack : Array (CryptoHash × Nibs) := #[(root, ByteArray.empty)]
  while !stack.isEmpty do
    let (h, path) := stack.back!
    stack := stack.pop
    let some bytes := t.nodes[h]? | continue
    let n ←
      match Codec.decodeAll (α := RawTrieNodeWithSize) bytes with
      | .ok n =>
        pure n
      | .error e =>
        throw s!"corrupt trie node {hashHex h}: {repr e}"
    let take (full : Nibs) (v : ValueRef) :
      Array (ByteArray × ByteArray) → Array (ByteArray × ByteArray) := fun acc =>
      match t.nodes[v.hash]? with
      | some value => acc.push (ofNibs full, value)
      | none => acc
    match n.node with
    | .leaf k v =>
      let (e, _) ← hpDecode k
      out := take (path ++ e) v out
    | .extension k c =>
      let (e, _) ← hpDecode k
      stack := stack.push (c, path ++ e)
    | .branchNoValue c =>
      for i in [0:16] do
        if let some ch := c.slots[i]! then
          stack := stack.push (ch, path.push i.toUInt8)
    | .branchWithValue v c =>
      out := take path v out
      for i in [0:16] do
        if let some ch := c.slots[i]! then
          stack := stack.push (ch, path.push i.toUInt8)
  return out.qsort fun a b => compareBytes a.1 b.1 == .lt

/-- The storage accounting trie of a chunk applied on a partial trie: the nodes and values the witness holds are the
lookups' witness, and the entries are those reachable (`overlayOf` for a trie held whole). -/
def PartialTrie.overlay (t : PartialTrie) (root : CryptoHash)
    (entries : Array (ByteArray × ByteArray)) (cache : CodeCache) :
    Except String (Near.TrieOverlay.State × CodeCache) := do
  let usage : UInt64 ←
    match t.nodes[root]? with
    | some b =>
      match Codec.decodeAll (α := RawTrieNodeWithSize) b with
      | .ok n =>
        pure n.memoryUsage
      | .error e =>
        throw s!"corrupt trie root {hashHex root}: {repr e}"
    | none =>
      pure 0
  let mut c := cache
  let mut es : Array (List UInt8 × List UInt8) := #[]
  for (k, v) in entries do
    let (l, c') := c.list v
    c := c'
    es := es.push (k.toList, l)
  let mut witness : Array (List UInt8 × List UInt8) := #[]
  for (h, b) in t.nodes.toList do
    let (l, c') := c.list b
    c := c'
    witness := witness.push (h.bytes.toList, l)
  pure
      ({ entries := es.toList,
         base :=
           { root := root.bytes.toList, memoryUsage := usage.toNat, witness := witness.toList } },
        c)

/-- What the replay reads from the node. -/
structure ReplayEnv where
  st : CS
  params : Params
  /-- The accepted blocks by hash (the chunk headers and the header of each). -/
  blockOf : CryptoHash → Option Block
  /-- The `ChunkExtra` a block left a shard with, for the genesis block. -/
  genesisExtra : ShardId → Option ChunkExtra
  cache : CodeCache
  validityPeriod : Nat
  /-- Applies the witness to every chunk header field too (the node's own checks of the chunk). -/
  code : ReedSolomon.Code

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

private def stateRootOf : ChunkExtra → CryptoHash
  | .v5 e => e.stateRoot
  | _ => CryptoHash.zero

/-- The blocks a witness spans, from the chunk's previous block back: the blocks whose chunk of the shard is not new
until the last new chunk (the implicit transitions, newest first), and the blocks from the one that includes the last
new chunk until the one before the block with the second last (the sources of the receipts, newest first). -/
def blockRange (st : CS) (prevHash : CryptoHash) (index : Nat) :
    Except String (Array BlockRec × Array BlockRec) := do
  let mut implicit : Array BlockRec := #[]
  let mut sources : Array BlockRec := #[]
  let mut seen := 0
  let mut cur ← lift (st.block prevHash)
  for _ in [0:100000] do
    let some chunk := cur.chunks[index]? | throw s!"block {cur.view.height} has no chunk {index}"
    let seen' := seen + (if chunk.isNewChunk cur.view.height then 1 else 0)
    if seen' == 0 then
      implicit := implicit.push cur
    else if seen' == 1 then
      sources := sources.push cur
    else
      break
    if cur.view.isGenesis then
      break
    cur ← lift (st.block cur.view.prevHash)
    seen := seen'
  return (implicit, sources)

/-- What `pre_validate_chunk_state_witness` establishes. -/
structure PreValidated where
  /-- The block with the last new chunk, and the chunk. -/
  last : BlockRec
  lastChunk : ShardChunkHeader
  /-- The implicit transitions, oldest first. -/
  implicit : Array BlockRec
  /-- The receipts the main transition applies, and the transactions of the last chunk that are inside their validity
  period. -/
  receipts : Array Receipt
  transactions : Array SignedTransaction

/-- `pre_validate_chunk_state_witness`. -/
def preValidate (re : ReplayEnv) (w : ChunkStateWitnessV2) : Except String PreValidated := do
  let header := w.chunkHeader
  let shard := header.shardId
  let st := re.st
  let epoch ← lift (st.epochIdFromPrevBlock header.prevBlockHash)
  let layout := (← lift (st.epoch epoch)).layout
  let some index := layout.getShardIndex shard | throw "the shard is not in the layout"
  -- the new transactions are valid for the configuration (`check_valid_for_config`)
  for t in w.newTransactions do
    match validateStateless re.params.cfg t with
    | .ok () =>
      pure ()
    | .error why =>
      throw s!"new transaction {Trie.hashHex t.hash} is invalid: {why.describe}"
  let (implicitNewestFirst, sources) ← blockRange st header.prevBlockHash index
  let some last := sources[0]? | throw "no block with a new chunk of the shard"
  let some lastChunk := last.chunks[index]? | throw "the last chunk is missing"
  -- the source receipt proofs (`validate_source_receipt_proofs`)
  let proofs := w.sourceReceiptProofs.entries
  let mut receipts : Array Receipt := #[]
  if sources.any (·.view.isGenesis) then
    unless sources.size == 1 do
      throw "invalid chain state: blocks alongside the genesis"
    unless proofs.isEmpty do
      throw "genesis source receipt proofs must be empty"
  else
    let mut expected := 0
    for block in sources do
      let mut blockProofs : Array ReceiptProof := #[]
      for chunk in block.chunks do
        if chunk.isNewChunk block.view.height then
          let some (_, proof) := proofs.find? (·.1 == chunk.chunkHash)
            | throw s!"missing source receipt proof for the chunk of shard {chunk.shardId} at {block.view.height}"
          unless proof.proof.fromShardId == chunk.shardId do
            throw "receipt proof from another shard"
          unless proof.proof.toShardId == shard do
            throw "receipt proof for another shard"
          unless proof.verifyAgainstReceiptRoot chunk.prevOutgoingReceiptsRoot do
            throw "receipt proof does not match the outgoing receipts root"
          expected := expected + 1
          blockProofs := blockProofs.push proof
      let (shuffled, _) := (ChaCha20Rng.fromSeed block.view.prevHash.bytes).shuffle blockProofs
      for p in shuffled do
        receipts := receipts ++ p.receipts
    unless proofs.size == expected do
      throw s!"source_receipt_proofs holds {proofs.size} proofs, expected {expected}"
  unless CryptoHash.hashBorsh receipts == w.appliedReceiptsHash do
    throw "the receipts do not hash to applied_receipts_hash"
  unless (merklize w.transactions).1 == lastChunk.txRoot do
    throw "the transactions do not hash to the tx_root of the last chunk"
  -- the transactions inside their validity period (relative to the block before `last`)
  let transactions ←
    if last.view.isGenesis then
      pure w.transactions
    else
      do
        let prevOfLast ← lift (st.block last.view.prevHash)
        pure
            (w.transactions.filter fun t =>
              (checkValidityPeriod st prevOfLast re.validityPeriod t).toOption.isSome)
  pure { last, lastChunk, implicit := implicitNewestFirst.reverse, receipts, transactions }

/-- A chunk applied to a partial trie. -/
structure Applied where
  extra : ChunkExtra
  /-- The receipts the chunk sent (Borsh). -/
  outgoing : Array ByteArray
  cache : CodeCache

/-- Whether `(k, v)` is the contract code an account keeps, which the witness leaves out and the replay writes back
unchanged: its hash is the code hash of the account's record. -/
private def unchangedCode (old : Std.HashMap ByteArray ByteArray) (k v : ByteArray) : Bool :=
  match TrieKey.parse? k with
  | some (.contractCode a) =>
    match old[TrieKey.toVec (.account a)]? with
    | some av =>
      match Codec.decodeAll (α := Account) av with
      | .ok (.v1 _ _ h _) => h == CryptoHash.hash v
      | .ok (.v2 _ _ _ (.local h)) => h == CryptoHash.hash v
      | _ => false
    | none => false
  | _ => false

/-- Applies the chunk of `block` for `shard` to the trie `state` proves at `root`: a new chunk with its transactions and
receipts, or an old chunk. -/
def applyOnPartial (re : ReplayEnv) (cache : CodeCache) (block : Block) (rec : BlockRec)
    (shard : ShardId) (isNew : Bool) (state : PartialState) (root : CryptoHash)
    (txs : Array SignedTransaction) (pending : Array Receipt) (prevExtra : Option ChunkExtraV5) :
    AM Applied := do
  let p := re.params
  let st := re.st
  let some v := block.header.view? | throw "header version"
  let epochId := rec.info.epochId
  let epoch ← liftExcept (lift (st.epoch epochId))
  let layout := epoch.layout
  let some index := layout.getShardIndex shard | throw "the shard is not in the layout"
  let some chunk := block.chunks[index]? | throw "the chunk is missing"
  let prevRec ← liftExcept (lift (st.block v.prevHash))
  let trie := PartialTrie.ofState state
  let entries ← liftExcept (trie.entries root)
  let provider ← liftExcept (lift (providerOf p st v.prevHash epochId))
  let input ← liftExcept (schedulerInput block layout v.prevHash)
  let proposals :=
    if isNew then chunk.prevValidatorProposals else (prevExtra.map (·.validatorProposals)).getD #[]
  let update ←
    liftExcept (lift (Epoch.validatorAccountsUpdate p.setup st v.prevHash shard proposals))
  let ctx := chunkContext p v epoch prevRec chunk layout provider update input
  let (prepared, cache) ← liftExcept (prepare entries txs pending #[] ctx cache true)
  let oldMap := entryMap entries
  if isNew then
    let (o, cache) ← liftExcept (trie.overlay root entries cache)
    let result ← runChunk none p.cfg p.congestion ctx prepared (some o) cache
    let cache :=
      { cache with
        byLabel := result.learned.foldl (fun m e => m.insert e.code.hash e) cache.byLabel }
    let newMap := entryMap result.entries
    let diff :=
      (diffEntries entries result.entries oldMap newMap).filter fun (k, nv) =>
        match nv with
        | some value => !unchangedCode oldMap k value
        | none => true
    let updated ← liftExcept (Trie.update trie.source root diff)
    let changes := updated.changes
    let (outcomeRoot, _) := merklizeHashes (result.outcomes.map (·.leafHash))
    pure
        {
          extra :=
            .v5
              { stateRoot := changes.newRoot, outcomeRoot, validatorProposals := result.proposals,
                gasUsed := result.gasBurnt.toUInt64, gasLimit := chunk.gasLimit,
                balanceBurnt := ⟨result.balanceBurnt⟩, congestionInfo := result.congestion,
                bandwidthRequests := result.requests, proposedSplit := none },
          outgoing := result.outgoing, cache }
  else
    let (newEntries, _) ← liftExcept (runOldChunk p.cfg p.congestion ctx prepared)
    let newMap := entryMap newEntries
    let diff :=
      (diffEntries entries newEntries oldMap newMap).filter fun (k, nv) =>
        match nv with
        | some value => !unchangedCode oldMap k value
        | none => true
    let updated ← liftExcept (Trie.update trie.source root diff)
    let changes := updated.changes
    let some old := prevExtra | throw "no chunk extra before an old chunk"
    pure { extra := .v5 { old with stateRoot := changes.newRoot }, outgoing := #[], cache }
where liftExcept {α : Type} (e : Except String α) : AM α := ExceptT.mk (pure e)

/-- What a replay returns. -/
structure Replayed where
  extra : ChunkExtraV5
  outgoing : Array Receipt
  cache : CodeCache

/-- `validate_chunk_state_witness_impl` after `pre_validate_chunk_state_witness`. -/
def replayWitness (re : ReplayEnv) (w : ChunkStateWitnessV2) : AM Replayed := do
  let pre ← ExceptT.mk (pure (preValidate re w))
  let header := w.chunkHeader
  let shard := header.shardId
  let st := re.st
  let epoch ← ExceptT.mk (pure (lift (st.epochIdFromPrevBlock header.prevBlockHash)))
  let layout := (← ExceptT.mk (pure (lift (st.epoch epoch)))).layout
  let mut cache := re.cache
  let mut outgoing : Array Receipt := #[]
  let mut extra : ChunkExtra := default
  -- the main transition
  if pre.last.view.isGenesis then
    let some e := re.genesisExtra shard | throw "no genesis chunk extra"
    extra := e
  else
    let some block := re.blockOf pre.last.hash | throw "the block of the last chunk is not held"
    let a ←
      applyOnPartial re cache block pre.last shard true w.mainStateTransition.baseState
          pre.lastChunk.prevStateRoot pre.transactions pre.receipts none
    extra := a.extra
    cache := a.cache
    outgoing ←
      a.outgoing.mapM fun r =>
          match Codec.decodeAll (α := Receipt) r with
          | .ok r => pure r
          | .error e => throw s!"outgoing receipt: {repr e}"
  unless stateRootOf extra == w.mainStateTransition.postStateRoot do
    throw "the post state root of the main transition differs from the witness's"
  -- the implicit transitions
  unless pre.implicit.size == w.implicitTransitions.size do
    throw s!"implicit transitions: expected {pre.implicit.size}, found {w.implicitTransitions.size}"
  for i in [0:pre.implicit.size] do
    let rec_ := pre.implicit[i]!
    let t := w.implicitTransitions[i]!
    let some block := re.blockOf rec_.hash | throw "a block of the implicit transitions is not held"
    let .v5 prev := extra | throw "chunk extra version"
    let a ←
      applyOnPartial re cache block rec_ shard false t.baseState prev.stateRoot #[] #[] (some prev)
    extra := a.extra
    cache := a.cache
    unless stateRootOf extra == t.postStateRoot do
      throw s!"the post state root of the implicit transition {i} differs from the witness's"
  -- the header of the chunk, and its new transactions
  let (outRoot, _) ← ExceptT.mk (pure (receiptProofs layout shard outgoing))
  ExceptT.mk (pure (headerAgrees header extra outRoot))
  unless (merklize w.newTransactions).1 == header.txRoot do
    throw "the new transactions do not hash to tx_root"
  let body : TransactionReceipt := ⟨w.newTransactions, outgoing⟩
  unless checkEncoding re.code header body do
    throw "the chunk's encoding differs from its header"
  let .v5 final := extra | throw "chunk extra version"
  pure { extra := final, outgoing, cache }

end Near.Node.Validator
