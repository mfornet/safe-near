import NearNode.Validator.State
import NearNode.Validator.WitnessMake
import NearNode.Validator.Wire
import NearNode.Validator.Witness
import NearNode.Validator.Messages
import NearNode.Epoch
import NearNode.Network.Peer
import NearNode.Network.Node

/-!
# The validator

What `ClientActor`, `Client`, `ShardsManager` and the stateless validation actors do together
(`chain/client`, `chain/chunks`), on one connection to a peer and one thread:

* a **block** from the peer is validated and recorded (`Epoch.processBlock`), and applied
  (`Apply.applyBlock`) as soon as its parent is applied and the bodies of its new chunks are in; the
  bodies are rebuilt from the parts of the chunks the peer pushes, or asked for;
* every **applied block** moves the Doomslug tip, and makes the node produce the chunks it is the
  producer of (`produce_chunks`): the chunk, its distribution to the part owners, its state witness for
  the chunk validators and its own endorsement;
* the **timer** sends approvals (`process_timer`) and, when the node is the producer of a height whose
  block is ready (approvals, and chunks or their wait), produces the block;
* a **witness** from the peer is rebuilt from its parts, checked against the node's own execution of the
  same blocks and endorsed (`ChunkEndorsement`) to the next block producers.

Messages to the account of this node are handled at once; every other account is the peer.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh Near.Node.ReedSolomon

/-- What the validator needs besides its state. -/
structure Env where
  signer : Signer
  nodeKey : NodeKey
  peer : PeerId
  setup : Epoch.Setup
  params : Params
  /-- The Reed-Solomon code of chunk bodies, and the number of parts. -/
  code : Code
  delays : Delays
  state : IO.Ref VState
  outbox : IO.Ref (Array PeerMessage)
  /-- The first thing that went wrong that the node cannot go on after. -/
  failure : IO.Ref (Option String)
  /-- One JSON line per applied block: its hash and the state root of each shard. -/
  appliedLog : Option IO.FS.Handle := none
  log : String → IO Unit
  /-- Milliseconds on the monotonic clock. -/
  nowMs : IO Nat

def Env.me (e : Env) : AccountId := e.signer.accountId

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

def wallNanos : IO UInt64 := do
  let t ← Std.Time.Timestamp.now
  pure t.toNanosecondsSinceUnixEpoch.val.toNat.toUInt64

def wallSeconds : IO Nat := do
  let t ← Std.Time.Timestamp.now
  pure t.toSecondsSinceUnixEpoch.val.toNat

def Env.get (e : Env) : IO VState :=
  e.state.get

def Env.bump (e : Env) (name : String) : IO Unit :=
  e.state.modify (·.bump name)

/-- A routed message to the peer (the account is the peer's). -/
def Env.toPeer (e : Env) (body : RoutedBody) : IO Unit := do
  let secs ← wallSeconds
  e.outbox.modify (·.push (routedTo e.nodeKey e.peer body secs))

def _root_.Near.Node.PartialEncodedChunk.header : PartialEncodedChunk → ShardChunkHeader
  | .v1 c => .v1 c.header
  | .v2 c => c.header

def _root_.Near.Node.PartialEncodedChunk.parts : PartialEncodedChunk → Array PartialEncodedChunkPart
  | .v1 c => c.parts
  | .v2 c => c.parts

def _root_.Near.Node.PartialEncodedChunk.receipts : PartialEncodedChunk → Array ReceiptProof
  | .v1 c => c.prevOutgoingReceipts
  | .v2 c => c.prevOutgoingReceipts


/-! ### Sending -/

/-- Delivers `body` to `account`: the peer, or this node itself (see `Drive`). -/
def Env.send (e : Env) (selfDeliver : RoutedBody → IO Unit) (account : AccountId) (body : RoutedBody) :
    IO Unit := do
  if account == e.me then selfDeliver body else e.toPeer body

/-! ### Chunks -/

/-- Adds parts whose merkle path leads to the header's root, and the receipts. -/
def ChunkEntry.addParts (c : ChunkEntry) (total : Nat) (parts : Array PartialEncodedChunkPart)
    (receipts : Array ReceiptProof) : ChunkEntry × Nat := Id.run do
  let mut c := c
  let mut refused := 0
  let some h := c.header | return (c, parts.size)
  let parts := c.pendingParts ++ parts
  c := { c with pendingParts := #[] }
  for p in parts do
    if p.partOrd.toNat < total && verifyPath h.encodedMerkleRoot p.merkleProof p.part then
      c := { c with parts := c.parts.insert p.partOrd p }
    else
      refused := refused + 1
  for r in receipts do
    if !c.receipts.any (fun x => x.proof.toShardId == r.proof.toShardId && x.proof.fromShardId == r.proof.fromShardId) then
      c := { c with receipts := c.receipts.push r }
  return (c, refused)

/-- Tries to rebuild the body of a chunk from its parts: the transactions must hash to `tx_root` and the
re-encoding must give the header's merkle root. -/
def ChunkEntry.assemble (c : ChunkEntry) (code : Code) : ChunkEntry × Option String :=
  match c.header, c.body with
  | some h, none =>
    if c.parts.size < code.data then (c, none)
    else
      match assembleBody code h c.parts with
      | .error m => (c, some m)
      | .ok body =>
        if (merklize body.transactions).1 != h.txRoot then (c, some "the transactions do not hash to tx_root")
        else if !checkEncoding code h body then (c, some "the body re-encodes to another merkle root")
        else ({ c with body := some body }, none)
  | _, _ => (c, none)

/-- The parts of block producer seats owned by `me`. -/
def ownedParts (st : CS) (epoch : EpochId) (total : Nat) (me : AccountId) : Array UInt64 :=
  (Array.range total).filterMap fun i =>
    match partOwner st epoch i with
    | .ok a => if a == me then some i.toUInt64 else none
    | .error _ => none

/-- The state with the entry of a chunk updated. -/
def VState.withChunk (s : VState) (hash : ChunkHash) (f : ChunkEntry → ChunkEntry) : VState :=
  let k := hash.hash.bytes
  { s with chunks := s.chunks.insert k (f (s.chunks.getD k {})) }

/-- A chunk header from the peer or from a block is recorded and its parts are checked against it. -/
def Env.noteHeader (e : Env) (h : ShardChunkHeader) : IO Unit :=
  e.state.modify fun s =>
    let entry := s.chunks.getD h.chunkHash.hash.bytes {}
    if entry.header.isSome then s
    else s.withChunk h.chunkHash fun c => { c with header := some h }

/-- Called when a chunk's parts or header changed: rebuilds the body if possible. Returns whether the
chunk became complete. -/
def Env.progressChunk (e : Env) (hash : ChunkHash) : IO Bool := do
  let k := hash.hash.bytes
  let s ← e.get
  let some c := s.chunks[k]? | return false
  let hadBody := c.body.isSome
  let (c', err) := c.assemble e.code
  if let some m := err then
    e.log s!"chunk {hash.hash.bytes.size}: {m}"
  e.state.modify fun s => { s with chunks := s.chunks.insert k c' }
  if c'.body.isSome && !hadBody then
    -- the chunk's body is known: it can be included and applied
    e.state.modify fun s =>
      { s with bodies := s.bodies.insert k c'.body.get! }
    return true
  return false

/-- Brings a chunk entry up to date: checks the producer's signature on the header once the previous block
is known, rebuilds the body when enough parts are in, and marks the chunk ready for inclusion once the parts
this node owns are in. Returns whether the chunk became complete or ready. -/
def Env.refreshChunk (e : Env) (hash : ChunkHash) : IO Bool := do
  let k := hash.hash.bytes
  let s ← e.get
  let some c := s.chunks[k]? | return false
  let some h := c.header | return false
  if !c.pendingParts.isEmpty then
    e.state.modify fun s => s.withChunk hash fun x => (x.addParts e.code.total #[] #[]).1
  if !c.verified && s.st.blockExists h.prevBlockHash then
    match s.st.chunkProducerAfter h.prevBlockHash h.shardId with
    | .ok producer =>
      if verifySignature h.signature hash.hash.bytes producer.publicKey then
        e.state.modify fun s => s.withChunk hash fun x => { x with verified := true }
      else
        e.log s!"a chunk header with an invalid signature for shard {h.shardId}"
        e.state.modify fun s => { s with chunks := s.chunks.erase k }
        return false
    | .error _ => pure ()
  let mut changed ← e.progressChunk hash
  let s ← e.get
  let some c := s.chunks[k]? | return changed
  if c.verified && !(s.inclusion.info.contains k) then
    if let some epoch := (s.st.epochIdFromPrevBlock h.prevBlockHash).toOption then
      let owned := ownedParts s.st epoch e.code.total e.me
      if owned.all c.parts.contains then
        if let some producer := (s.st.chunkProducerAfter h.prevBlockHash h.shardId).toOption then
          let now ← e.nowMs
          e.state.modify fun s => { s with inclusion := s.inclusion.markReady h producer.accountId now }
          changed := true
  return changed

/-- A `PartialEncodedChunk` from the peer. Returns whether a chunk became complete or ready. -/
def Env.onPartialChunk (e : Env) (c : PartialEncodedChunk) : IO Bool := do
  let h := c.header
  e.bump "PartialEncodedChunk"
  e.state.modify fun s =>
    s.withChunk h.chunkHash fun x =>
      let x := if x.header.isSome then x else { x with header := some h }
      (x.addParts e.code.total c.parts c.receipts).1
  e.refreshChunk h.chunkHash

/-- A `PartialEncodedChunkForward`: parts of a chunk whose header may not be known yet. -/
def Env.onChunkForward (e : Env) (m : PartialEncodedChunkForwardMsg) : IO Bool := do
  e.bump "PartialEncodedChunkForward"
  let hash : ChunkHash := ⟨m.chunkHash⟩
  e.state.modify fun s =>
    s.withChunk hash fun x =>
      -- parts are kept unchecked until the header is known: check then
      { x with pendingParts := x.pendingParts ++ m.parts }
  e.refreshChunk hash

end Near.Node.Validator
