import NearNode.Validator.Node
import NearNode.Validator.Prepare

/-!
# Contract code for the witnesses of shards the node does not hold

A state witness leaves the contract code out (`ExcludeContractCodeFromStateWitness`). A chunk producer sends the chunk
validators that do not produce the shard's chunks a `ChunkContractAccesses` message (the hashes of the code its previous
chunk read) alongside the witness; a validator that lacks some of it asks a chunk producer of the shard with a
`ContractCodeRequest` and gets a `ContractCodeResponse` with the zstd compressed code
(`chain/client/src/stateless_validation/partial_witness/partial_witness_actor.rs`). The code lands in the node's code
cache, where the replay of the witness finds it by hash.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain Near.Node.Network Near.Node.Apply Near.Node.Borsh

private def lift {α : Type} (r : Result α) : Except String α :=
  r.mapError fun e => s!"{e.kind} {e.detail}"

/-- The label (`base58(sha256(code))`) the code cache names code by. -/
def codeLabel (h : CryptoHash) : String :=
  Near.StateEncoding.base58 h.bytes.toList

/-- `ContractCodeRequest::new`. -/
def newCodeRequest (s : Signer) (key : ChunkProductionKey) (contracts : Array CodeHash)
    (main : MainTransitionKey) : ContractCodeRequest :=
  let inner : ContractCodeRequestInner :=
    ⟨s.accountId, key, contracts, main, "ContractCodeRequestInner"⟩
  .v1 ⟨inner, s.sign (Codec.encode inner)⟩

/-- Asks the chunk producers of the shard for the code with these hashes, once each. -/
def Env.requestCode (e : Env) (key : ChunkProductionKey) (hashes : Array CryptoHash)
    (main : MainTransitionKey) : IO Unit := do
  let s ← e.get
  let fresh := hashes.filter fun h => !s.codeRequested.contains h.bytes
  if fresh.isEmpty then
    return
  e.state.modify fun s =>
      { s with codeRequested := fresh.foldl (fun m h => m.insert h.bytes) s.codeRequested }
  e.toPeer (.contractCodeRequest (newCodeRequest e.signer key (fresh.map fun h => ⟨h⟩) main))
  e.bump "contractCodeRequests"
  e.log
      s!"contract code: asked for {fresh.size} contract(s) for the chunk of shard {key.shardId} at height {key.heightCreated}"

/-- The code a chunk reads that the node does not hold (`ChunkContractAccesses`): asked for at once. -/
def Env.onContractAccesses (e : Env) (a : ChunkContractAccesses) : IO Unit := do
  let .v1 v := a
  let key := v.inner.nextChunk
  let s ← e.get
  e.bump "ChunkContractAccesses"
  -- a chunk validator of the chunk, and the message is the chunk producer's
  match lift (s.st.chunkValidatorAssignments key.epochId key.shardId key.heightCreated) with
  | .error _ =>
    return
  | .ok assignments =>
    unless assignments.any (·.1 == e.me) do
      return
  match lift (s.st.chunkProducer key.epochId key.heightCreated key.shardId) with
  | .error _ =>
    return
  | .ok producer =>
    unless verifySignature v.signature a.signingBytes producer.publicKey do
      e.log "contract accesses: invalid signature"
      return
  let missing := v.inner.contracts.filter fun h => !s.pr.cache.byLabel.contains (codeLabel h.hash)
  unless missing.isEmpty do
    e.requestCode key (missing.map (·.hash)) v.inner.mainTransition

/-- Code the peer sent (`ContractCodeResponse`): decoded into the cache. Returns whether a witness waited for any. -/
def Env.onContractCode (e : Env) (r : ContractCodeResponse) : IO Bool := do
  e.bump "ContractCodeResponse"
  let s ← e.get
  let key := r.chunkProductionKey
  -- a V2 response is signed by a chunk producer of the shard
  if let some bytes := r.signingBytes then
    let .v2 v := r | return false
    match lift (s.st.validatorByAccount key.epochId v.inner.responder) with
    | .ok responder =>
      unless verifySignature v.signature bytes responder.publicKey do
        e.log "contract code: invalid signature"
        return false
    | .error _ =>
      return false
  let compressed :=
    match r with
    | .v1 x => x.compressedContracts.bytes
    | .v2 x => x.inner.compressedContracts.bytes
  match Zstd.decompress compressed (64 * 1024 * 1024) with
  | .error m =>
    e.log s!"contract code: zstd: {m}"
    return false
  | .ok raw =>
    match Codec.decodeAll (α := Array CodeBytes) raw with
    | .error err =>
      e.log s!"contract code does not decode: {repr err}"
      return false
    | .ok codes =>
      let mut got : Array String := #[]
      for c in codes do
        let st ← e.get
        match (Near.Node.Apply.code c.code).run { cache := st.pr.cache } with
        | .ok (entry, conv) =>
          let h := c.hash.hash
          e.state.modify fun s =>
              { s with
                pr := { s.pr with cache := conv.cache }, keepCodes := s.keepCodes.insert h.bytes }
          got := got.push entry.code.hash
        | .error m =>
          e.log s!"contract code: {m}"
      e.log s!"contract code: {got.size} contract(s) received"
      let s ← e.get
      return s.waitingCode.any fun (_, label) => got.contains label

end Near.Node.Validator
