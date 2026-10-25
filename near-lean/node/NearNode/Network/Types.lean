import NearNode.Primitives
import NearNode.Chain.Types

/-!
# Network types

The Borsh types of `chain/network/src/network_protocol` at the pinned nearcore: `PeerInfo` and
`PeerChainInfoV2` (`peer.rs`), `Edge`, `EdgeInner` and `PartialEdgeInfo` (`edge.rs`), and the routed
message with its bodies and the request messages that ride in it (`mod.rs`, `state_sync.rs`).
`PeerId` and `AnnounceAccount` are `NearNode.Primitives.StateSync`. A routed body is the flat
`RoutedMessageBody` enum that goes over the wire; `RoutedBody.tiered` converts to and from
`TieredMessageBody` (the T1 and T2 enums of `RoutedMessageV3`), which carry the same payloads under
other tags. `TxStatusResponse` (tag 3), whose payload is the RPC view `FinalExecutionOutcomeView`,
is not modelled: a message with that body does not decode.
-/

namespace Near.Node

open Borsh

/-! ### Ordering and addresses -/

/-- `PublicKey`'s derived order: the scheme first, then the bytes. -/
def PublicKey.compare (a b : PublicKey) : Ordering :=
  let rank : PublicKey → Nat
    | .ed25519 _ => 0
    | .secp256k1 _ => 1
    | .mldsa65 _ => 2
  let bytes : PublicKey → ByteArray
    | .ed25519 k => k
    | .secp256k1 k => k
    | .mldsa65 k => k
  (Ord.compare (rank a) (rank b)).then (compareBytes (bytes a) (bytes b))

/-- `PeerId`'s derived order. -/
def PeerId.compare (a b : PeerId) : Ordering :=
  a.key.compare b.key

instance : Ord PeerId :=
  ⟨PeerId.compare⟩

/-- `std::net::SocketAddr` as Borsh writes it: a variant, the octets and the port. -/
inductive SocketAddr where
  | v4 (ip : ByteArray) (port : UInt16)
  | v6 (ip : ByteArray) (port : UInt16)
  deriving BEq, Inhabited

instance : Codec SocketAddr :=
  .enum "SocketAddr"
    [.variantOf 0 (Codec.pair (.fixed 4) inferInstance) (fun (ip, p) => .v4 ip p) fun
        | .v4 ip p => some (ip, p)
        | _ => none,
      .variantOf 1 (Codec.pair (.fixed 16) inferInstance) (fun (ip, p) => .v6 ip p) fun
        | .v6 ip p => some (ip, p)
        | _ => none]

/-- The port of an address. -/
def SocketAddr.port : SocketAddr → UInt16
  | .v4 _ p => p
  | .v6 _ p => p

/-- `PeerInfo`: the peer id, its address and the account it serves. -/
structure PeerInfo where
  id : PeerId
  addr : Option SocketAddr
  accountId : Option AccountId
  deriving BEq, Inhabited

instance : Codec PeerInfo :=
  .iso (PeerId × Option SocketAddr × Option AccountId) (fun (i, a, c) => ⟨i, a, c⟩) fun x =>
    (x.id, x.addr, x.accountId)

/-- `PeerChainInfoV2`. -/
structure PeerChainInfo where
  genesisId : GenesisId
  height : BlockHeight
  trackedShards : Array ShardId
  archival : Bool
  deriving BEq, Inhabited

/-! ### Edges -/

/-- `PartialEdgeInfo`: a nonce and the sender's signature of the edge hash. -/
structure PartialEdgeInfo where
  nonce : UInt64
  signature : Signature
  deriving BEq, Inhabited

instance : Codec PartialEdgeInfo :=
  .iso (UInt64 × Signature) (fun (n, s) => ⟨n, s⟩) fun x => (x.nonce, x.signature)

/-- `EdgeInner`: `key.0 ≤ key.1`, the nonce (odd: added, even: removed), both signatures of the edge
hash and, for a removal, who signed it. -/
structure Edge where
  key0 : PeerId
  key1 : PeerId
  nonce : UInt64
  signature0 : Signature
  signature1 : Signature
  removalInfo : Option (Bool × Signature)
  deriving BEq, Inhabited

instance : Codec Edge :=
  .iso (PeerId × PeerId × UInt64 × Signature × Signature × Option (Bool × Signature))
    (fun (a, b, n, s0, s1, r) => ⟨a, b, n, s0, s1, r⟩) fun x =>
    (x.key0, x.key1, x.nonce, x.signature0, x.signature1, x.removalInfo)

namespace Edge

/-- `Edge::build_hash`: the hash of the ordered pair of peers and the nonce. -/
def buildHash (p0 p1 : PeerId) (nonce : UInt64) : CryptoHash :=
  let (a, b) := if p0.compare p1 == .gt then (p1, p0) else (p0, p1)
  CryptoHash.hashBorsh (a, b, nonce)

/-- `Edge::make_key`. -/
def makeKey (p0 p1 : PeerId) : PeerId × PeerId :=
  if p0.compare p1 == .lt then (p0, p1) else (p1, p0)

/-- `Edge::hash`. -/
def hash (e : Edge) : CryptoHash :=
  buildHash e.key0 e.key1 e.nonce

/-- `Edge::next_nonce`. -/
def nextNonce (n : UInt64) : UInt64 :=
  if n % 2 == 0 then n + 1 else n + 2

/-- `Edge::next`. -/
def next (e : Edge) : UInt64 :=
  nextNonce e.nonce

/-- `Edge::create_fresh_nonce`: the Unix time, made odd. -/
def freshNonce (unixSeconds : UInt64) : UInt64 :=
  if unixSeconds % 2 == 0 then unixSeconds + 1 else unixSeconds

/-- `Edge::new` with the keys in order. -/
def new (p0 p1 : PeerId) (nonce : UInt64) (s0 s1 : Signature) : Edge :=
  if p0.compare p1 == .lt then ⟨p0, p1, nonce, s0, s1, none⟩ else ⟨p1, p0, nonce, s1, s0, none⟩

/-- Whether the edge is added (odd nonce). -/
def isActive (e : Edge) : Bool :=
  e.nonce % 2 == 1

/-- `Edge::verify`: the signatures of an added edge, or those of the added edge it removes and the
signature of the party that removed it. -/
def verify (e : Edge) : Bool :=
  if e.key0.compare e.key1 == .gt then false
  else
    if e.isActive then
      e.removalInfo.isNone && Chain.verifySignature e.signature0 e.hash.bytes e.key0.key &&
        Chain.verifySignature e.signature1 e.hash.bytes e.key1.key
    else
      if e.nonce == 0 then false
      else
        let addHash := buildHash e.key0 e.key1 (e.nonce - 1)
        if
            !(Chain.verifySignature e.signature0 addHash.bytes e.key0.key &&
                Chain.verifySignature e.signature1 addHash.bytes e.key1.key) then
          false
        else
          match e.removalInfo with
          | some (party, sig) =>
            Chain.verifySignature sig e.hash.bytes (if party then e.key0.key else e.key1.key)
          | none => false

/-- `Edge::contains_peer`. -/
def containsPeer (e : Edge) (p : PeerId) : Bool :=
  e.key0 == p || e.key1 == p

end Edge

/-- `Edge::partial_verify`: `edge_info` was signed by `peer1` for the pair. -/
def PartialEdgeInfo.verify (peer0 peer1 : PeerId) (info : PartialEdgeInfo) : Bool :=
  Chain.verifySignature info.signature (Edge.buildHash peer0 peer1 info.nonce).bytes peer1.key

/-! ### Routed messages -/

/-- `PeerIdOrHash`. -/
inductive PeerIdOrHash where
  | peerId (p : PeerId)
  | hash (h : CryptoHash)
  deriving BEq, Inhabited

instance : Codec PeerIdOrHash :=
  .enum "PeerIdOrHash"
    [.variant 0 PeerId .peerId fun
        | .peerId p => some p
        | _ => none,
      .variant 1 CryptoHash .hash fun
        | .hash h => some h
        | _ => none]

/-- `Ping` and `Pong`. -/
structure PingPong where
  nonce : UInt64
  source : PeerId
  deriving BEq, Inhabited

instance : Codec PingPong :=
  .iso (UInt64 × PeerId) (fun (n, s) => ⟨n, s⟩) fun x => (x.nonce, x.source)

/-- `PartialEncodedChunkForwardMsg`. -/
structure PartialEncodedChunkForwardMsg where
  chunkHash : CryptoHash
  innerHeaderHash : CryptoHash
  merkleRoot : CryptoHash
  signature : Signature
  prevBlockHash : CryptoHash
  heightCreated : BlockHeight
  shardId : ShardId
  parts : Array PartialEncodedChunkPart
  deriving BEq, Inhabited

instance : Codec PartialEncodedChunkForwardMsg :=
  .iso
    (CryptoHash ×
      CryptoHash ×
      CryptoHash × Signature × CryptoHash × BlockHeight × ShardId × Array PartialEncodedChunkPart)
    (fun (c, i, m, s, p, h, sh, ps) => ⟨c, i, m, s, p, h, sh, ps⟩) fun x =>
    (x.chunkHash, x.innerHeaderHash, x.merkleRoot, x.signature, x.prevBlockHash, x.heightCreated,
      x.shardId, x.parts)

/-- `PartialEncodedChunkRequestMsg`: the chunk, the parts wanted and the shards the requester
tracks (a `HashSet`, written sorted). -/
structure PartialEncodedChunkRequestMsg where
  chunkHash : CryptoHash
  partOrds : Array UInt64
  trackingShards : SortedMap ShardId Unit
  deriving BEq, Inhabited

instance : Codec PartialEncodedChunkRequestMsg :=
  .iso (CryptoHash × Array UInt64 × SortedMap ShardId Unit) (fun (c, p, t) => ⟨c, p, t⟩) fun x =>
    (x.chunkHash, x.partOrds, x.trackingShards)

/-- `PartialEncodedChunkResponseMsg`. -/
structure PartialEncodedChunkResponseMsg where
  chunkHash : CryptoHash
  parts : Array PartialEncodedChunkPart
  receipts : Array ReceiptProof
  deriving BEq, Inhabited

instance : Codec PartialEncodedChunkResponseMsg :=
  .iso (CryptoHash × Array PartialEncodedChunkPart × Array ReceiptProof)
    (fun (c, p, r) => ⟨c, p, r⟩) fun x => (x.chunkHash, x.parts, x.receipts)

/-- `StateHeaderRequest`. -/
structure StateHeaderRequest where
  shardId : ShardId
  syncHash : CryptoHash
  addr : SocketAddr
  deriving BEq, Inhabited

instance : Codec StateHeaderRequest :=
  .iso (ShardId × CryptoHash × SocketAddr) (fun (s, h, a) => ⟨s, h, a⟩) fun x =>
    (x.shardId, x.syncHash, x.addr)

/-- `StatePartRequest`. -/
structure StatePartRequest where
  shardId : ShardId
  syncHash : CryptoHash
  partId : UInt64
  addr : SocketAddr
  deriving BEq, Inhabited

instance : Codec StatePartRequest :=
  .iso (ShardId × CryptoHash × UInt64 × SocketAddr) (fun (s, h, p, a) => ⟨s, h, p, a⟩) fun x =>
    (x.shardId, x.syncHash, x.partId, x.addr)

/-- `SpicePartialDataRequest`. -/
structure SpicePartialDataRequest where
  dataId : SpiceDataIdentifier
  requester : AccountId
  deriving BEq, Inhabited

instance : Codec SpicePartialDataRequest :=
  .iso (SpiceDataIdentifier × AccountId) (fun (d, r) => ⟨d, r⟩) fun x => (x.dataId, x.requester)

/-- `StateResponseInfoV1`. -/
structure StateResponseInfoV1 where
  shardId : ShardId
  syncHash : CryptoHash
  stateResponse : ShardStateSyncResponseV1
  deriving BEq, Inhabited

instance : Codec StateResponseInfoV1 :=
  .iso (ShardId × CryptoHash × ShardStateSyncResponseV1) (fun (s, h, r) => ⟨s, h, r⟩) fun x =>
    (x.shardId, x.syncHash, x.stateResponse)

/-- `StateResponseInfoV2`. -/
structure StateResponseInfoV2 where
  shardId : ShardId
  syncHash : CryptoHash
  stateResponse : ShardStateSyncResponse
  deriving BEq, Inhabited

instance : Codec StateResponseInfoV2 :=
  .iso (ShardId × CryptoHash × ShardStateSyncResponse) (fun (s, h, r) => ⟨s, h, r⟩) fun x =>
    (x.shardId, x.syncHash, x.stateResponse)

/-- `StateResponseInfo`. -/
inductive StateResponseInfo where
  | v1 (i : StateResponseInfoV1)
  | v2 (i : StateResponseInfoV2)
  deriving BEq, Inhabited

instance : Codec StateResponseInfo :=
  .enum "StateResponseInfo"
    [.variant 0 StateResponseInfoV1 .v1 fun
        | .v1 i => some i
        | _ => none,
      .variant 1 StateResponseInfoV2 .v2 fun
        | .v2 i => some i
        | _ => none]

/-- `RoutedMessageBody`, with the tag of each variant as an enum discriminant. -/
inductive RoutedBody where
  | blockApproval (a : Approval)
  | forwardTx (t : SignedTransaction)
  | txStatusRequest (account : AccountId) (hash : CryptoHash)
  | partialEncodedChunkRequest (m : PartialEncodedChunkRequestMsg)
  | partialEncodedChunkResponse (m : PartialEncodedChunkResponseMsg)
  | ping (p : PingPong)
  | pong (p : PingPong)
  | versionedPartialEncodedChunk (c : PartialEncodedChunk)
  | partialEncodedChunkForward (m : PartialEncodedChunkForwardMsg)
  | chunkStateWitnessAck (a : ChunkStateWitnessAck)
  | partialEncodedStateWitness (w : PartialEncodedStateWitness)
  | partialEncodedStateWitnessForward (w : PartialEncodedStateWitness)
  | versionedChunkEndorsement (e : ChunkEndorsement)
  | statePartRequest (r : StatePartRequest)
  | chunkContractAccesses (a : ChunkContractAccesses)
  | contractCodeRequest (r : ContractCodeRequest)
  | contractCodeResponse (r : ContractCodeResponse)
  | partialEncodedContractDeploys (d : PartialEncodedContractDeploys)
  | stateHeaderRequest (r : StateHeaderRequest)
  | spicePartialData (d : SpicePartialData)
  | stateRequestAck (a : StateRequestAck)
  | spiceChunkEndorsement (e : SpiceChunkEndorsement)
  | spicePartialDataRequest (r : SpicePartialDataRequest)
  | spiceChunkContractAccesses (a : SpiceChunkContractAccesses)
  | spiceContractCodeRequest (r : SpiceContractCodeRequest)
  | spiceContractCodeResponse (r : SpiceContractCodeResponse)
  | versionedPartialEncodedStateWitness (w : VersionedPartialEncodedStateWitness)
  | versionedPartialEncodedStateWitnessForward (w : VersionedPartialEncodedStateWitness)
  deriving BEq, Inhabited

/-- One variant of `RoutedBody` under its tag. -/
private def routedCase (tag : UInt8) (β : Type) [Codec β] (inj : β → RoutedBody)
    (prj : RoutedBody → Option β) : Codec.Case RoutedBody :=
  .variant tag β inj prj

instance : Codec RoutedBody :=
  .enum "RoutedMessageBody"
    [routedCase 0 Approval .blockApproval fun
        | .blockApproval a => some a
        | _ => none,
      routedCase 1 SignedTransaction .forwardTx fun
        | .forwardTx t => some t
        | _ => none,
      routedCase 2 (AccountId × CryptoHash) (fun (a, h) => .txStatusRequest a h) fun
        | .txStatusRequest a h => some (a, h)
        | _ => none,
      routedCase 11 PartialEncodedChunkRequestMsg .partialEncodedChunkRequest fun
        | .partialEncodedChunkRequest m => some m
        | _ => none,
      routedCase 12 PartialEncodedChunkResponseMsg .partialEncodedChunkResponse fun
        | .partialEncodedChunkResponse m => some m
        | _ => none,
      routedCase 14 PingPong .ping fun
        | .ping p => some p
        | _ => none,
      routedCase 15 PingPong .pong fun
        | .pong p => some p
        | _ => none,
      routedCase 16 PartialEncodedChunk .versionedPartialEncodedChunk fun
        | .versionedPartialEncodedChunk c => some c
        | _ => none,
      routedCase 18 PartialEncodedChunkForwardMsg .partialEncodedChunkForward fun
        | .partialEncodedChunkForward m => some m
        | _ => none,
      routedCase 21 ChunkStateWitnessAck .chunkStateWitnessAck fun
        | .chunkStateWitnessAck a => some a
        | _ => none,
      routedCase 22 PartialEncodedStateWitness .partialEncodedStateWitness fun
        | .partialEncodedStateWitness w => some w
        | _ => none,
      routedCase 23 PartialEncodedStateWitness .partialEncodedStateWitnessForward fun
        | .partialEncodedStateWitnessForward w => some w
        | _ => none,
      routedCase 24 ChunkEndorsement .versionedChunkEndorsement fun
        | .versionedChunkEndorsement e => some e
        | _ => none,
      routedCase 27 StatePartRequest .statePartRequest fun
        | .statePartRequest r => some r
        | _ => none,
      routedCase 28 ChunkContractAccesses .chunkContractAccesses fun
        | .chunkContractAccesses a => some a
        | _ => none,
      routedCase 29 ContractCodeRequest .contractCodeRequest fun
        | .contractCodeRequest r => some r
        | _ => none,
      routedCase 30 ContractCodeResponse .contractCodeResponse fun
        | .contractCodeResponse r => some r
        | _ => none,
      routedCase 31 PartialEncodedContractDeploys .partialEncodedContractDeploys fun
        | .partialEncodedContractDeploys d => some d
        | _ => none,
      routedCase 32 StateHeaderRequest .stateHeaderRequest fun
        | .stateHeaderRequest r => some r
        | _ => none,
      routedCase 33 SpicePartialData .spicePartialData fun
        | .spicePartialData d => some d
        | _ => none,
      routedCase 34 StateRequestAck .stateRequestAck fun
        | .stateRequestAck a => some a
        | _ => none,
      routedCase 35 SpiceChunkEndorsement .spiceChunkEndorsement fun
        | .spiceChunkEndorsement e => some e
        | _ => none,
      routedCase 36 SpicePartialDataRequest .spicePartialDataRequest fun
        | .spicePartialDataRequest r => some r
        | _ => none,
      routedCase 37 SpiceChunkContractAccesses .spiceChunkContractAccesses fun
        | .spiceChunkContractAccesses a => some a
        | _ => none,
      routedCase 38 SpiceContractCodeRequest .spiceContractCodeRequest fun
        | .spiceContractCodeRequest r => some r
        | _ => none,
      routedCase 39 SpiceContractCodeResponse .spiceContractCodeResponse fun
        | .spiceContractCodeResponse r => some r
        | _ => none,
      routedCase 40 VersionedPartialEncodedStateWitness .versionedPartialEncodedStateWitness fun
        | .versionedPartialEncodedStateWitness w => some w
        | _ => none,
      routedCase 41 VersionedPartialEncodedStateWitness .versionedPartialEncodedStateWitnessForward
        fun
        | .versionedPartialEncodedStateWitnessForward w => some w
        | _ => none]

/-- `RoutedMessageV1`: what the `Routed` protobuf message carries. -/
structure RoutedMessageV1 where
  target : PeerIdOrHash
  author : PeerId
  signature : Signature
  ttl : UInt8
  body : RoutedBody
  deriving BEq, Inhabited

instance : Codec RoutedMessageV1 :=
  .iso (PeerIdOrHash × PeerId × Signature × UInt8 × RoutedBody)
    (fun (t, a, s, l, b) => ⟨t, a, s, l, b⟩) fun x =>
    (x.target, x.author, x.signature, x.ttl, x.body)

namespace RoutedBody

/-- The tag of a body in `RoutedMessageBody`. -/
def tag (b : RoutedBody) : UInt8 :=
  (Codec.encode b)[0]!

/-- Whether the variant is a T1 message. -/
def isT1 (b : RoutedBody) : Bool :=
  [0, 16, 18, 22, 23, 24, 28, 29, 30, 33, 35, 36, 37, 38, 39, 40, 41].contains b.tag

/-- The T1 tags of `T1MessageBody`, indexed by the `RoutedMessageBody` tag they stand for. -/
def t1Table : List (UInt8 × UInt8) :=
  [(0, 0), (16, 1), (18, 2), (22, 3), (23, 4), (24, 5), (28, 6), (29, 7), (30, 8), (33, 9),
    (35, 10), (36, 11), (37, 12), (38, 13), (39, 14), (40, 15), (41, 16)]

/-- The T2 tags of `T2MessageBody`, indexed by the `RoutedMessageBody` tag they stand for. -/
def t2Table : List (UInt8 × UInt8) :=
  [(1, 0), (2, 1), (11, 3), (12, 4), (14, 5), (15, 6), (21, 7), (27, 8), (31, 9), (32, 10),
    (34, 11)]

/-- The limit on an incoming message of this body (`PeerMessage::max_size`): 512 KiB, 32 MiB or
128 MiB. -/
def maxSize (b : RoutedBody) : Nat :=
  let small := 512 * 1024
  let medium := 32 * 1048576
  let large := 128 * 1048576
  match b with
  | .blockApproval _ | .versionedChunkEndorsement _ | .spiceChunkEndorsement _ => small
  | .txStatusRequest _ _ | .ping _ | .pong _ | .chunkStateWitnessAck _ | .statePartRequest _ |
    .stateHeaderRequest _ | .stateRequestAck _ => small
  | .partialEncodedChunkForward _ | .chunkContractAccesses _ | .contractCodeRequest _ |
    .spicePartialDataRequest _ | .spiceChunkContractAccesses _ | .spiceContractCodeRequest _ |
    .versionedPartialEncodedChunk _ => medium
  | .forwardTx _ | .partialEncodedChunkRequest _ | .partialEncodedChunkResponse _ => medium
  | .partialEncodedStateWitness _ | .partialEncodedStateWitnessForward _ |
    .versionedPartialEncodedStateWitness _ | .versionedPartialEncodedStateWitnessForward _ |
    .contractCodeResponse _ | .spicePartialData _ | .spiceContractCodeResponse _ => large
  | .partialEncodedContractDeploys _ => large

/-- `TieredMessageBody` Borsh: the tier, the tag within the tier, and the payload. -/
def tiered (b : RoutedBody) : ByteArray :=
  let e := Codec.encode b
  let table := if b.isT1 then t1Table else t2Table
  let inner := (table.lookup e[0]!).getD 0
  (ByteArray.empty.push (if b.isT1 then 0 else 1) |>.push inner).append (e.extract 1 e.size)

/-- Reads `TieredMessageBody` Borsh. -/
def ofTiered (d : ByteArray) : Except Error RoutedBody :=
  if d.size < 2 then .error .eof
  else
    let table := if d[0]! == 0 then t1Table else t2Table
    if d[0]! > 1 then .error (.tag "TieredMessageBody" d[0]!.toNat)
    else
      match table.find? (·.2 == d[1]!) with
      | some (v1, _) => Codec.decodeAll ((ByteArray.empty.push v1).append (d.extract 2 d.size))
      | none => .error (.tag "TieredMessageBody" d[1]!.toNat)

end RoutedBody

/-- `RoutedMessageV3`: the message as the node handles it. The time is `created_at` in seconds. -/
structure RoutedMessage where
  target : PeerIdOrHash
  author : PeerId
  ttl : UInt8
  body : RoutedBody
  signature : Option Signature
  createdAt : Option Int
  numHops : UInt32
  deriving BEq, Inhabited

/-- `RoutedMessage::build_hash`: what the author signs, the hash of the target, author and body. -/
def RoutedMessage.hash (m : RoutedMessage) : CryptoHash :=
  CryptoHash.hashBorsh (m.target, m.author, m.body)

/-- `RoutedMessageV3::verify`. -/
def RoutedMessage.verify (m : RoutedMessage) : Bool :=
  match m.signature with
  | some s => Chain.verifySignature s m.hash.bytes m.author.key
  | none => false

end Near.Node
