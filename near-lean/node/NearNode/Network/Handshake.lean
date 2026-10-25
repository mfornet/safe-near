import NearNode.Network.Message
import NearNode.Network.Keys

/-!
# The handshake

`PeerActor::process_handshake` and `send_handshake` of `chain/network/src/peer/peer_actor.rs`, as
functions of values and a clock. The outbound side proposes an edge and checks the reply; the inbound
side checks what it is proposed and answers with a handshake, a `HandshakeFailure` or the `LastEdge`
it holds. `NearNode.Network.Peer` runs them on a connection.

An edge between two peers is signed by both: each side signs the hash of the ordered pair of peer ids
and the nonce. The nonce is the time in seconds, made odd (an even nonce removes the edge), and a peer
refuses a nonce that is 0, not a valid time, or 20 minutes away from its clock
(`routing/edge.rs::verify_nonce`).
-/

namespace Near.Node.Network

open Near.Node

/-- The network protocol version of the pinned nearcore (`PROTOCOL_VERSION`). -/
def protocolVersion : UInt32 :=
  86

/-- `MIN_SUPPORTED_PROTOCOL_VERSION`. -/
def minSupportedProtocolVersion : UInt32 :=
  83

/-- `EDGE_NONCE_MAX_TIME_DELTA`, in seconds. -/
def edgeNonceMaxTimeDelta : Nat :=
  20 * 60

/-- `MAX_CLOCK_SKEW` of an owned account, in seconds. -/
def maxClockSkew : Int :=
  30 * 60

/-- The three kinds of connection; the node only uses the second. -/
inductive Tier where
  | t1
  | t2
  | t3
  deriving BEq, Inhabited, Repr

/-- The identity and chain of a node. -/
structure Config where
  key : NodeKey
  genesisId : GenesisId
  /-- The port the node listens on: a peer that does not get one drops the connection. -/
  listenPort : Option UInt16
  trackedShards : Array ShardId := #[]
  archival : Bool := false
  protocolVersion : UInt32 := Near.Node.Network.protocolVersion
  oldestSupported : UInt32 := minSupportedProtocolVersion

/-- Why a handshake does not complete. -/
inductive HandshakeError where
  | protocolVersion (theirs : UInt32)
  | genesis
  | peerId
  | tier
  | nonce
  | badNonce
  | invalidEdge
  | ownedAccountSignature
  | ownedAccountMismatch
  | clockSkew
  /-- The peer sent a `HandshakeFailure`. -/
  | failure (reason : HandshakeFailureReason)
  /-- The peer sent an edge that is not valid. -/
  | invalidLastEdge
  /-- The connection closed or the peer sent something else. -/
  | closed (what : String)
  deriving BEq, Inhabited

/-- The handshake message of a tier. -/
def Tier.message : Tier → Handshake → PeerMessage
  | .t1, h => .tier1Handshake h
  | .t2, h => .tier2Handshake h
  | .t3, h => .tier3Handshake h

/-- The handshake and its tier, if the message is one. -/
def PeerMessage.asHandshake? : PeerMessage → Option (Tier × Handshake)
  | .tier1Handshake h => some (.t1, h)
  | .tier2Handshake h => some (.t2, h)
  | .tier3Handshake h => some (.t3, h)
  | _ => none

/-- The edge an outbound connection proposes and the version it proposes it under. -/
structure Spec where
  peerId : PeerId
  tier : Tier
  protocolVersion : UInt32
  edge : PartialEdgeInfo

/-- `Edge::create_fresh_nonce` at the Unix time `now`. -/
def freshNonce (now : Nat) : UInt64 :=
  Edge.freshNonce now.toUInt64

/-- `propose_edge`: the nonce is fresh, or past the nonce of the edge already held with the peer. -/
def proposeNonce (now : Nat) (existing : Option Edge) : UInt64 :=
  let fresh := freshNonce now
  match existing with
  | some e => if e.next > fresh then e.next else fresh
  | none => fresh

/-- `verify_nonce`: the nonce is a time within 20 minutes of `now` (Unix seconds). -/
def verifyNonce (now : Nat) (nonce : UInt64) : Bool :=
  nonce != 0 &&
    (if nonce.toNat > now then nonce.toNat - now else now - nonce.toNat) < edgeNonceMaxTimeDelta

/-- `send_handshake`: the handshake of this node to `spec.peerId`, with the node's height. -/
def Config.hello (c : Config) (spec : Spec) (height : UInt64) : PeerMessage :=
  spec.tier.message
    { protocolVersion := spec.protocolVersion, oldestSupportedVersion := c.oldestSupported,
      senderPeerId := c.key.peerId, targetPeerId := spec.peerId, senderListenPort := c.listenPort,
      senderChainInfo :=
        { genesisId := c.genesisId, height, trackedShards := c.trackedShards,
          archival := c.archival },
      partialEdgeInfo := spec.edge, ownedAccount := none }

/-- The proposal of an outbound connection to `peer` at time `now`. -/
def Config.propose (c : Config) (peer : PeerId) (tier : Tier) (now : Nat) (existing : Option Edge) :
    Spec :=
  { peerId := peer, tier, protocolVersion := c.protocolVersion,
    edge := c.key.partialEdge peer (proposeNonce now existing) }

/-- The checks on the owned account of a handshake: its signature, its owner and its age (`now` in
Unix seconds). -/
def checkOwnedAccount (h : Handshake) (now : Nat) : Except HandshakeError Unit :=
  match h.ownedAccount with
  | none => pure ()
  | some o =>
    if !Chain.verifySignature o.payload.signature o.payload.payload o.account.accountKey then
      .error .ownedAccountSignature
    else
      if o.account.peerId != h.senderPeerId then .error .ownedAccountMismatch
      else
        if
            (o.account.timestamp.seconds * 1000000000 + o.account.timestamp.nanos -
                    now * 1000000000 :
                  Int).natAbs ≥
              maxClockSkew.toNat * 1000000000 then
          .error .clockSkew
        else pure ()

/-- The edge of two partial edges: this node's first. -/
def Config.mergeEdge (c : Config) (peer : PeerId) (nonce : UInt64) (mine theirs : Signature) :
    Edge :=
  Edge.new c.key.peerId peer nonce mine theirs

/-- The outbound side checks the answer to its handshake (the first half of `process_handshake`) and
merges the edges. -/
def Config.checkReply (c : Config) (spec : Spec) (tier : Tier) (h : Handshake) (now : Nat) :
    Except HandshakeError Edge := do
  if h.protocolVersion != spec.protocolVersion then
    throw (.protocolVersion h.protocolVersion)
  if h.senderChainInfo.genesisId != c.genesisId then
    throw .genesis
  if h.senderPeerId != spec.peerId then
    throw .peerId
  if tier != spec.tier then
    throw .tier
  if h.partialEdgeInfo.nonce != spec.edge.nonce then
    throw .nonce
  checkOwnedAccount h now
  let edge :=
    c.mergeEdge h.senderPeerId spec.edge.nonce spec.edge.signature h.partialEdgeInfo.signature
  if !edge.verify then
    throw .invalidEdge
  pure edge

/-- What the inbound side does with a handshake. -/
inductive Inbound where
  /-- Answer with this message and register the connection under this edge. -/
  | accept (reply : PeerMessage) (edge : Edge)
  /-- Answer with this message and keep waiting for a handshake (a failure or the `LastEdge`). -/
  | answer (reply : PeerMessage)
  /-- Close the connection. -/
  | reject (why : HandshakeError)

/-- The inbound side (the second half of `process_handshake`). `existing` is the edge held with the
sender, `height` the height of this node. -/
def Config.checkInbound (c : Config) (tier : Tier) (h : Handshake) (now : Nat)
    (existing : Option Edge) (height : UInt64) : Inbound :=
  let me : PeerInfo := ⟨c.key.peerId, none, none⟩
  if h.protocolVersion < c.oldestSupported || h.protocolVersion > c.protocolVersion then
    .answer (.handshakeFailure me (.protocolVersionMismatch c.protocolVersion c.oldestSupported))
  else
    if h.senderChainInfo.genesisId != c.genesisId then
      .answer (.handshakeFailure me (.genesisMismatch c.genesisId))
    else
      if h.targetPeerId != c.key.peerId then .answer (.handshakeFailure me .invalidTarget)
      else
        if !verifyNonce now h.partialEdgeInfo.nonce then .reject .badNonce
        else
          match existing with
          | some e => if e.nonce ≥ h.partialEdgeInfo.nonce then .answer (.lastEdge e) else finish
          | none => finish
where finish : Inbound :=
    match checkOwnedAccount h now with
    | .error e => .reject e
    | .ok _ =>
      let nonce := h.partialEdgeInfo.nonce
      let mine := c.key.partialEdge h.senderPeerId nonce
      let edge := c.mergeEdge h.senderPeerId nonce mine.signature h.partialEdgeInfo.signature
      if !edge.verify then .reject .invalidEdge
      else
        .accept
          (tier.message
            { protocolVersion := h.protocolVersion, oldestSupportedVersion := c.oldestSupported,
              senderPeerId := c.key.peerId, targetPeerId := h.senderPeerId,
              senderListenPort := c.listenPort,
              senderChainInfo :=
                { genesisId := c.genesisId, height, trackedShards := c.trackedShards,
                  archival := c.archival },
              partialEdgeInfo := mine, ownedAccount := none })
          edge

/-- What the outbound side does with a message that is not a handshake while it waits for one. -/
inductive Retry where
  /-- Send this proposal again. -/
  | again (spec : Spec)
  | stop (why : HandshakeError)

/-- `handle_msg_connecting`: a `HandshakeFailure` or a `LastEdge` in answer to the proposal. -/
def Config.onFailure (c : Config) (spec : Spec) (now : Nat) (m : PeerMessage) : Retry :=
  match m with
  | .handshakeFailure _ reason =>
    match reason with
    | .genesisMismatch _ => .stop (.failure reason)
    | .invalidTarget => .stop (.failure reason)
    | .protocolVersionMismatch version oldest =>
      let common := if version < c.protocolVersion then version else c.protocolVersion
      if common < oldest || common < c.oldestSupported then .stop (.failure reason)
      else .again { spec with protocolVersion := common }
  | .lastEdge e =>
    let ok :=
      Edge.makeKey c.key.peerId spec.peerId == (e.key0, e.key1) && e.nonce ≥ spec.edge.nonce &&
        e.verify
    if !ok then .stop .invalidLastEdge
    else
      let nonce := if e.next > freshNonce now then e.next else freshNonce now
      .again { spec with edge := c.key.partialEdge spec.peerId nonce }
  | _ => .stop (.closed "unexpected message during handshake")

end Near.Node.Network
