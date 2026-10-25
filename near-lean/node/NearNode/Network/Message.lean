import NearNode.Proto.Wire
import NearNode.Network.Types

/-!
# Peer messages

`PeerMessage`, the message of the peer protocol, with its protobuf codec: `network.proto` and the
conversions of `chain/network/src/network_protocol/proto_conv/*` at the pinned nearcore. Most
messages are a protobuf wrapper (`bytes borsh = 1`) around a Borsh value of `NearNode.Primitives`
or `NearNode.Network.Types`; the handshake, the account data and the routing messages are real
protobuf messages.

`PeerMessage.decode` accepts what nearcore's `PeerMessage::deserialize` accepts: the message is
parsed completely (every occurrence of every known field, and the framing of every unknown field),
the last occurrence of a oneof or singular field wins, and a conversion that fails (a missing
required field, a Borsh payload that does not decode, a bad length) rejects the message.
-/

namespace Near.Node.Network

open Near.Node Proto
open Near.Node.Borsh (Codec)

/-! ### Schemas of `network.proto` -/

namespace Schemas

/-- The `bytes borsh = 1` wrappers, and `CryptoHash { bytes hash = 1 }`. -/
def wrapper : Schema :=
  [(1, .bytes)]

def timestamp : Schema :=
  [(1, .i64), (2, .i32)]

def genesisId : Schema :=
  [(1, .string), (2, .msg wrapper)]

def peerChainInfo : Schema :=
  [(1, .msg genesisId), (2, .u64), (3, .packed), (4, .bool)]

def signedPayload : Schema :=
  [(1, .bytes), (2, .msg wrapper)]

def handshake : Schema :=
  [(1, .u32), (2, .u32), (3, .msg wrapper), (4, .msg wrapper), (5, .u32), (6, .msg peerChainInfo),
    (7, .msg wrapper), (8, .msg signedPayload)]

def handshakeFailure : Schema :=
  [(1, .i32), (2, .msg wrapper), (3, .msg genesisId), (4, .u32), (5, .u32)]

def socketAddr : Schema :=
  [(1, .bytes), (2, .u32)]

def peerAddr : Schema :=
  [(1, .msg socketAddr), (2, .msg wrapper)]

def accountData : Schema :=
  [(5, .msg wrapper), (6, .msg wrapper), (2, .msg peerAddr), (7, .u64), (4, .msg timestamp)]

def ownedAccount : Schema :=
  [(1, .msg wrapper), (2, .msg wrapper), (3, .msg timestamp)]

def accountKeyPayload : Schema :=
  [(2, .msg accountData), (3, .msg ownedAccount)]

def routingTableUpdate : Schema :=
  [(1, .msg wrapper), (2, .msg wrapper)]

/-- A message whose only field is an embedded message, repeated or not. -/
def holder : Schema :=
  [(1, .msg wrapper)]

def syncAccountsData : Schema :=
  [(1, .msg signedPayload), (2, .bool), (3, .bool)]

def peersRequest : Schema :=
  [(1, .u32), (2, .u32)]

def peersResponse : Schema :=
  [(1, .msg wrapper), (2, .msg wrapper)]

def routed : Schema :=
  [(1, .bytes), (2, .msg timestamp), (4, .u32)]

def peerIdOrHash : Schema :=
  [(1, .msg wrapper), (2, .msg wrapper)]

def routedV3 : Schema :=
  [(1, .msg peerIdOrHash), (2, .msg wrapper), (3, .u32), (4, .bytes), (5, .msg wrapper), (6, .i64),
    (7, .u32)]

def disconnect : Schema :=
  [(1, .bool)]

def stateRequestHeader : Schema :=
  [(1, .u64), (2, .msg wrapper)]

def stateRequestPart : Schema :=
  [(1, .u64), (2, .msg wrapper), (3, .u64)]

def snapshotHostInfo : Schema :=
  [(1, .msg wrapper), (2, .msg wrapper), (3, .u64), (4, .packed), (5, .msg wrapper)]

def syncSnapshotHosts : Schema :=
  [(1, .msg snapshotHostInfo)]

def epochSyncResponse : Schema :=
  [(1, .bytes)]

def optimisticBlock : Schema :=
  [(1, .bytes), (2, .msg wrapper), (3, .msg wrapper)]

def traceContext : Schema :=
  [(1, .bytes), (2, .bytes), (3, .i32)]

/-- The members of the `message_type` oneof of `PeerMessage`, by field number. -/
def peerMessageMembers : Schema :=
  [(27, .msg handshake), (4, .msg handshake), (33, .msg handshake), (5, .msg handshakeFailure),
    (6, .msg holder), (7, .msg routingTableUpdate), (8, .msg holder), (9, .msg holder),
    (25, .msg syncAccountsData), (10, .msg peersRequest), (11, .msg peersResponse),
    (12, .msg holder), (13, .msg holder), (14, .msg holder), (15, .msg holder), (16, .msg wrapper),
    (17, .msg routed), (18, .msg disconnect), (19, .msg wrapper), (29, .msg stateRequestHeader),
    (30, .msg stateRequestPart), (31, .msg holder), (32, .msg syncSnapshotHosts), (34, .msg []),
    (35, .msg epochSyncResponse), (36, .msg optimisticBlock), (37, .msg routedV3)]

/-- `PeerMessage`. -/
def peerMessage : Schema :=
  (26, .msg traceContext) :: peerMessageMembers

end Schemas

/-! ### Field readers

The readers below convert the last occurrence of a field. Every occurrence has already been checked
by `validate`, as the parser of `protobuf` checks it, so an occurrence that a later one replaces is
accepted whatever it holds. -/

/-- Reads a Borsh payload; the error carries what it was. -/
def borshOf [Codec α] (what : String) (b : ByteArray) : Except Error α :=
  match Codec.decodeAll (α := α) b with
  | .ok a => .ok a
  | .error _ => .error (.other what)

/-- The last length-delimited occurrence of `num`, and how far its limit lies beyond its bytes. -/
def lastSub (fs : Array Field) (num : Nat) : Option (ByteArray × Nat) :=
  fs.foldl (init := none) fun r x =>
    match x.val with
    | .bytes b s => if x.num == num then some (b, s) else r
    | _ => r

/-- The last length-delimited occurrence of `num` (a `bytes` or `string` field). -/
def lastBytes (fs : Array Field) (num : Nat) : Option ByteArray :=
  (lastSub fs num).map (·.1)

/-- The last occurrence of `num`, converted with `f`. -/
def lastMessage (fs : Array Field) (num : Nat) (f : ByteArray → Nat → Except Error α) :
    Except Error (Option α) :=
  match lastSub fs num with
  | some (b, s) => some <$> f b s
  | none => pure none

/-- All occurrences of a repeated message field, converted. -/
def allMessages (fs : Array Field) (num : Nat) (f : ByteArray → Nat → Except Error α) :
    Except Error (Array α) := do
  let mut out := #[]
  for x in fs do
    if x.num == num then
      if let .bytes b s := x.val then
        out := out.push (← f b s)
  pure out

/-- The last occurrence of a `uint32` field. -/
def lastU32 (fs : Array Field) (num : Nat) : Except Error (Option UInt32) := do
  let mut r := none
  for x in fs do
    if x.num == num then
      if let .varint v := x.val then
        r := some (← v.toU32)
  pure r

/-- The last occurrence of a `uint64` field. -/
def lastU64 (fs : Array Field) (num : Nat) : Option UInt64 :=
  fs.foldl (init := none) fun r x =>
    match x.val with
    | .varint v => if x.num == num then some v.val else r
    | _ => r

/-- The last occurrence of a `bool` field. -/
def lastBool (fs : Array Field) (num : Nat) : Option Bool :=
  fs.foldl (init := none) fun r x =>
    match x.val with
    | .varint v => if x.num == num then some v.toBool else r
    | _ => r

/-- The last occurrence of an `int64` field. -/
def lastI64 (fs : Array Field) (num : Nat) : Option Int :=
  fs.foldl (init := none) fun r x =>
    match x.val with
    | .varint v => if x.num == num then some v.toI64 else r
    | _ => r

/-- The last occurrence of an `int32` or enum field. -/
def lastI32 (fs : Array Field) (num : Nat) : Except Error (Option Int) := do
  let mut r := none
  for x in fs do
    if x.num == num then
      if let .varint v := x.val then
        r := some (← v.toI32)
  pure r

/-- The last occurrence of a `string` field. -/
def lastString (fs : Array Field) (num : Nat) : Except Error (Option String) :=
  match lastBytes fs num with
  | some b => some <$> readString b
  | none => pure none

/-- A repeated `uint64`, packed or not. -/
def allU64 (fs : Array Field) (num : Nat) : Except Error (Array UInt64) := do
  let mut out := #[]
  for x in fs do
    if x.num == num then
      match x.val with
      | .varint v =>
        out := out.push v.val
      | .bytes b _ =>
        out := out ++ (← readPacked b)
      | _ =>
        pure ()
  pure out

/-! ### Wrappers and small messages -/

/-- The `bytes borsh = 1` wrapper that most messages are. -/
def decodeWrapper [Codec α] (what : String) (b : ByteArray) (sl : Nat) : Except Error α := do
  let fs ← parseFields b [] sl
  borshOf what ((lastBytes fs 1).getD ByteArray.empty)

/-- Encodes the wrapper. -/
def encodeWrapper [Codec α] (a : α) : ByteArray :=
  putBytes ByteArray.empty 1 (Codec.encode a)

/-- `CryptoHash { bytes hash = 1 }`: exactly 32 bytes. -/
def decodeHash (b : ByteArray) (sl : Nat) : Except Error CryptoHash := do
  let fs ← parseFields b [] sl
  let raw := (lastBytes fs 1).getD ByteArray.empty
  if raw.size == 32 then
    pure ⟨raw⟩
  else
    throw (.other "hash")

def encodeHash (h : CryptoHash) : ByteArray :=
  putBytes ByteArray.empty 1 h.bytes

/-- `google.protobuf.Timestamp`. -/
structure Timestamp where
  seconds : Int
  nanos : Int
  deriving BEq, Inhabited, Repr

/-- The range of `time::OffsetDateTime` without `large-dates`, in Unix seconds. -/
def timestampMin : Int :=
  -377705116800

def timestampMax : Int :=
  253402300799

/-- Whether `utc_from_proto` accepts the timestamp. -/
def Timestamp.valid (t : Timestamp) : Bool :=
  let secs := (t.seconds * 1000000000 + t.nanos) / 1000000000
  timestampMin ≤ secs && secs ≤ timestampMax

def decodeTimestamp (b : ByteArray) (sl : Nat) : Except Error Timestamp := do
  let fs ← parseFields b [] sl
  pure ⟨(lastI64 fs 1).getD 0, (← lastI32 fs 2).getD 0⟩

def encodeTimestamp (t : Timestamp) : ByteArray :=
  putI64 (putI64 ByteArray.empty 1 t.seconds) 2 t.nanos

/-- A required timestamp that `utc_from_proto` converts. -/
def requireTimestamp (t : Option Timestamp) : Except Error Timestamp := do
  let t ← required "timestamp" t
  if t.valid then
    pure t
  else
    throw (.other "timestamp out of range")

/-- `SocketAddr { bytes ip = 1; uint32 port = 2 }`. -/
def decodeSocketAddr (b : ByteArray) (sl : Nat) : Except Error SocketAddr := do
  let fs ← parseFields b [] sl
  let ip := (lastBytes fs 1).getD ByteArray.empty
  let port := (← lastU32 fs 2).getD 0
  if port > 65535 then
    throw (.other "port")
  if ip.size == 4 then
    pure (.v4 ip port.toUInt16)
  else if ip.size == 16 then
    pure (.v6 ip port.toUInt16)
  else
    throw (.other "ip")

def encodeSocketAddr (a : SocketAddr) : ByteArray :=
  match a with
  | .v4 ip p => putU32 (putBytes ByteArray.empty 1 ip) 2 p.toUInt32
  | .v6 ip p => putU32 (putBytes ByteArray.empty 1 ip) 2 p.toUInt32

def decodePublicKey (b : ByteArray) (sl : Nat) : Except Error PublicKey :=
  decodeWrapper "PublicKey" b sl

def decodePeerId (b : ByteArray) (sl : Nat) : Except Error PeerId :=
  (fun k => ⟨k⟩) <$> decodePublicKey b sl

def encodePublicKey (k : PublicKey) : ByteArray :=
  encodeWrapper k

def encodePeerId (p : PeerId) : ByteArray :=
  encodePublicKey p.key

def decodeSignature (b : ByteArray) (sl : Nat) : Except Error Signature :=
  decodeWrapper "Signature" b sl

def encodeSignature (s : Signature) : ByteArray :=
  encodeWrapper s

/-- `GenesisId { string chain_id = 1; CryptoHash hash = 2 }`. -/
def decodeGenesisId (b : ByteArray) (sl : Nat) : Except Error GenesisId := do
  let fs ← parseFields b Schemas.genesisId.wide sl
  let chainId := (← lastString fs 1).getD ""
  let hash ← required "genesis hash" (← lastMessage fs 2 decodeHash)
  pure ⟨chainId, hash⟩

def encodeGenesisId (g : GenesisId) : ByteArray :=
  putMessage (putString ByteArray.empty 1 g.chainId) 2 (some (encodeHash g.hash))

/-- The limit on `tracked_shards` of a handshake. -/
def maxTrackedShardsPerPeer : Nat :=
  128

/-- `PeerChainInfo`. -/
def decodePeerChainInfo (b : ByteArray) (sl : Nat) : Except Error PeerChainInfo := do
  let fs ← parseFields b Schemas.peerChainInfo.wide sl
  let genesisId ← required "genesis_id" (← lastMessage fs 1 decodeGenesisId)
  let shards ← allU64 fs 3
  if shards.size > maxTrackedShardsPerPeer then
    throw (.other "tracked_shards")
  pure ⟨genesisId, (lastU64 fs 2).getD 0, shards, (lastBool fs 4).getD false⟩

def encodePeerChainInfo (c : PeerChainInfo) : ByteArray :=
  let d := putMessage ByteArray.empty 1 (some (encodeGenesisId c.genesisId))
  let d := putU64 d 2 c.height
  let d := putRepeatedField d 3 c.trackedShards
  putBool d 4 c.archival

/-! ### Handshake -/

/-- `AccountKeySignedPayload`: the serialized payload and the signature of its bytes. -/
structure SignedPayload where
  payload : ByteArray
  signature : Signature
  deriving BEq, Inhabited

def decodeSignedPayload (b : ByteArray) (sl : Nat) : Except Error SignedPayload := do
  let fs ← parseFields b Schemas.signedPayload.wide sl
  let signature ← required "signature" (← lastMessage fs 2 decodeSignature)
  pure ⟨(lastBytes fs 1).getD ByteArray.empty, signature⟩

def encodeSignedPayload (p : SignedPayload) : ByteArray :=
  putMessage (putBytes ByteArray.empty 1 p.payload) 2 (some (encodeSignature p.signature))

/-- `OwnedAccount`: the account key, the peer that owns it and when this was signed. -/
structure OwnedAccount where
  accountKey : PublicKey
  peerId : PeerId
  timestamp : Timestamp
  deriving BEq, Inhabited

def decodeOwnedAccountBody (b : ByteArray) (sl : Nat) : Except Error OwnedAccount := do
  let fs ← parseFields b Schemas.ownedAccount.wide sl
  let key ← required "account_key" (← lastMessage fs 1 decodePublicKey)
  let peer ← required "peer_id" (← lastMessage fs 2 decodePeerId)
  let ts ← requireTimestamp (← lastMessage fs 3 decodeTimestamp)
  pure ⟨key, peer, ts⟩

def encodeOwnedAccountBody (a : OwnedAccount) : ByteArray :=
  let d := putMessage ByteArray.empty 1 (some (encodePublicKey a.accountKey))
  let d := putMessage d 2 (some (encodePeerId a.peerId))
  putMessage d 3 (some (encodeTimestamp a.timestamp))

/-- `AccountKeyPayload` with an `OwnedAccount`: field 3 of the `payload_type` oneof. -/
def encodeOwnedAccountPayload (a : OwnedAccount) : ByteArray :=
  putBytesField ByteArray.empty 3 (encodeOwnedAccountBody a)

/-- The slack of a message that is parsed from a stream of its own, whose limit is `u64::MAX`. -/
def topSlack (d : ByteArray) : Nat :=
  noLimit - d.size

/-- The member of the `payload_type` oneof of an `AccountKeyPayload` that comes last, if any. -/
def lastPayload (payload : ByteArray) : Except Error (Option (Nat × ByteArray × Nat)) := do
  validate Schemas.accountKeyPayload payload (topSlack payload)
  let fs ← parseFields payload Schemas.accountKeyPayload.wide (topSlack payload)
  let mut kind : Option (Nat × ByteArray × Nat) := none
  for f in fs do
    if let .bytes d sl := f.val then
      if f.num == 2 || f.num == 3 then
        kind := some (f.num, d, sl)
  pure kind

/-- A signed `OwnedAccount`, with the bytes the signature covers. -/
structure SignedOwnedAccount where
  account : OwnedAccount
  payload : SignedPayload
  deriving BEq, Inhabited

/-- `SignedOwnedAccount::try_from`: the payload is an `AccountKeyPayload` holding an
`OwnedAccount`. -/
def decodeSignedOwnedAccount (b : ByteArray) (sl : Nat) : Except Error SignedOwnedAccount := do
  let sp ← decodeSignedPayload b sl
  match ← lastPayload sp.payload with
  | some (3, d, sl) =>
    pure ⟨← decodeOwnedAccountBody d sl, sp⟩
  | _ =>
    throw (.other "bad payload type")

/-- `Handshake`. -/
structure Handshake where
  protocolVersion : UInt32
  oldestSupportedVersion : UInt32
  senderPeerId : PeerId
  targetPeerId : PeerId
  senderListenPort : Option UInt16
  senderChainInfo : PeerChainInfo
  partialEdgeInfo : PartialEdgeInfo
  ownedAccount : Option SignedOwnedAccount
  deriving BEq, Inhabited

def decodeHandshake (b : ByteArray) (sl : Nat) : Except Error Handshake := do
  let fs ← parseFields b Schemas.handshake.wide sl
  let sender ← required "sender_peer_id" (← lastMessage fs 3 decodePeerId)
  let target ← required "target_peer_id" (← lastMessage fs 4 decodePeerId)
  let port := (← lastU32 fs 5).getD 0
  if port > 65535 then
    throw (.other "sender_listen_port")
  let info ← required "sender_chain_info" (← lastMessage fs 6 decodePeerChainInfo)
  let edge ←
    required "partial_edge_info"
        (← lastMessage fs 7 (decodeWrapper (α := PartialEdgeInfo) "PartialEdgeInfo"))
  pure
      { protocolVersion := (← lastU32 fs 1).getD 0,
        oldestSupportedVersion := (← lastU32 fs 2).getD 0, senderPeerId := sender,
        targetPeerId := target, senderListenPort := if port == 0 then none else some port.toUInt16,
        senderChainInfo := info, partialEdgeInfo := edge,
        ownedAccount := ← lastMessage fs 8 decodeSignedOwnedAccount }

def encodeHandshake (h : Handshake) : ByteArray :=
  let d := putU32 (putU32 ByteArray.empty 1 h.protocolVersion) 2 h.oldestSupportedVersion
  let d := putMessage d 3 (some (encodePeerId h.senderPeerId))
  let d := putMessage d 4 (some (encodePeerId h.targetPeerId))
  let d := putU32 d 5 (h.senderListenPort.getD 0).toUInt32
  let d := putMessage d 6 (some (encodePeerChainInfo h.senderChainInfo))
  let d := putMessage d 7 (some (encodeWrapper h.partialEdgeInfo))
  putMessage d 8 (h.ownedAccount.map fun o => encodeSignedPayload o.payload)

/-- `HandshakeFailureReason`. -/
inductive HandshakeFailureReason where
  | protocolVersionMismatch (version oldestSupportedVersion : UInt32)
  | genesisMismatch (genesisId : GenesisId)
  | invalidTarget
  deriving BEq, Inhabited

def decodeHandshakeFailure (b : ByteArray) (sl : Nat) :
    Except Error (PeerInfo × HandshakeFailureReason) := do
  let fs ← parseFields b Schemas.handshakeFailure.wide sl
  let info ← required "peer_info" (← lastMessage fs 2 (decodeWrapper (α := PeerInfo) "PeerInfo"))
  match (← lastI32 fs 1).getD 0 with
  | 1 =>
    pure (info, .protocolVersionMismatch ((← lastU32 fs 4).getD 0) ((← lastU32 fs 5).getD 0))
  | 2 =>
    pure (info, .genesisMismatch (← required "genesis_id" (← lastMessage fs 3 decodeGenesisId)))
  | 3 =>
    pure (info, .invalidTarget)
  | _ =>
    throw (.other "reason: unknown")

def encodeHandshakeFailure (info : PeerInfo) (r : HandshakeFailureReason) : ByteArray :=
  let reason : UInt64 :=
    match r with
    | .protocolVersionMismatch _ _ => 1
    | .genesisMismatch _ => 2
    | .invalidTarget => 3
  let d := putU64 ByteArray.empty 1 reason
  let d := putMessage d 2 (some (encodeWrapper info))
  match r with
  | .protocolVersionMismatch v o => putU32 (putU32 d 4 v) 5 o
  | .genesisMismatch g => putMessage d 3 (some (encodeGenesisId g))
  | .invalidTarget => d

/-! ### Account data -/

/-- `PeerAddr`: a peer and where it listens. -/
structure PeerAddr where
  addr : SocketAddr
  peerId : PeerId
  deriving BEq, Inhabited

def decodePeerAddr (b : ByteArray) (sl : Nat) : Except Error PeerAddr := do
  let fs ← parseFields b Schemas.peerAddr.wide sl
  pure
      { addr := ← required "addr" (← lastMessage fs 1 decodeSocketAddr),
        peerId := ← required "peer_id" (← lastMessage fs 2 decodePeerId) }

def encodePeerAddr (a : PeerAddr) : ByteArray :=
  putMessage (putMessage ByteArray.empty 1 (some (encodeSocketAddr a.addr))) 2
    (some (encodePeerId a.peerId))

/-- `VersionedAccountData`. -/
structure AccountData where
  peerId : PeerId
  accountKey : PublicKey
  proxies : Array PeerAddr
  version : UInt64
  timestamp : Timestamp
  deriving BEq, Inhabited

def decodeAccountDataBody (b : ByteArray) (sl : Nat) : Except Error AccountData := do
  let fs ← parseFields b Schemas.accountData.wide sl
  pure
      { peerId := ← required "peer_id" (← lastMessage fs 5 decodePeerId),
        accountKey := ← required "account_key" (← lastMessage fs 6 decodePublicKey),
        proxies := ← allMessages fs 2 decodePeerAddr, version := (lastU64 fs 7).getD 0,
        timestamp := ← requireTimestamp (← lastMessage fs 4 decodeTimestamp) }

/-- `AccountKeyPayload` with an `AccountData`: field 2 of the `payload_type` oneof. -/
def encodeAccountDataPayload (a : AccountData) : ByteArray :=
  let d := putMessage ByteArray.empty 5 (some (encodePeerId a.peerId))
  let d := putMessage d 6 (some (encodePublicKey a.accountKey))
  let d := a.proxies.foldl (fun d p => putBytesField d 2 (encodePeerAddr p)) d
  let d := putU64 d 7 a.version
  let d := putMessage d 4 (some (encodeTimestamp a.timestamp))
  putBytesField ByteArray.empty 2 d

/-- `SignedAccountData`. -/
structure SignedAccountData where
  data : AccountData
  payload : SignedPayload
  deriving BEq, Inhabited

def decodeSignedAccountData (b : ByteArray) (sl : Nat) : Except Error SignedAccountData := do
  let sp ← decodeSignedPayload b sl
  match ← lastPayload sp.payload with
  | some (2, d, sl) =>
    pure ⟨← decodeAccountDataBody d sl, sp⟩
  | _ =>
    throw (.other "bad payload type")

/-- `SyncAccountsData`. -/
structure SyncAccountsData where
  accountsData : Array SignedAccountData
  incremental : Bool
  requestingFullSync : Bool
  deriving BEq, Inhabited

/-! ### Routing and the rest -/

/-- `RoutingTableUpdate`. -/
structure RoutingTableUpdate where
  edges : Array Edge
  accounts : Array AnnounceAccount
  deriving BEq, Inhabited

def decodeRoutingTableUpdate (b : ByteArray) (sl : Nat) : Except Error RoutingTableUpdate := do
  let fs ← parseFields b Schemas.routingTableUpdate.wide sl
  pure
      { edges := ← allMessages fs 1 (decodeWrapper (α := Edge) "Edge"),
        accounts := ← allMessages fs 2 (decodeWrapper (α := AnnounceAccount) "AnnounceAccount") }

def encodeRoutingTableUpdate (u : RoutingTableUpdate) : ByteArray :=
  let d := u.edges.foldl (fun d e => putBytesField d 1 (encodeWrapper e)) ByteArray.empty
  u.accounts.foldl (fun d a => putBytesField d 2 (encodeWrapper a)) d

/-- `PeersRequest`: the optional limits. -/
structure PeersRequest where
  maxPeers : Option UInt32
  maxDirectPeers : Option UInt32
  deriving BEq, Inhabited

/-- `PeersResponse`. -/
structure PeersResponse where
  peers : Array PeerInfo
  directPeers : Array PeerInfo
  deriving BEq, Inhabited

/-- `SnapshotHostInfo`. -/
structure SnapshotHostInfo where
  peerId : PeerId
  syncHash : CryptoHash
  epochHeight : UInt64
  shards : Array UInt64
  signature : Signature
  deriving BEq, Inhabited

/-- `MAX_SHARDS_PER_SNAPSHOT_HOST_INFO`. -/
def maxShardsPerSnapshotHostInfo : Nat :=
  512

def decodeSnapshotHostInfo (b : ByteArray) (sl : Nat) : Except Error SnapshotHostInfo := do
  let fs ← parseFields b Schemas.snapshotHostInfo.wide sl
  let shards ← allU64 fs 4
  if shards.size > maxShardsPerSnapshotHostInfo then
    throw (.other "shards")
  pure
      { peerId := ← required "peer_id" (← lastMessage fs 1 decodePeerId),
        syncHash := ← required "sync_hash" (← lastMessage fs 2 decodeHash),
        epochHeight := (lastU64 fs 3).getD 0, shards,
        signature := ← required "signature" (← lastMessage fs 5 decodeSignature) }

def encodeSnapshotHostInfo (i : SnapshotHostInfo) : ByteArray :=
  let d := putMessage ByteArray.empty 1 (some (encodePeerId i.peerId))
  let d := putMessage d 2 (some (encodeHash i.syncHash))
  let d := putU64 d 3 i.epochHeight
  let d := putRepeatedField d 4 i.shards
  putMessage d 5 (some (encodeSignature i.signature))

/-- `Disconnect`. -/
structure Disconnect where
  removeFromConnectionStore : Bool
  deriving BEq, Inhabited

/-- The limit on a routed message body. -/
def maxRoutedMessageBytes : Nat :=
  64 * 1048576

/-- The protobuf `RoutedMessage`: the Borsh `RoutedMessageV1` with the creation time and the hop
count beside it. -/
def decodeRouted (b : ByteArray) (sl : Nat) : Except Error RoutedMessage := do
  let fs ← parseFields b Schemas.routed.wide sl
  let raw := (lastBytes fs 1).getD ByteArray.empty
  if raw.size > maxRoutedMessageBytes then
    throw (.other "routed message too large")
  let v1 ← borshOf (α := RoutedMessageV1) "RoutedMessageV1" raw
  let createdAt ←
    match ← lastMessage fs 2 decodeTimestamp with
    | none =>
      pure none
    | some t =>
      if t.valid then
        pure (some ((t.seconds * 1000000000 + t.nanos) / 1000000000))
      else
        throw (.other "created_at")
  pure
      { target := v1.target, author := v1.author, ttl := v1.ttl, body := v1.body,
        signature := some v1.signature, createdAt, numHops := (← lastU32 fs 4).getD 0 }

def decodePeerIdOrHash (b : ByteArray) (sl : Nat) : Except Error PeerIdOrHash := do
  let fs ← parseFields b Schemas.peerIdOrHash.wide sl
  let mut r : Option PeerIdOrHash := none
  for f in fs do
    if let .bytes d sl := f.val then
      if f.num == 1 then
        r := some (.peerId (← decodePeerId d sl))
      else if f.num == 2 then
        r := some (.hash (← decodeHash d sl))
  required "target_type" r

/-- The protobuf `RoutedMessageV3`. -/
def decodeRoutedV3 (b : ByteArray) (sl : Nat) : Except Error RoutedMessage := do
  let fs ← parseFields b Schemas.routedV3.wide sl
  let target ← required "target" (← lastMessage fs 1 decodePeerIdOrHash)
  let author ← required "author" (← lastMessage fs 2 decodePeerId)
  let raw := (lastBytes fs 4).getD ByteArray.empty
  if raw.size > maxRoutedMessageBytes then
    throw (.other "routed message too large")
  let body ←
    match RoutedBody.ofTiered raw with
    | .ok b =>
      pure b
    | .error _ =>
      throw (.other "borsh_body")
  pure
      { target, author, ttl := ((lastU64 fs 3).getD 0).toUInt8, body,
        signature := ← lastMessage fs 5 decodeSignature, createdAt := lastI64 fs 6,
        numHops := (← lastU32 fs 7).getD 0 }

/-- `PeerMessage::serialize` of a routed message: nearcore sends the V1 form. -/
def encodeRouted (m : RoutedMessage) : ByteArray :=
  let v1 : RoutedMessageV1 :=
    ⟨m.target, m.author, m.signature.getD (.ed25519 (ByteArray.mk (Array.replicate 64 0))), m.ttl,
      m.body⟩
  let d := putBytes ByteArray.empty 1 (Codec.encode v1)
  let d :=
    match m.createdAt with
    | some t =>
      if timestampMin ≤ t && t ≤ timestampMax then putMessage d 2 (some (encodeTimestamp ⟨t, 0⟩))
      else d
    | none => d
  putU32 d 4 m.numHops

/-! ### The peer message -/

/-- `PeerMessage`. -/
inductive PeerMessage where
  | tier1Handshake (h : Handshake)
  | tier2Handshake (h : Handshake)
  | tier3Handshake (h : Handshake)
  | handshakeFailure (info : PeerInfo) (reason : HandshakeFailureReason)
  | lastEdge (e : Edge)
  | syncRoutingTable (u : RoutingTableUpdate)
  | requestUpdateNonce (p : PartialEdgeInfo)
  | syncAccountsData (d : SyncAccountsData)
  | peersRequest (r : PeersRequest)
  | peersResponse (r : PeersResponse)
  | blockHeadersRequest (hashes : Array CryptoHash)
  | blockHeaders (headers : Array BlockHeader)
  | blockRequest (hash : CryptoHash)
  | block (b : Block)
  /-- The optimistic block and the hash that the message carries beside it. -/
  | optimisticBlock (b : OptimisticBlock) (hash : CryptoHash)
  | transaction (t : SignedTransaction)
  | routed (m : RoutedMessage)
  | disconnect (d : Disconnect)
  | challenge (c : Challenge)
  | syncSnapshotHosts (hosts : Array SnapshotHostInfo)
  | stateRequestHeader (shardId : ShardId) (syncHash : CryptoHash)
  | stateRequestPart (shardId : ShardId) (syncHash : CryptoHash) (partId : UInt64)
  | versionedStateResponse (i : StateResponseInfo)
  | epochSyncRequest
  | epochSyncResponse (compressedProof : ByteArray)
  deriving BEq, Inhabited

/-- The limit on a transaction body. -/
def maxTransactionBytes : Nat :=
  16 * 1048576

/-- A message whose only field is a wrapped Borsh value, at `num`. -/
private def single [Codec α] (what : String) (b : ByteArray) (sl : Nat) : Except Error α := do
  let fs ← parseFields b Schemas.holder.wide sl
  let (m, msl) ← required what (lastSub fs 1)
  decodeWrapper what m msl

/-- Decodes the body of one member of the oneof of a `PeerMessage`. -/
def decodeMember (num : Nat) (b : ByteArray) (sl : Nat) : Except Error (Option PeerMessage) :=
  match num with
  | 27 => (fun h => some (.tier1Handshake h)) <$> decodeHandshake b sl
  | 4 => (fun h => some (.tier2Handshake h)) <$> decodeHandshake b sl
  | 33 => (fun h => some (.tier3Handshake h)) <$> decodeHandshake b sl
  | 5 => (fun (i, r) => some (.handshakeFailure i r)) <$> decodeHandshakeFailure b sl
  | 6 => (fun e => some (.lastEdge e)) <$> single (α := Edge) "edge" b sl
  | 7 => (fun u => some (.syncRoutingTable u)) <$> decodeRoutingTableUpdate b sl
  | 8 =>
    (fun p => some (.requestUpdateNonce p)) <$>
      single (α := PartialEdgeInfo) "partial_edge_info" b sl
  | 9 => (fun e => some (.syncRoutingTable ⟨#[e], #[]⟩)) <$> single (α := Edge) "edge" b sl
  | 25 => do
    let fs ← parseFields b Schemas.syncAccountsData.wide sl
    pure
        (some
          (.syncAccountsData
            ⟨← allMessages fs 1 decodeSignedAccountData, (lastBool fs 2).getD false,
              (lastBool fs 3).getD false⟩))
  | 10 => do
    let fs ← parseFields b [] sl
    pure (some (.peersRequest ⟨← lastU32 fs 1, ← lastU32 fs 2⟩))
  | 11 => do
    let fs ← parseFields b Schemas.peersResponse.wide sl
    let w := decodeWrapper (α := PeerInfo) "PeerInfo"
    pure (some (.peersResponse ⟨← allMessages fs 1 w, ← allMessages fs 2 w⟩))
  | 12 => do
    let fs ← parseFields b Schemas.holder.wide sl
    pure (some (.blockHeadersRequest (← allMessages fs 1 decodeHash)))
  | 13 => do
    let fs ← parseFields b Schemas.holder.wide sl
    pure
        (some (.blockHeaders (← allMessages fs 1 (decodeWrapper (α := BlockHeader) "BlockHeader"))))
  | 14 => do
    let fs ← parseFields b Schemas.holder.wide sl
    pure (some (.blockRequest (← required "block_hash" (← lastMessage fs 1 decodeHash))))
  | 15 => (fun x => some (.block x)) <$> single (α := Block) "block" b sl
  | 36 => do
    let fs ← parseFields b Schemas.optimisticBlock.wide sl
    let inner ←
      borshOf (α := OptimisticBlockInner) "OptimisticBlockInner"
          ((lastBytes fs 1).getD ByteArray.empty)
    let sig ← required "signature" (← lastMessage fs 2 decodeSignature)
    let hash ← required "hash" (← lastMessage fs 3 decodeHash)
    pure (some (.optimisticBlock ⟨inner, sig⟩ hash))
  | 16 => do
    let raw := (lastBytes (← parseFields b [] sl) 1).getD ByteArray.empty
    if raw.size > maxTransactionBytes then
      throw (.other "transaction too large")
    pure (some (.transaction (← borshOf "SignedTransaction" raw)))
  | 17 => (fun m => some (.routed m)) <$> decodeRouted b sl
  | 37 => (fun m => some (.routed m)) <$> decodeRoutedV3 b sl
  | 18 => do
    let fs ← parseFields b [] sl
    pure (some (.disconnect ⟨(lastBool fs 1).getD false⟩))
  | 19 => do
    let fs ← parseFields b [] sl
    pure (some (.challenge (← borshOf "Challenge" ((lastBytes fs 1).getD ByteArray.empty))))
  | 32 => do
    let fs ← parseFields b Schemas.syncSnapshotHosts.wide sl
    pure (some (.syncSnapshotHosts (← allMessages fs 1 decodeSnapshotHostInfo)))
  | 29 => do
    let fs ← parseFields b Schemas.stateRequestHeader.wide sl
    pure
        (some
          (.stateRequestHeader ((lastU64 fs 1).getD 0)
            (← required "sync_hash" (← lastMessage fs 2 decodeHash))))
  | 30 => do
    let fs ← parseFields b Schemas.stateRequestPart.wide sl
    pure
        (some
          (.stateRequestPart ((lastU64 fs 1).getD 0)
            (← required "sync_hash" (← lastMessage fs 2 decodeHash)) ((lastU64 fs 3).getD 0)))
  | 31 =>
    (fun i => some (.versionedStateResponse i)) <$>
      single (α := StateResponseInfo) "state_response_info" b sl
  | 34 => pure (some .epochSyncRequest)
  | 35 => do
    let fs ← parseFields b [] sl
    pure (some (.epochSyncResponse ((lastBytes fs 1).getD ByteArray.empty)))
  | _ => pure none

/-- `PeerMessage::deserialize`: the whole message is checked as `protobuf` checks it, then the member
that comes last is converted. -/
def PeerMessage.decode (data : ByteArray) : Except Error PeerMessage := do
  validate Schemas.peerMessage data (topSlack data)
  let fs ← parseFields data Schemas.peerMessage.wide (topSlack data)
  let mut last : Option (Nat × ByteArray × Nat) := none
  for f in fs do
    if let .bytes b sl := f.val then
      if Schemas.peerMessageMembers.any (·.1 == f.num) then
        last := some (f.num, b, sl)
  match last with
  | some (num, b, sl) =>
    required "message_type" (← decodeMember num b sl)
  | none =>
    throw (.missing "message_type")

/-- `PeerMessage::max_size`: the size above which an incoming message of this type is dropped. -/
def PeerMessage.maxSize (m : PeerMessage) : Nat :=
  let small := 512 * 1024
  let medium := 32 * 1048576
  match m with
  | .blockRequest _ | .blockHeadersRequest _ | .stateRequestHeader _ _ | .stateRequestPart _ _ _ |
    .requestUpdateNonce _ | .tier1Handshake _ | .tier2Handshake _ | .tier3Handshake _ |
    .disconnect _ | .handshakeFailure _ _ | .lastEdge _ | .peersRequest _ | .challenge _ |
    .epochSyncRequest => small
  | .peersResponse _ | .transaction _ | .syncRoutingTable _ | .syncAccountsData _ |
    .syncSnapshotHosts _ | .blockHeaders _ | .block _ | .optimisticBlock _ _ => medium
  | .versionedStateResponse _ => 128 * 1048576
  | .epochSyncResponse _ => 512 * 1048576
  | .routed r => r.body.maxSize

/-- A `PeerMessage` with the member of the oneof at `num`. -/
private def member (num : Nat) (body : ByteArray) : ByteArray :=
  putBytesField ByteArray.empty num body

/-- `PeerMessage::serialize` without a trace context. -/
def PeerMessage.encode (m : PeerMessage) : ByteArray :=
  match m with
  | .tier1Handshake h => member 27 (encodeHandshake h)
  | .tier2Handshake h => member 4 (encodeHandshake h)
  | .tier3Handshake h => member 33 (encodeHandshake h)
  | .handshakeFailure i r => member 5 (encodeHandshakeFailure i r)
  | .lastEdge e => member 6 (putBytesField ByteArray.empty 1 (encodeWrapper e))
  | .syncRoutingTable u => member 7 (encodeRoutingTableUpdate u)
  | .requestUpdateNonce p => member 8 (putBytesField ByteArray.empty 1 (encodeWrapper p))
  | .syncAccountsData d =>
    let b :=
      d.accountsData.foldl (fun b a => putBytesField b 1 (encodeSignedPayload a.payload))
        ByteArray.empty
    member 25 (putBool (putBool b 2 d.incremental) 3 d.requestingFullSync)
  | .peersRequest r =>
    let b :=
      match r.maxPeers with
      | some v => putVarintField ByteArray.empty 1 v.toUInt64
      | none => ByteArray.empty
    let b :=
      match r.maxDirectPeers with
      | some v => putVarintField b 2 v.toUInt64
      | none => b
    member 10 b
  | .peersResponse r =>
    let b := r.peers.foldl (fun b p => putBytesField b 1 (encodeWrapper p)) ByteArray.empty
    member 11 (r.directPeers.foldl (fun b p => putBytesField b 2 (encodeWrapper p)) b)
  | .blockHeadersRequest hs =>
    member 12 (hs.foldl (fun b h => putBytesField b 1 (encodeHash h)) ByteArray.empty)
  | .blockHeaders hs =>
    member 13 (hs.foldl (fun b h => putBytesField b 1 (encodeWrapper h)) ByteArray.empty)
  | .blockRequest h => member 14 (putBytesField ByteArray.empty 1 (encodeHash h))
  | .block b => member 15 (putBytesField ByteArray.empty 1 (encodeWrapper b))
  | .optimisticBlock o hash =>
    let b := putBytes ByteArray.empty 1 (Codec.encode o.inner)
    let b := putMessage b 2 (some (encodeSignature o.signature))
    member 36 (putMessage b 3 (some (encodeHash hash)))
  | .transaction t => member 16 (encodeWrapper t)
  | .routed r => member 17 (encodeRouted r)
  | .disconnect d => member 18 (putBool ByteArray.empty 1 d.removeFromConnectionStore)
  | .challenge c => member 19 (encodeWrapper c)
  | .syncSnapshotHosts hs =>
    member 32 (hs.foldl (fun b h => putBytesField b 1 (encodeSnapshotHostInfo h)) ByteArray.empty)
  | .stateRequestHeader s h =>
    member 29 (putMessage (putU64 ByteArray.empty 1 s) 2 (some (encodeHash h)))
  | .stateRequestPart s h p =>
    member 30 (putU64 (putMessage (putU64 ByteArray.empty 1 s) 2 (some (encodeHash h))) 3 p)
  | .versionedStateResponse i => member 31 (putBytesField ByteArray.empty 1 (encodeWrapper i))
  | .epochSyncRequest => member 34 ByteArray.empty
  | .epochSyncResponse p => member 35 (putBytes ByteArray.empty 1 p)

end Near.Node.Network
