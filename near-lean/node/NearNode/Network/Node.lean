import Lean.Data.Json
import NearNode.Net
import NearNode.Chain.Bootstrap
import NearNode.Network.Peer
import NearNode.Network.Driver

/-!
# The node as a peer

The connection loop of a `PeerActor` that is `Ready` (`chain/network/src/peer/peer_actor.rs`) and
the node that runs it against a boot node.

On a new connection the node sends what nearcore sends: its routing table (the edges it knows, now
the one it just signed), its snapshot hosts (none), and, on the connection it opened, a full sync
of account data. Then, every minute (`REQUEST_PEERS_INTERVAL`, `SYNC_LATEST_BLOCK_INTERVAL`), a
`PeersRequest` and its latest block: a peer closes a connection that is silent for two minutes
(`READ_TIMEOUT`). Every ten minutes the dialer asks for a newer nonce of the edge
(`RequestUpdateNonce`), as `PRUNE_EDGES_AFTER / 3` is. It answers `PeersRequest`,
`SyncAccountsData`, `RequestUpdateNonce`, `BlockHeadersRequest`, `BlockRequest` and `Ping`; checks
every edge and every routed message signature it is given and closes the connection on an invalid
one (nearcore bans the peer); and hands blocks, headers and chunk responses to the sync driver.
-/

namespace Near.Node.Network

open Near.Node Near.Node.Net Near.Node.Borsh

/-- `REQUEST_PEERS_INTERVAL`, `SYNC_LATEST_BLOCK_INTERVAL`: a minute. -/
def minuteMs : Nat :=
  60000

/-- `PRUNE_EDGES_AFTER / 3` and `ACCOUNTS_DATA_FULL_SYNC_INTERVAL`: ten minutes. -/
def tenMinutesMs : Nat :=
  600000

/-- The name of a message for the counters. -/
def PeerMessage.name : PeerMessage → String
  | .tier1Handshake _ => "Tier1Handshake"
  | .tier2Handshake _ => "Tier2Handshake"
  | .tier3Handshake _ => "Tier3Handshake"
  | .handshakeFailure _ _ => "HandshakeFailure"
  | .lastEdge _ => "LastEdge"
  | .syncRoutingTable _ => "SyncRoutingTable"
  | .requestUpdateNonce _ => "RequestUpdateNonce"
  | .syncAccountsData _ => "SyncAccountsData"
  | .peersRequest _ => "PeersRequest"
  | .peersResponse _ => "PeersResponse"
  | .blockHeadersRequest _ => "BlockHeadersRequest"
  | .blockHeaders _ => "BlockHeaders"
  | .blockRequest _ => "BlockRequest"
  | .block _ => "Block"
  | .optimisticBlock _ _ => "OptimisticBlock"
  | .transaction _ => "Transaction"
  | .routed _ => "Routed"
  | .disconnect _ => "Disconnect"
  | .challenge _ => "Challenge"
  | .syncSnapshotHosts _ => "SyncSnapshotHosts"
  | .stateRequestHeader _ _ => "StateRequestHeader"
  | .stateRequestPart _ _ _ => "StateRequestPart"
  | .versionedStateResponse _ => "VersionedStateResponse"
  | .epochSyncRequest => "EpochSyncRequest"
  | .epochSyncResponse _ => "EpochSyncResponse"

/-- The edges a node knows, by the pair of peers (the Borsh of the two ids). -/
abbrev Graph :=
  Std.HashMap (ByteArray × ByteArray) Edge

/-- Adds an edge if it is newer than the one held for the pair. -/
def Graph.add (g : Graph) (e : Edge) : Graph :=
  let key := (Codec.encode e.key0, Codec.encode e.key1)
  match g[key]? with
  | some old => if old.nonce ≥ e.nonce then g else g.insert key e
  | none => g.insert key e

/-- What the connection loop needs from the rest of the node. -/
structure Hooks where
  tick : IO Unit
  onHeaders : Array BlockHeader → IO Unit
  onBlock : Block → IO Unit
  onRouted : RoutedMessage → IO Unit
  /-- A state sync response, which arrives on a Tier 3 connection the peer opens to this node. -/
  onStateResponse : StateResponseInfo → IO Unit
  /-- The block sent to the peer every minute. -/
  latestBlock : IO (Option Block)
  headersAfter : Array CryptoHash → IO (Array BlockHeader)
  blockOf : CryptoHash → IO (Option Block)
  /-- A line for the log. -/
  status : IO String

/-- The state shared by the loops of a node. -/
structure Env where
  cfg : Config
  clock : Clock
  outbox : IO.Ref (Array PeerMessage)
  graph : IO.Ref Graph
  stop : IO.Ref Bool
  /-- Messages received, by name. -/
  counts : IO.Ref (Std.HashMap String Nat)
  /-- Edges received and found valid, and invalid. -/
  edgesOk : IO.Ref Nat
  edgesBad : IO.Ref Nat
  /-- The log. -/
  log : String → IO Unit

/-- How a connection ended. -/
structure Ended where
  reason : String
  /-- Whether the peer sent `Disconnect`. -/
  byPeer : Bool

private def count (env : Env) (name : String) : IO Unit :=
  env.counts.modify fun m => m.insert name (m.getD name 0 + 1)

/-- Handles one message. Returns a reason to close the connection. -/
private def handle (env : Env) (hooks : Hooks) (link : Link) (m : PeerMessage) :
    IO (Option Ended) := do
  count env m.name
  let reply (r : PeerMessage) : IO Unit := env.outbox.modify (·.push r)
  match m with
  | .disconnect _ =>
    return some ⟨"the peer sent Disconnect", true⟩
  | .tier1Handshake _ | .tier2Handshake _ | .tier3Handshake _ =>
    return some ⟨"a second handshake", false⟩
  | .peersRequest _ =>
    pure ()
  | .peersResponse r =>
    if r.peers.size > 1000 || r.directPeers.size > 128 then
      return some ⟨"too many peers in PeersResponse", false⟩
  | .requestUpdateNonce info =>
    let now ← env.clock
    if !verifyNonce now info.nonce then
      return some ⟨"RequestUpdateNonce with a bad nonce", false⟩
    let held :=
      (←
          env.graph.get)[(Codec.encode (Edge.makeKey env.cfg.key.peerId link.peer).1,
          Codec.encode (Edge.makeKey env.cfg.key.peerId link.peer).2)]?
    match held with
    | some e =>
      if e.isActive && e.nonce ≥ info.nonce then
        reply (.syncRoutingTable ⟨#[e], #[]⟩)
        return none
    | none =>
      pure ()
    let mine := env.cfg.key.partialEdge link.peer info.nonce
    let e := env.cfg.mergeEdge link.peer info.nonce mine.signature info.signature
    if !e.verify then
      return some ⟨"RequestUpdateNonce with an invalid signature", false⟩
    env.graph.modify (·.add e)
    reply (.syncRoutingTable ⟨#[e], #[]⟩)
  | .syncRoutingTable u =>
    let mut bad := false
    for e in u.edges do
      if e.verify then
        env.edgesOk.modify (· + 1)
      else
        env.edgesBad.modify (· + 1)
        bad := true
    if bad then
      return some ⟨"an invalid edge in SyncRoutingTable", false⟩
    env.graph.modify fun g => u.edges.foldl Graph.add g
  | .lastEdge e =>
    if !e.verify then
      return some ⟨"an invalid LastEdge", false⟩
  | .syncAccountsData d =>
    if d.requestingFullSync then
      reply (.syncAccountsData ⟨#[], false, false⟩)
  | .syncSnapshotHosts _ =>
    pure ()
  | .blockHeadersRequest hashes =>
    if hashes.size > 20 then
      return some ⟨"BlockHeadersRequest with too many hashes", false⟩
    let hs ← hooks.headersAfter hashes
    reply (.blockHeaders hs)
  | .blockRequest h =>
    if let some b← hooks.blockOf h then
      reply (.block b)
  | .blockHeaders hs =>
    hooks.onHeaders hs
  | .block b =>
    hooks.onBlock b
  | .versionedStateResponse i =>
    hooks.onStateResponse i
  | .routed r =>
    if !r.verify then
      return some ⟨"a routed message with an invalid signature", false⟩
    let forMe :=
      match r.target with
      | .peerId p => p == env.cfg.key.peerId
      | .hash _ => true
    if forMe then
      match r.body with
      | .ping p =>
        let target := PeerIdOrHash.hash r.hash
        let body := RoutedBody.pong ⟨p.nonce, env.cfg.key.peerId⟩
        let h := CryptoHash.hashBorsh (target, env.cfg.key.peerId, body)
        reply
            (.routed
              { target, author := env.cfg.key.peerId, ttl := 100, body,
                signature := some (env.cfg.key.sign h.bytes), createdAt := some (← env.clock),
                numHops := 0 })
      | _ =>
        hooks.onRouted r
  | _ =>
    pure ()
  return none

/-- The loop over one connection until it ends. -/
partial def runLink (env : Env) (hooks : Hooks) (link : Link) : IO Ended := do
  let started ← IO.monoMsNow
  -- what a new connection sends; a Tier 3 connection only carries state sync responses
  let graph ← env.graph.get
  if link.tier != .t3 then
    env.outbox.modify (·.push (.syncRoutingTable ⟨graph.toArray.map (·.2), #[]⟩))
    env.outbox.modify (·.push (.syncSnapshotHosts #[]))
    if link.outbound then
      env.outbox.modify (·.push (.syncAccountsData ⟨#[], false, true⟩))
  let mut lastPeers : Option Nat := none
  let mut lastBlock : Option Nat := none
  let mut lastNonce := started
  let mut lastReport := started
  let mut result : Option Ended := none
  while result.isNone do
    if ← env.stop.get then
      result := some ⟨"stopped", false⟩
      break
    let now ← IO.monoMsNow
    -- the periodic messages
    if link.tier != .t3 && lastPeers.all (fun t => now - t ≥ minuteMs) then
      env.outbox.modify (·.push (.peersRequest ⟨some 32, some 128⟩))
      lastPeers := some now
    if link.tier != .t3 && lastBlock.all (fun t => now - t ≥ minuteMs) then
      if let some b← hooks.latestBlock then
        env.outbox.modify (·.push (.block b))
      lastBlock := some now
    if link.outbound && now - lastNonce ≥ tenMinutesMs then
      let nonce := freshNonce (← env.clock)
      env.outbox.modify (·.push (.requestUpdateNonce (env.cfg.key.partialEdge link.peer nonce)))
      lastNonce := now
    if now - lastReport ≥ 2000 then
      let line ← hooks.status
      if !line.isEmpty then
        env.log line
      lastReport := now
    hooks.tick
    -- everything queued goes out
    let out ← env.outbox.modifyGet fun o => (o, #[])
    for m in out do
      try
        link.send m
      catch e =>
        result := some ⟨s!"send failed: {e}", false⟩
        break
    if result.isSome then
      break
    match ← link.recv 20 with
    | .timeout =>
      pure ()
    | .closed why =>
      result := some ⟨why, false⟩
    | .undecodable n =>
      env.log s!"dropped a frame of {n} bytes that is not a PeerMessage"
    | .oversized n =>
      env.log s!"dropped a message of {n} bytes: larger than its type allows"
    | .message m _ =>
      result := ← handle env hooks link m
  let ended := result.getD ⟨"ended", false⟩
  if !ended.byPeer then
    try
      link.send (.disconnect ⟨false⟩)
    catch _ =>
      pure ()
  link.close
  return ended

end Near.Node.Network
