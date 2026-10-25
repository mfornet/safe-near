import Std.Time
import NearNode.Net
import NearNode.Network.Handshake

/-!
# A peer connection

`Link` is a connection whose handshake is done. `connect` and `accept` run the two sides of the
handshake of `peer_actor.rs` over a `Framed` stream: the outbound side sends its handshake, waits for
the answer for `handshake_timeout` (20 s on the localnets) and retries as `handle_msg_connecting`
does (a version both sides speak, a newer nonce after a `LastEdge`); the inbound side answers.
`Link.recv` is the receive loop of the `PeerActor`: a frame that does not decode is dropped and a
message larger than its type allows is dropped, neither closes the connection.
-/

namespace Near.Node.Network

open Near.Node Near.Node.Net

/-- The clock of a node, in Unix seconds. -/
abbrev Clock :=
  IO Nat

/-- `Timestamp::now` as Unix seconds. -/
def systemClock : Clock := do
  let t ← Std.Time.Timestamp.now
  pure t.toSecondsSinceUnixEpoch.val.toNat

/-- A connection whose handshake completed. -/
structure Link where
  framed : Framed
  /-- The peer at the other end, with the address it was reached at. -/
  peer : PeerId
  addr : Addr
  tier : Tier
  /-- The edge both signed. -/
  edge : Edge
  /-- The version both speak. -/
  protocolVersion : UInt32
  /-- The peer's handshake: its chain, height and the port it listens on. -/
  theirs : Handshake
  /-- Whether this node opened the connection. -/
  outbound : Bool

/-- `HandshakeStartedEvent` to `ConnectionClosed`: what happened to a received frame. -/
inductive Incoming where
  | message (m : PeerMessage) (size : Nat)
  | timeout
  | closed (why : String)
  /-- The frame is not a `PeerMessage`; nearcore ignores it. -/
  | undecodable (size : Nat)
  /-- The message is larger than its type allows; nearcore ignores it. -/
  | oversized (size : Nat)

/-- `handshake_timeout` of the localnets, in milliseconds. -/
def handshakeTimeoutMs : Nat :=
  20000

/-- Reads the next message. -/
def Link.recv (l : Link) (timeoutMs : Nat) : IO Incoming := do
  match ← l.framed.recv timeoutMs with
  | .timeout =>
    pure .timeout
  | .closed .eof =>
    pure (.closed "end of stream")
  | .closed (.error e) =>
    pure (.closed e)
  | .tooLarge n =>
    pure (.closed s!"message of {n} bytes")
  | .message bytes =>
    match PeerMessage.decode bytes with
    | .error _ =>
      pure (.undecodable bytes.size)
    | .ok m =>
      pure (if bytes.size > m.maxSize then .oversized bytes.size else .message m bytes.size)

/-- Sends a message. -/
def Link.send (l : Link) (m : PeerMessage) : IO Unit :=
  l.framed.send m.encode

def Link.close (l : Link) : IO Unit :=
  l.framed.close

/-- Waits for the next handshake-level message; messages that are not part of the handshake are
skipped, as `handle_msg_connecting` does. -/
private partial def awaitMessage (f : Framed) (deadline : Nat) :
    IO (Except HandshakeError PeerMessage) := do
  let now ← IO.monoMsNow
  if now ≥ deadline then
    return .error (.closed "handshake timeout")
  match ← f.recv (deadline - now) with
  | .timeout =>
    return .error (.closed "handshake timeout")
  | .closed _ =>
    return .error (.closed "connection closed")
  | .tooLarge _ =>
    return .error (.closed "message too large")
  | .message bytes =>
    match PeerMessage.decode bytes with
    | .error _ =>
      awaitMessage f deadline
    | .ok (.disconnect _) =>
      return .error (.closed "the peer disconnected")
    | .ok m =>
      return .ok m

/-- The outbound side of the handshake on an open stream. `existing` is the edge held with the peer
and `height` this node's height. -/
partial def handshakeOutbound (cfg : Config) (clock : Clock) (stream : Stream) (peer : PeerId)
    (tier : Tier) (existing : Option Edge) (height : UInt64) : IO (Except HandshakeError Link) := do
  let f ← Framed.new stream
  let deadline := (← IO.monoMsNow) + handshakeTimeoutMs
  let rec attempt (spec : Spec) : IO (Except HandshakeError Link) := do
    f.send (cfg.hello spec height).encode
    let rec wait : IO (Except HandshakeError Link) := do
      match ← awaitMessage f deadline with
      | .error e =>
        return .error e
      | .ok m =>
        match m.asHandshake? with
        | some (t, h) =>
          match cfg.checkReply spec t h (← clock) with
          | .error e =>
            return .error e
          | .ok edge =>
            return .ok
                { framed := f, peer := h.senderPeerId, addr := stream.peer, tier := t, edge,
                  protocolVersion := h.protocolVersion, theirs := h, outbound := true }
        | none =>
          match cfg.onFailure spec (← clock) m with
          | .stop e =>
            return .error e
          | .again spec' =>
            attempt spec'
    wait
  attempt (cfg.propose peer tier (← clock) existing)

/-- The inbound side of the handshake on an accepted stream. -/
partial def handshakeInbound (cfg : Config) (clock : Clock) (stream : Stream)
    (existing : PeerId → Option Edge) (height : UInt64) : IO (Except HandshakeError Link) := do
  let f ← Framed.new stream
  let deadline := (← IO.monoMsNow) + handshakeTimeoutMs
  let rec wait : IO (Except HandshakeError Link) := do
    match ← awaitMessage f deadline with
    | .error e =>
      return .error e
    | .ok m =>
      match m.asHandshake? with
      | none =>
        wait
      | some (tier, h) =>
        match cfg.checkInbound tier h (← clock) (existing h.senderPeerId) height with
        | .reject e =>
          return .error e
        | .answer reply =>
          f.send reply.encode
          wait
        | .accept reply edge =>
          f.send reply.encode
          return .ok
              { framed := f, peer := h.senderPeerId, addr := stream.peer, tier, edge,
                protocolVersion := h.protocolVersion, theirs := h, outbound := false }
  wait

end Near.Node.Network
