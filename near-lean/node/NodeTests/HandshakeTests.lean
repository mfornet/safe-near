import NearNode.Net.Mem
import NearNode.Network.Peer

/-!
`node-handshake-tests`: the two sides of the handshake against each other on the in-memory network:
a valid handshake, a chain with another genesis, a bad signature, a version that is not spoken, a
stale nonce, a wrong target, a `LastEdge` answer, owned accounts, and what a link does with frames.
-/

open Near.Node Near.Node.Net Near.Node.Network

private initialize checks : IO.Ref Nat ←
  IO.mkRef 0

private def check (failures : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  checks.modify (· + 1)
  if !ok then
    IO.eprintln s!"FAIL {name}"
    failures.modify (· + 1)

private def seedBytes (n : Nat) : ByteArray :=
  ByteArray.mk ((Array.range 32).map fun i => (i * 7 + n).toUInt8)

private def keyOf (n : Nat) : NodeKey :=
  (NodeKey.ofSeed? (seedBytes n)).get!

private def genesisOf (n : Nat) : GenesisId :=
  ⟨"localnet", ⟨ByteArray.mk (Array.replicate 32 n.toUInt8)⟩⟩

private def configOf (key : Nat) (genesis : Nat) (port : Option UInt16 := some 24567) : Config :=
  { key := keyOf key, genesisId := genesisOf genesis, listenPort := port }

private def addr (n : UInt8) (port : UInt16) : Addr :=
  ⟨ByteArray.mk #[10, 0, 0, n], port⟩

/-- Runs the inbound side of the node `b` on one accepted connection, in a task. -/
private def serve (b : Config) (clock : Clock) (hub : Mem.Hub) (at_ : Addr)
    (existing : PeerId → Option Edge := fun _ => none) :
    IO (Task (Except IO.Error (Except HandshakeError Link))) := do
  let l ← hub.net.listen at_
  IO.asTask do
      let some s ← l.accept 5000 | throw (IO.userError "nothing to accept")
      handshakeInbound b clock s existing 0

private def outbound (a : Config) (clock : Clock) (hub : Mem.Hub) (to : Addr) (peer : PeerId)
    (existing : Option Edge := none) : IO (Except HandshakeError Link) := do
  let s ← hub.net.connect to 1000
  let r ← handshakeOutbound a clock s peer .t2 existing 7
  if let .error _ := r then
    s.close
  pure r

private def okLink : Except HandshakeError Link → Option Link
  | .ok l => some l
  | .error _ => none

private def errorOf : Except HandshakeError Link → Option HandshakeError
  | .error e => some e
  | .ok _ => none

def now : Nat :=
  1700000000

def main (_ : List String) : IO UInt32 := do
  let failures ← IO.mkRef 0
  let clock : Clock := pure now
  let (a, b) := (configOf 1 0, configOf 2 0)
  -- a valid handshake
  do
    let hub ← Mem.Hub.new
    let task ← serve b clock hub (addr 2 24567)
    let ra ← outbound a clock hub (addr 2 24567) b.key.peerId
    let rb ← IO.ofExcept (← IO.wait task)
    check failures "valid: both sides complete" (ra.toOption.isSome && rb.toOption.isSome)
    if let (some la, some lb) := (okLink ra, okLink rb) then
      check failures "valid: the edges are the same and verify"
          (la.edge == lb.edge && la.edge.verify)
      check failures "valid: the nonce is the time made odd" (la.edge.nonce == 1700000001)
      check failures "valid: peers" (la.peer == b.key.peerId && lb.peer == a.key.peerId)
      check failures "valid: version" (la.protocolVersion == 86 && lb.protocolVersion == 86)
      check failures "valid: the listen port reaches the peer"
          (lb.theirs.senderListenPort == some 24567)
      check failures "valid: the height reaches the peer" (lb.theirs.senderChainInfo.height == 7)
      check failures "valid: who opened" (la.outbound && !lb.outbound)
      -- and then messages in both directions
      la.send (.peersRequest ⟨some 5, none⟩)
      match ← lb.recv 1000 with
      | .message (.peersRequest r) _ =>
        check failures "valid: a message arrives" (r == ⟨some 5, none⟩)
      | _ =>
        check failures "valid: a message arrives" false
      lb.send (.disconnect ⟨true⟩)
      match ← la.recv 1000 with
      | .message (.disconnect d) _ =>
        check failures "valid: disconnect" d.removeFromConnectionStore
      | _ =>
        check failures "valid: disconnect" false
      -- a frame that is not a message is dropped, and so is one that is too large for its type
      la.framed.send (ByteArray.mk #[0xff, 0xff, 0xff])
      match ← lb.recv 1000 with
      | .undecodable 3 =>
        pure ()
      | _ =>
        check failures "valid: an undecodable frame is reported" false
      let big := PeerMessage.requestUpdateNonce ⟨5, .ed25519 (ByteArray.mk (Array.replicate 64 0))⟩
      la.framed.send (big.encode ++ ByteArray.mk (Array.replicate (600 * 1024) 0))
      match ← lb.recv 1000 with
      | .undecodable _ | .oversized _ =>
        pure ()
      | _ =>
        check failures "valid: an oversized frame is dropped" false
      la.close
      match ← lb.recv 1000 with
      | .closed _ =>
        pure ()
      | _ =>
        check failures "valid: close is seen" false
  -- another genesis
  do
    let hub ← Mem.Hub.new
    let c := configOf 2 9
    let task ← serve c clock hub (addr 2 24567)
    let ra ← outbound a clock hub (addr 2 24567) c.key.peerId
    let rb ← IO.ofExcept (← IO.wait task)
    check failures "genesis: the dialer is told which genesis the peer has"
        (errorOf ra == some (.failure (.genesisMismatch (genesisOf 9))))
    check failures "genesis: the acceptor does not complete" (rb.toOption.isNone)
  -- a signature that is not the dialer's
  do
    let hub ← Mem.Hub.new
    let task ← serve b clock hub (addr 2 24567)
    let s ← hub.net.connect (addr 2 24567) 1000
    let f ← Framed.new s
    let spec := a.propose b.key.peerId .t2 now none
    let bad : Signature := .ed25519 (ByteArray.mk (Array.replicate 64 1))
    f.send (a.hello { spec with edge := { spec.edge with signature := bad } } 0).encode
    let rb ← IO.ofExcept (← IO.wait task)
    check failures "bad signature: the acceptor refuses the edge" (errorOf rb == some .invalidEdge)
    s.close
  -- versions
  do
    let hub ← Mem.Hub.new
    let task ← serve b clock hub (addr 2 24567)
    let newer :=
      { a with
        protocolVersion := 100, oldestSupported := 90 }
    let ra ← outbound newer clock hub (addr 2 24567) b.key.peerId
    let rb ← IO.ofExcept (← IO.wait task)
    -- 86 is below the dialer's oldest, so it cannot retry
    check failures "version: dialer that is too new does not agree on 86"
        (errorOf ra == some (.failure (.protocolVersionMismatch 86 83)))
    check failures "version: acceptor completes nothing" rb.toOption.isNone
  do
    let hub ← Mem.Hub.new
    let l ← hub.net.listen (addr 2 24567)
    let task ←
      IO.asTask do
          -- the acceptor sees a first handshake it refuses and a second it takes
          let some s ← l.accept 5000 | throw (IO.userError "nothing to accept")
          handshakeInbound b clock s (fun _ => none) 0
    let newer := { a with protocolVersion := 100 }
    let ra ← outbound newer clock hub (addr 2 24567) b.key.peerId
    let rb ← IO.ofExcept (← IO.wait task)
    check failures "version: a newer dialer settles on 86"
        ((okLink ra).map (·.protocolVersion) == some 86 &&
          (okLink rb).map (·.protocolVersion) == some 86)
  do
    let hub ← Mem.Hub.new
    let task ← serve b clock hub (addr 2 24567)
    let older :=
      { a with
        protocolVersion := 70, oldestSupported := 60 }
    let ra ← outbound older clock hub (addr 2 24567) b.key.peerId
    let rb ← IO.ofExcept (← IO.wait task)
    check failures "version: a dialer below the oldest version is refused"
        (errorOf ra == some (.failure (.protocolVersionMismatch 86 83)) && rb.toOption.isNone)
  -- a nonce that is an hour old
  do
    let hub ← Mem.Hub.new
    let task ← serve b clock hub (addr 2 24567)
    let ra ← outbound a (pure (now - 3600)) hub (addr 2 24567) b.key.peerId
    let rb ← IO.ofExcept (← IO.wait task)
    check failures "nonce: a stale nonce is refused" (errorOf rb == some .badNonce)
    check failures "nonce: and the dialer does not complete" ra.toOption.isNone
  -- a peer id that is not the acceptor's
  do
    let hub ← Mem.Hub.new
    let task ← serve b clock hub (addr 2 24567)
    let ra ← outbound a clock hub (addr 2 24567) (keyOf 5).peerId
    let _ ← IO.wait task
    check failures "target: the dialer is told it reached someone else"
        (errorOf ra == some (.failure .invalidTarget))
  -- an edge with a higher nonce is held: the acceptor shows it, the dialer signs a newer one
  do
    let hub ← Mem.Hub.new
    let held :=
      Edge.new a.key.peerId b.key.peerId 1700000051
        (a.key.sign (Edge.buildHash a.key.peerId b.key.peerId 1700000051).bytes)
        (b.key.sign (Edge.buildHash a.key.peerId b.key.peerId 1700000051).bytes)
    let task ←
      serve b clock hub (addr 2 24567) (fun p => if p == a.key.peerId then some held else none)
    let ra ← outbound a clock hub (addr 2 24567) b.key.peerId
    let rb ← IO.ofExcept (← IO.wait task)
    check failures "last edge: the dialer proposes the next nonce and both complete"
        ((okLink ra).map (·.edge.nonce) == some 1700000053 &&
          (okLink rb).map (·.edge.nonce) == some 1700000053)
  -- a last edge that is not valid for the pair is a failure of the dialer
  do
    let hub ← Mem.Hub.new
    let other := configOf 6 0
    let held :=
      Edge.new a.key.peerId other.key.peerId 1700000051
        (a.key.sign (Edge.buildHash a.key.peerId other.key.peerId 1700000051).bytes)
        (other.key.sign (Edge.buildHash a.key.peerId other.key.peerId 1700000051).bytes)
    let task ← serve b clock hub (addr 2 24567) (fun _ => some held)
    let ra ← outbound a clock hub (addr 2 24567) b.key.peerId
    let _ ← IO.wait task
    check failures "last edge: an edge between other peers is refused"
        (errorOf ra == some .invalidLastEdge)
  -- owned accounts
  let owned (peer : Config) (signer : NodeKey) (ts : Int) : SignedOwnedAccount :=
    let account : OwnedAccount := ⟨.ed25519 signer.signing.publicKey, peer.key.peerId, ⟨ts, 0⟩⟩
    let payload := encodeOwnedAccountPayload account
    ⟨account, ⟨payload, signer.sign payload⟩⟩
  let withOwned (o : SignedOwnedAccount) (expected : Option HandshakeError) (name : String) :
    IO Unit := do
    let hub ← Mem.Hub.new
    let task ← serve b clock hub (addr 2 24567)
    let s ← hub.net.connect (addr 2 24567) 1000
    let f ← Framed.new s
    let spec := a.propose b.key.peerId .t2 now none
    let msg := a.hello spec 0
    let msg :=
      match msg with
      | .tier2Handshake h => PeerMessage.tier2Handshake { h with ownedAccount := some o }
      | m => m
    f.send msg.encode
    let rb ← IO.ofExcept (← IO.wait task)
    check failures s!"owned account: {name}" (errorOf rb == expected)
    s.close
  let validator := keyOf 8
  withOwned (owned a validator (now : Nat)) none "a valid one"
  withOwned (owned (configOf 4 0) validator (now : Nat)) (some .ownedAccountMismatch)
      "another owner"
  withOwned (owned a validator (now - 4000 : Nat)) (some .clockSkew) "too old"
  let o := owned a validator (now : Nat)
  withOwned
      { o with
        payload := { o.payload with signature := .ed25519 (ByteArray.mk (Array.replicate 64 2)) } }
      (some .ownedAccountSignature) "a bad signature"
  -- nobody answers
  do
    let hub ← Mem.Hub.new
    let l ← hub.net.listen (addr 2 24567)
    let s ← hub.net.connect (addr 2 24567) 1000
    let _ ← l.accept 1000
    let started ← IO.monoMsNow
    -- a shorter wait than the real one: the dialer gives up when its deadline passes
    let f ← Framed.new s
    match ← f.recv 100 with
    | .timeout =>
      pure ()
    | _ =>
      check failures "silence is a timeout" false
    check failures "silence: the wait is bounded" ((← IO.monoMsNow) - started < 5000)
  let n ← failures.get
  IO.println s!"handshake tests: {← checks.get} checks, {n} failures"
  return if n == 0 then 0 else 1
