import Lean.Data.Json
import NodeConformance.Runner
import NearNode.Protocol
import NearNode.Network.Message

/-!
`node-conformance-network [DIR]`: the peer protocol against the fixtures that
`tools/localnet/network_oracle.rs` writes with nearcore's own `network_protocol` code
(default `near-lean/node/fixtures/network`; `just node-conformance-network` regenerates nothing).

* `PeerMessage.jsonl`: protobuf bytes in `proto`. nearcore's `PeerMessage::deserialize` accepted
  them (the line has `canonical`, what `PeerMessage::serialize` writes for the decoded value, unless
  it is the input itself) or rejected them. The Lean decoder must agree, its encoder must write the
  canonical bytes, and the derived values (the size limit, the signature checks, the routed message
  hash) must be the ones nearcore computes.
* the Borsh types of the network, checked as the M1 types are, with derived values: the hash and
  verdict of an `Edge`, the tiered form of a routed body, the hash of a routed message.
-/

open Lean Near.Node Near.Node.Conformance Near.Node.Network Near.Node.Borsh

private def u64Hex (n : Nat) : ByteArray :=
  Codec.encode n.toUInt64

private def flags (bs : List Bool) : ByteArray :=
  ByteArray.mk (bs.map fun b => if b then 1 else 0).toArray

/-- The signature checks of a handshake that nearcore performs when it registers the connection. -/
private def handshakeDerived (h : Handshake) : List (String × ByteArray) :=
  let edgeOk := h.partialEdgeInfo.verify h.targetPeerId h.senderPeerId
  let owned : UInt8 :=
    match h.ownedAccount with
    | none => 2
    | some o =>
      if Chain.verifySignature o.payload.signature o.payload.payload o.account.accountKey then 1
      else 0
  [("partialEdgeOk", flags [edgeOk]), ("ownedOk", ByteArray.mk #[owned])]

/-- The derived values of a decoded message. -/
def peerDerived (m : PeerMessage) : List (String × ByteArray) :=
  ("maxSize", u64Hex m.maxSize) ::
    match m with
    | .tier1Handshake h | .tier2Handshake h | .tier3Handshake h => handshakeDerived h
    | .syncRoutingTable u => [("edgesOk", flags (u.edges.toList.map Edge.verify))]
    | .lastEdge e => [("edgesOk", flags [e.verify])]
    | .syncAccountsData s =>
      [("accountsOk",
          flags
            (s.accountsData.toList.map fun a =>
              Chain.verifySignature a.payload.signature a.payload.payload a.data.accountKey))]
    | .routed r => [("routedHash", r.hash.bytes), ("routedVerify", flags [r.verify])]
    | _ => []

/-- The derived values of `line` against what was computed, as `check` does. -/
def compareDerived (line : Line) (derived : List (String × ByteArray)) : Option String :=
  (derived.findSome? fun (k, h) =>
        match line.hashes.lookup k with
        | some (some x) => if x == toHex h then none else some s!"{k} differs: {toHex h} vs {x}"
        | _ => some s!"fixture has no {k}").orElse
    fun _ =>
    line.hashes.findSome? fun (k, x) =>
      if x.isSome && !derived.any (·.1 == k) then
        some s!"fixture has {k}, which the test does not compute"
      else none

/-- One line of `PeerMessage.jsonl`. -/
def checkPeerMessage : Check := fun line =>
  match PeerMessage.decode line.borsh with
  | .error _ => if line.reject then none else some "rejected a message that nearcore accepts"
  | .ok m =>
    if line.reject then some "accepted a message that nearcore rejects"
    else
      if m.encode != line.canonical.getD line.borsh then some s!"encodes to {toHex m.encode}"
      else compareDerived line (peerDerived m)

/-- `TieredMessageBody`: decoding goes through `RoutedBody`. -/
def checkTiered : Check := fun line =>
  match RoutedBody.ofTiered line.borsh with
  | .error _ => if line.reject then none else some "rejected a body that nearcore accepts"
  | .ok b =>
    if line.reject then some "accepted a body that nearcore rejects"
    else
      if b.tiered != line.canonical.getD line.borsh then some "tiered form differs"
      else compareDerived line [("routed", Codec.encode b)]

/-- Every Borsh type of the network with its check. -/
def registry : List (String × Check) :=
  [("SocketAddr", check SocketAddr), ("PeerInfo", check PeerInfo),
    ("PartialEdgeInfo", check PartialEdgeInfo),
    ("Edge",
      check Edge fun e =>
        [("hash", e.hash.bytes), ("verify", flags [e.verify]), ("next", u64Hex e.next.toNat)]),
    ("RoutedBody", check RoutedBody fun b => [("tiered", b.tiered), ("isT1", flags [b.isT1])]),
    ("TieredBody", checkTiered),
    ("RoutedMessageV1",
      check RoutedMessageV1 fun m =>
        let r : RoutedMessage := ⟨m.target, m.author, m.ttl, m.body, some m.signature, none, 0⟩
        [("hash", r.hash.bytes), ("verify", flags [r.verify])]),
    ("PartialEncodedChunkRequestMsg", check PartialEncodedChunkRequestMsg),
    ("PartialEncodedChunkResponseMsg", check PartialEncodedChunkResponseMsg),
    ("PartialEncodedChunkForwardMsg",
      check PartialEncodedChunkForwardMsg fun m =>
        [("validHash", flags [(combineHash m.innerHeaderHash m.merkleRoot) == m.chunkHash])]),
    ("StateHeaderRequest", check StateHeaderRequest), ("StatePartRequest", check StatePartRequest),
    ("SpicePartialDataRequest", check SpicePartialDataRequest),
    ("StateResponseInfo", check StateResponseInfo), ("PeerMessage", checkPeerMessage)]

private def manifestCounts (j : Json) : Except String (List (String × Nat × Nat)) := do
  let types ← (← j.getObjVal? "types").getObj?
  types.toList.mapM fun (k, v) => do
      pure (k, ← v.getObjValAs? Nat "accept", ← v.getObjValAs? Nat "reject")

private def preview (b : ByteArray) : String :=
  let h := toHex b
  if h.length > 96 then (h.take 96).toString ++ s!"... ({b.size} bytes)" else h

def main (args : List String) : IO UInt32 := do
  let dir : System.FilePath := args.head?.getD "near-lean/node/fixtures/network"
  let manifest ←
    match Json.parse (← IO.FS.readFile (dir / "manifest.json")) with
    | .ok j =>
      pure j
    | .error e =>
      throw (IO.userError s!"manifest.json: {e}")
  let mut failures := 0
  let pv := (manifest.getObjValAs? Nat "protocol_version").toOption
  let rel := (manifest.getObjValAs? String "nearcore_release").toOption
  if pv != some protocolVersion || rel != some nearcoreRelease then
    IO.eprintln
        s!"fixtures are for protocol {pv} / nearcore {rel}, the node implements \
      {protocolVersion} / {nearcoreRelease}"
    failures := failures + 1
  let counts ←
    match manifestCounts manifest with
    | .ok c =>
      pure c
    | .error e =>
      throw (IO.userError s!"manifest.json: {e}")
  for (k, _, _) in counts do
    if (registry.lookup k).isNone then
      IO.eprintln s!"{k}: fixtures exist but the Lean registry has no entry"
      failures := failures + 1
  IO.println s!"fixtures: nearcore {nearcoreRelease}, protocol {protocolVersion}, {dir}"
  let mut totalAccept := 0
  let mut totalReject := 0
  for (name, run) in registry do
    let some (_, wantAccept, wantReject) := counts.find? (·.1 == name)
      |
      IO.eprintln s!"{name}: no fixtures in the manifest";
      failures := failures + 1;
      continue
    let key := if name == "PeerMessage" then "proto" else "borsh"
    let text ← IO.FS.readFile (dir / s!"{name}.jsonl")
    let mut accept := 0
    let mut reject := 0
    let mut bad : Array String := #[]
    let mut badCount := 0
    for raw in text.splitOn "\n" do
      if raw.isEmpty then
        continue
      match parseLine raw key with
      | .error e =>
        badCount := badCount + 1
        bad := bad.push s!"  unparsable line: {e}"
      | .ok line =>
        if line.reject then
          reject := reject + 1
        else
          accept := accept + 1
        if let some msg := run line then
          badCount := badCount + 1
          if bad.size < 5 then
            bad := bad.push s!"  {line.name}: {msg}\n    input {preview line.borsh}"
    if accept != wantAccept || reject != wantReject then
      bad :=
        bad.push
          s!"  manifest says {wantAccept} accept / {wantReject} reject, file has \
        {accept} / {reject}"
      badCount := badCount + 1
    totalAccept := totalAccept + accept
    totalReject := totalReject + reject
    IO.println
        s!"{name}: accept {accept}, reject {reject}: {if badCount == 0 then "ok" else s!"FAILED ({badCount})"}"
    for b in bad do
      IO.println b
    failures := failures + badCount
  IO.println
      s!"{registry.length} types, {totalAccept} accepted and {totalReject} rejected inputs, \
    {failures} failures"
  return if failures == 0 then 0 else 1
