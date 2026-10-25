import NearNode.Net.Uv
import NearNode.Network.Node
import NearNode.Network.Apply

/-!
# Running the node against a boot node

`run` starts the chain from its genesis files (or from the store), opens the connection to the boot
node, and syncs: the connection loop (`Node.runLink`) with the driver (`Driver`) on this thread, the
apply worker (`Apply.applyLoop`) on another, and, when the node listens, a loop that accepts peers
and answers their handshakes and requests. It ends when asked to, when a time limit passes, or when
the node has followed the peer's head for the time requested; a failure of validation or of
application ends it at once. The summary says what happened.
-/

namespace Near.Node.Network

open Lean Near.Node Near.Node.Net Near.Node.Chain Near.Node.Apply Near.Node.Bootstrap

/-- What to run. -/
structure Options where
  chainDir : System.FilePath
  configs : System.FilePath := "near-lean/vm/configs"
  keyFile : System.FilePath
  peers : Array (PeerId × Addr)
  listen : Option UInt16 := none
  store : Option System.FilePath := none
  apply : Bool := true
  /-- Stop after this many seconds. -/
  seconds : Option Nat := none
  /-- Stop this many seconds after the node has reached the peer's head. -/
  follow : Option Nat := none
  /-- After that, wait for the worker to apply what was validated, at most this many seconds. -/
  drain : Nat := 0
  appliedLog : Option System.FilePath := none
  report : Option System.FilePath := none
  quiet : Bool := false

/-- A node key from a `node_key.json`, or a new one written to `file`. -/
def loadOrCreateKey (file : System.FilePath) : IO NodeKey := do
  if ← file.pathExists then
    let j ← IO.ofExcept (Json.parse (← IO.FS.readFile file) |>.mapError IO.userError)
    match NodeKey.ofJson? j with
    | some k =>
      pure k
    | none =>
      throw (IO.userError s!"{file}: not a node key")
  else
    let seed ← IO.getRandomBytes 32
    let some k := NodeKey.ofSeed? seed | throw (IO.userError "key generation failed")
    let secret := "ed25519:" ++ base58Encode (seed ++ k.signing.publicKey)
    IO.FS.writeFile file
        s!"\{\"account_id\":\"node\",\"public_key\":\"{k.peerId.key.toText}\",\"secret_key\":\"{secret}\"}\n"
    pure k

private def jsonNat (n : Nat) : Json :=
  Json.num n

/-- Everything the report says. -/
structure Summary where
  handshakes : Nat := 0
  disconnects : Array String := #[]
  peerHeight : UInt64 := 0
  tipHeight : UInt64 := 0
  startHeight : UInt64 := 0
  validated : Nat := 0
  applied : UInt64 := 0
  reachedHeadAt : Option Nat := none
  seconds : Nat := 0

private def ratio (a b : Nat) : String :=
  s!"{a}/{b}"

/-- The node runs until it is done; the exit code is 0 when everything agreed. -/
def run (o : Options) : IO UInt32 := do
  let boot ←
    Boot.load (o.chainDir / "meta.json") (o.chainDir / "genesis.json") (o.chainDir / "blocks.jsonl")
        o.configs
  let key ← loadOrCreateKey o.keyFile
  let clock := systemClock
  let started ← IO.monoMsNow
  let log (s : String) : IO Unit := do
    unless o.quiet do
      IO.eprintln s!"[{((← IO.monoMsNow) - started) / 1000}s] {s}"
  log
      s!"chain {boot.genesis.chainId}, genesis {base58Encode boot.genesisHash.bytes}, node {key.peerId.key.toText}"
  -- the store, and the chain it holds
  let mut st := boot.state
  let mut progress := boot.progress
  let mut store? : Option Store.Store := none
  let mut resumed := false
  if o.apply then
    if let some dir := o.store then
      let (s, _) ← Store.Store.open dir
      match ← orThrow (Near.Node.Apply.load boot.config (← s.view)) with
      | some (st0, pr0) =>
        st := st0
        progress := pr0
        resumed := true
        log s!"continuing from the store at height {st0.headHeight}"
      | none =>
        discard <| s.commit boot.ops
      store? := some s
  let shared ← Shared.new st.headHeight
  let outbox ← IO.mkRef #[]
  let driver ←
    Driver.new { key, peer := (o.peers[0]!).1, setup := boot.genesis.setup, apply := o.apply }
        shared st outbox clock
  let appliedLog ←
    match o.appliedLog with
    | some f =>
      pure (some (← IO.FS.Handle.mk f .write))
    | none =>
      pure none
  let stats ← IO.mkRef ({} : ApplyStats)
  let progressRef ← IO.mkRef progress
  let workerEnv : WorkerEnv :=
    { params := boot.params, shared, store := store?, progress := progressRef, stats, appliedLog,
      log }
  let worker ←
    if o.apply then
      some <$> IO.asTask (applyLoop workerEnv) Task.Priority.dedicated
    else
      pure none
  let summary ← IO.mkRef ({ startHeight := st.headHeight, tipHeight := st.headHeight } : Summary)
  let cfg : Config :=
    { key, genesisId := ⟨boot.genesis.chainId, boot.genesisHash⟩, listenPort := o.listen }
  let env : Env :=
    { cfg, clock, outbox, graph := ← IO.mkRef {}, stop := shared.stop, counts := ← IO.mkRef {},
      edgesOk := ← IO.mkRef 0, edgesBad := ← IO.mkRef 0, log }
  -- when to stop
  let monitor : IO Unit := do
    let now ← IO.monoMsNow
    let elapsed := (now - started) / 1000
    let s ← driver.state.get
    let applied ← shared.applied.get
    summary.modify fun x =>
        { x with
          peerHeight := s.peerHeight, tipHeight := s.tipHeight, validated := s.validated, applied }
    if (← shared.failure.get).isSome then
      shared.stop.set true
    if let some limit := o.seconds then
      if elapsed ≥ limit then
        shared.stop.set true
    if let some follow := o.follow then
      let x ← summary.get
      -- caught up: the tip is the peer's head and nothing is waiting
      if
          x.reachedHeadAt.isNone && s.peerHeight > 0 && s.tipHeight + 2 ≥ s.peerHeight &&
            s.pending.isEmpty then
        summary.modify fun x => { x with reachedHeadAt := some elapsed }
        log s!"reached the peer's head at height {s.tipHeight}"
      if let some t := x.reachedHeadAt then
        let drainOver := !o.apply || applied + 3 ≥ s.tipHeight || elapsed ≥ t + follow + o.drain
        if elapsed ≥ t + follow && drainOver then
          shared.stop.set true
  let hooks : Hooks :=
    { tick := do
        driver.tick;
        monitor
      onHeaders := driver.onHeaders, onBlock := driver.onBlock, onRouted := driver.onRouted
      latestBlock := do
        driver.blockOf (← driver.state.get).tipHash
      headersAfter := driver.headersAfter, blockOf := driver.blockOf
      status := do
        let s ← driver.state.get
        let a ← shared.applied.get
        let q := (← shared.queue.get).size
        let wk ← stats.get
        pure
            s!"tip {s.tipHeight} (peer {s.peerHeight}) validated {s.validated} staged {s.staged.size} jobs {s.jobs.size} queued {q} applied {a} ({wk.chunks} chunks)" }
  -- the listener
  let listener ←
    match o.listen with
    | some port =>
      let l ← Uv.net.listen ⟨ByteArray.mk #[0, 0, 0, 0], port⟩
      log s!"listening on {l.addr}"
      let t ←
        IO.asTask (prio := Task.Priority.dedicated) do
            while !(← shared.stop.get) do
              if let some s← l.accept 250 then
                discard <|
                    IO.asTask (prio := Task.Priority.dedicated) do
                      let ob ← IO.mkRef #[]
                      let env' := { env with outbox := ob }
                      match ← handshakeInbound cfg clock s (fun _ => none) st.headHeight with
                      | .error e =>
                        log s!"inbound handshake failed: {e.describe}"
                        s.close
                      | .ok link =>
                        log s!"inbound connection from {link.addr}"
                        let serve : Hooks :=
                          { hooks with
                            tick := pure (), onHeaders := fun _ => pure (),
                            onBlock := fun _ => pure (), onRouted := fun _ => pure (),
                            status := pure "" }
                        let ended ← runLink env' serve link
                        log s!"inbound connection closed: {ended.reason}"
      pure (some t)
    | none =>
      pure none
  -- the outbound connection, again after it fails
  let mut attempts := 0
  while !(← shared.stop.get) do
    let (peerId, addr) := o.peers[attempts % o.peers.size]!
    attempts := attempts + 1
    try
      let stream ← Uv.net.connect addr 5000
      match ← handshakeOutbound cfg clock stream peerId .t2 none st.headHeight with
      | .error e =>
        log s!"handshake with {addr} failed: {e.describe}"
        stream.close
        summary.modify fun x =>
            { x with disconnects := x.disconnects.push s!"handshake: {e.describe}" }
        IO.sleep 1000
      | .ok link =>
        log
            s!"handshake with {addr} done: its height {link.theirs.senderChainInfo.height}, version {link.protocolVersion}, edge nonce {link.edge.nonce}"
        summary.modify fun x => { x with handshakes := x.handshakes + 1 }
        driver.state.modify fun s =>
            { s with
              peerHeight :=
                if link.theirs.senderChainInfo.height > s.peerHeight then
                  link.theirs.senderChainInfo.height
                else s.peerHeight }
        env.graph.modify (·.add link.edge)
        let ended ← runLink env hooks link
        log s!"connection closed: {ended.reason}"
        if ended.reason != "stopped" then
          summary.modify fun x => { x with disconnects := x.disconnects.push ended.reason }
    catch e =>
      log s!"connection to {addr} failed: {e}"
      summary.modify fun x => { x with disconnects := x.disconnects.push s!"{e}" }
      IO.sleep 1000
  shared.stop.set true
  if let some t := worker then
    discard <| IO.wait t
  if let some t := listener then
    discard <| IO.wait t
  if let some s := store? then
    s.close
  -- the report
  let x ← summary.get
  let wk ← stats.get
  let s ← driver.state.get
  let counts ← env.counts.get
  let failure ← shared.failure.get
  let elapsed := ((← IO.monoMsNow) - started) / 1000
  let applied ← shared.applied.get
  let json : Json :=
    Json.mkObj
      [("chainId", boot.genesis.chainId), ("genesisHash", base58Encode boot.genesisHash.bytes),
        ("nodePeerId", key.peerId.key.toText), ("handshakes", jsonNat x.handshakes),
        ("disconnects", Json.arr (x.disconnects.map Json.str)),
        ("peerHeight", jsonNat s.peerHeight.toNat), ("startHeight", jsonNat x.startHeight.toNat),
        ("tipHeight", jsonNat s.tipHeight.toNat), ("blocksValidated", jsonNat s.validated),
        ("appliedHeight", jsonNat applied.toNat), ("blocksApplied", jsonNat wk.blocks),
        ("chunksApplied", jsonNat wk.chunks), ("extrasChecked", jsonNat wk.extrasChecked),
        ("extrasAgree", jsonNat wk.extrasAgree), ("receiptsChecked", jsonNat wk.receiptsChecked),
        ("receiptsAgree", jsonNat wk.receiptsAgree),
        ("mismatches", Json.arr (wk.mismatches.map Json.str)), ("applyMillis", jsonNat wk.millis),
        ("reachedHeadAtSeconds",
          match x.reachedHeadAt with
          | some t => jsonNat t
          | none => Json.null),
        ("seconds", jsonNat elapsed), ("resumed", Json.bool resumed),
        ("edgesVerified", jsonNat (← env.edgesOk.get)),
        ("edgesInvalid", jsonNat (← env.edgesBad.get)),
        ("received", Json.mkObj (counts.toList.map fun (k, v) => (k, jsonNat v))),
        ("chunkResponses", jsonNat s.chunkResponses),
        ("chunkPartsRefused", jsonNat s.chunkPartsRefused),
        ("failure",
          match failure with
          | some f => Json.str f
          | none => Json.null)]
  if let some f := o.report then
    IO.FS.writeFile f (json.pretty ++ "\n")
  IO.println json.compress
  let ok :=
    failure.isNone && wk.mismatches.isEmpty && x.handshakes > 0 &&
      (o.follow.isNone || x.reachedHeadAt.isSome)
  return if ok then 0 else 1

end Near.Node.Network
