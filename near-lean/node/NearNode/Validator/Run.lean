import Lean.Data.Json
import NearNode.Net.Uv
import NearNode.Chain.Bootstrap
import NearNode.Network.Run
import NearNode.Validator.Drive
import NearNode.Rpc.Server
import NearNode.Validator.Persist
import NearNode.Store

/-!
# Running as a validator

`near-lean-node validator`: starts the chain from its genesis, connects to a peer and follows,
produces and validates as a validator (`NearNode.Validator.Drive`). The validator key gives the
account and the signing key; the node key is the peer id.
-/

namespace Near.Node.Validator

open Lean Near.Node Near.Node.Net Near.Node.Network Near.Node.Chain Near.Node.Bootstrap
  Near.Node.Apply

structure Options where
  chainDir : System.FilePath
  configs : System.FilePath := "near-lean/vm/configs"
  nodeKey : System.FilePath
  validatorKey : System.FilePath
  peer : PeerId × Addr
  listen : Option UInt16 := none
  seconds : Option Nat := none
  report : Option System.FilePath := none
  appliedLog : Option System.FilePath := none
  /-- The node ends, and writes its report, when this file exists. -/
  stopFile : Option System.FilePath := none
  quiet : Bool := false
  /-- `text` (`[12.3s] message`) or `json` (one object per line: `ts`, `level`, `target`, `msg`). -/
  logFormat : String := "text"
  /-- Where the JSON-RPC server listens (`rpc.addr` of `config.json`); none: no server. -/
  rpcAddr : Option Addr := none
  /-- neard's `genesis.json`, from which the RPC answers `EXPERIMENTAL_genesis_config`. -/
  genesisConfig : Option System.FilePath := none
  /-- The directory of the chain store (`data/` of a neard home); none: nothing is kept across a restart. -/
  store : Option System.FilePath := none
  /-- `min_block_production_delay`, `max_block_production_delay`, `max_block_wait_delay`, in ms. -/
  endorsementDelay : Nat := 600
  baseDelay : Nat := 2000
  capDelay : Nat := 6000

/-- Serves headers after the first locator hash we know, along the chain of the head. -/
def Env.headersAfter (e : Env) (hashes : Array CryptoHash) : IO (Array BlockHeader) := do
  let s ← e.get
  let some start := hashes.find? fun h => s.st.blockExists h | return #[]
  let mut out : List BlockHeader := []
  let mut cur := s.st.head
  for _ in [0:100000] do
    if cur == start then
      break
    match s.st.block cur with
    | .ok r =>
      out := r.header :: out
      cur := r.view.prevHash
    | .error _ =>
      break
  return (out.toArray.extract 0 512)

def run (o : Options) : IO UInt32 := do
  let boot ←
    Boot.load (o.chainDir / "meta.json") (o.chainDir / "genesis.json") (o.chainDir / "blocks.jsonl")
        o.configs
  let nodeKey ← loadOrCreateKey o.nodeKey
  let signer ←
    match
      Signer.ofJson?
        (← IO.ofExcept (Json.parse (← IO.FS.readFile o.validatorKey) |>.mapError IO.userError)) with
    | some s =>
      pure s
    | none =>
      throw (IO.userError s!"{o.validatorKey}: not a validator key")
  let started ← IO.monoMsNow
  let log (msg : String) : IO Unit := do
    unless o.quiet do
      if o.logFormat == "json" then
        let ms := (← IO.monoMsNow) - started
        IO.eprintln
            (Json.mkObj
                [("ts", Json.num (JsonNumber.fromNat (← wallSeconds))),
                  ("uptime_ms", Json.num (JsonNumber.fromNat ms)), ("level", "INFO"),
                  ("target", "near-lean-node"), ("msg", Json.str msg)]).compress
      else
        IO.eprintln
            s!"[{((← IO.monoMsNow) - started) / 1000}.{(((← IO.monoMsNow) - started) % 1000) / 100}s] {msg}"
  log s!"validator {signer.accountId.val}, node {nodeKey.peerId.key.toText}"
  let total := numTotalParts boot.genesis.setup.config.numBlockProducerSeats
  let code ← IO.ofExcept (chunkCode total |>.mapError IO.userError)
  let delays : Delays :=
    { endorsement := o.endorsementDelay, base := o.baseDelay, cap := o.capDelay }
  let genesisHeight := boot.state.headHeight
  let now0 ← IO.monoMsNow
  let mut store? : Option Store.Store := none
  let mut resumed? : Option Resumed := none
  if let some dir := o.store then
    let (store, recovery) ← Store.Store.open dir
    store? := some store
    match ← orThrow (resume boot.config (← store.view) delays now0) with
    | some r =>
      resumed? := some r
      log
          s!"continuing from the store at height {r.state.tipHeight} (generation {recovery.generation}, {recovery.commits} commits replayed); largest approval target {r.safety.largestTarget}"
    | none =>
      discard <| store.commit boot.ops
  let ds := (Doomslug.new now0 0 delays).setTip boot.genesisHash genesisHeight genesisHeight now0
  let vstate : VState :=
    match resumed? with
    | some r => r.state
    | none =>
      { st := boot.state, pr := boot.progress,
        blocks :=
          ({} : Std.HashMap ByteArray Block).insert boot.genesisHash.bytes boot.genesisBlock,
        applied :=
          ({} : Std.HashMap ByteArray BlockHeight).insert boot.genesisHash.bytes genesisHeight,
        tip := boot.genesisHash, tipHeight := genesisHeight, ds, latestKnown := genesisHeight }
  let env : Env :=
    { signer, nodeKey, peer := o.peer.1, setup := boot.genesis.setup, params := boot.params, code,
      delays,
      validityPeriod :=
        (boot.metaJson.getObjValAs? Nat "transactionValidityPeriod").toOption.getD 86400,
      state := ← IO.mkRef vstate, txQueue := ← IO.mkRef #[], store := store?,
      outbox := ← IO.mkRef #[], failure := ← IO.mkRef none, log,
      appliedLog :=
        ←
          (match o.appliedLog with
            | some f => some <$> IO.FS.Handle.mk f .write
            | none => pure none),
      nowMs := IO.monoMsNow, applying := ← IO.mkRef none, lastTurn := ← IO.mkRef 0 }
  let stop ← IO.mkRef false
  let connected ← IO.mkRef false
  let rpcStop ← IO.mkRef false
  -- SIGTERM and SIGINT end the node as the stop file does: the loop leaves, the store is closed, the report written
  for signum in [15, 2] do
    Uv.onSignal signum do
        log "signal received, shutting down"
        stop.set true
  if let some addr := o.rpcAddr then
    let genesisConfig : Json ←
      match o.genesisConfig with
      | some f =>
        let j ← IO.ofExcept (Json.parse (← IO.FS.readFile f) |>.mapError IO.userError)
        match j with
        | .obj kvs =>
          let kvs := kvs.erase "records"
          -- `genesis_time` is written without a fraction when it has none
          let kvs :=
            match kvs.get? "genesis_time" with
            | some (.str t) => kvs.insert "genesis_time" (.str ((t.replace ".000000000Z" "Z")))
            | _ => kvs
          pure (Json.obj kvs)
        | other =>
          pure other
      | none =>
        pure (Json.mkObj [])
    let runtimeFile :=
      o.configs / s!"runtime_config_v{boot.genesis.setup.reward.genesisProtocolVersion}.json"
    let runtimeConfig : Json ←
      if ← runtimeFile.pathExists then
        let j ← IO.ofExcept (Json.parse (← IO.FS.readFile runtimeFile) |>.mapError IO.userError)
        let keep :=
          ["account_creation_charge", "account_creation_config", "congestion_control_config",
            "min_gas_purchase_price", "storage_amount_per_byte", "transaction_costs", "wasm_config",
            "witness_config"]
        pure (Json.mkObj (keep.filterMap fun k => (j.getObjVal? k).toOption.map (k, ·)))
      else
        pure (Json.mkObj [])
    let ctx : Rpc.Ctx :=
      { env, rpcAddr := toString addr, startedMs := started, genesisConfig, runtimeConfig,
        nodeKey := nodeKey.peerId.key }
    let srv : Rpc.Server :=
      { ctx, connected, peerAddr := toString o.peer.2, peerId := o.peer.1.key }
    discard <| IO.asTask (Rpc.run srv addr rpcStop) Task.Priority.dedicated
    log s!"JSON-RPC on {addr}"
  let cfg : Near.Node.Network.Config :=
    { key := nodeKey, genesisId := ⟨boot.genesis.chainId, boot.genesisHash⟩, listenPort := o.listen,
      trackedShards := boot.genesisEpoch.layout.shardIds }
  let netEnv : Near.Node.Network.Env :=
    { cfg, clock := systemClock, outbox := env.outbox, graph := ← IO.mkRef {}, stop,
      counts := ← IO.mkRef {}, edgesOk := ← IO.mkRef 0, edgesBad := ← IO.mkRef 0, log }
  let lastAnnounce ← IO.mkRef 0
  let disconnects ← IO.mkRef (#[] : Array String)
  let handshakes ← IO.mkRef 0
  let tick : IO Unit := do
    env.tick
    let now ← IO.monoMsNow
    if now - (← lastAnnounce.get) ≥ 30000 || (← lastAnnounce.get) == 0 then
      lastAnnounce.set now
      env.outbox.modify (·.push (announce signer nodeKey (← wallSeconds).toUInt64 (← wallSeconds)))
    if let some limit := o.seconds then
      if (now - started) / 1000 ≥ limit then
        stop.set true
    if let some f := o.stopFile then
      if ← f.pathExists then
        stop.set true
    if (← env.failure.get).isSome then
      stop.set true
  let hooks : Hooks :=
    { tick, onHeaders := fun _ => pure (), onBlock := env.ingestBlock, onRouted := env.onRouted
      onStateResponse := fun _ => pure ()
      latestBlock := do
        let s ← env.get
        pure (s.blocks[s.tip.bytes]?)
      headersAfter := env.headersAfter
      blockOf := fun h => do
        pure ((← env.get).blocks[h.bytes]?)
      status := do
        let s ← env.get
        let n (k : String) := s.stats.getD k 0
        pure
            s!"tip {s.tipHeight} (head {s.st.headHeight}) applied {n "blocksApplied"} pending {s.pending.size} produced {n "blocksProduced"} blocks, {n "chunksProduced"} chunks; approvals sent {n "approvalsSent"} collected {n "approvalsCollected"}; endorsements sent {n "endorsementsSent"}; witnesses sent {n "witnessesSent"} valid {n "witnessesValid"} invalid {n "witnessesInvalid"}" }
  let (peerId, addr) := o.peer
  while !(← stop.get) do
    try
      let stream ← Uv.net.connect addr 5000
      match ← handshakeOutbound cfg systemClock stream peerId .t2 none (← env.get).tipHeight with
      | .error e =>
        log s!"handshake with {addr} failed: {e.describe}"
        stream.close
        disconnects.modify (·.push s!"handshake: {e.describe}")
        IO.sleep 1000
      | .ok link =>
        log s!"handshake with {addr} done: its height {link.theirs.senderChainInfo.height}"
        handshakes.modify (· + 1)
        connected.set true
        netEnv.graph.modify (·.add link.edge)
        -- announce the validator, now and again
        lastAnnounce.set 0
        let ended ← runLink netEnv hooks link
        connected.set false
        log s!"connection closed: {ended.reason}"
        if ended.reason != "stopped" then
          disconnects.modify (·.push ended.reason)
    catch err =>
      log s!"connection to {addr} failed: {err}"
      disconnects.modify (·.push s!"{err}")
      IO.sleep 1000
  log "stopping: closing the RPC server and the store"
  rpcStop.set true
  if let some store := store? then
    store.close
  -- the report
  let s ← env.get
  let failure ← env.failure.get
  let json : Json :=
    Json.mkObj
      [("account", signer.accountId.val), ("chainId", boot.genesis.chainId),
        ("genesisHash", base58Encode boot.genesisHash.bytes),
        ("handshakes", Json.num (JsonNumber.fromNat (← handshakes.get))),
        ("disconnects", Json.arr ((← disconnects.get).map Json.str)),
        ("tipHeight", Json.num (JsonNumber.fromNat s.tipHeight.toNat)),
        ("headHeight", Json.num (JsonNumber.fromNat s.st.headHeight.toNat)),
        ("tipHash", base58Encode s.tip.bytes),
        ("stats",
          Json.mkObj (s.stats.toList.map fun (k, v) => (k, Json.num (JsonNumber.fromNat v)))),
        ("seconds", Json.num (JsonNumber.fromNat (((← IO.monoMsNow) - started) / 1000))),
        ("failure",
          match failure with
          | some f => Json.str f
          | none => Json.null)]
  if let some f := o.report then
    IO.FS.writeFile f (json.pretty ++ "\n")
  IO.println json.compress
  return if failure.isNone && (← handshakes.get) > 0 then 0 else 1

end Near.Node.Validator
