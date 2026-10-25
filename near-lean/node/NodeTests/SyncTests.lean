import Lean.Data.Json
import NearNode.Net.Mem
import NearNode.Network.Run
import NearNode.Chain.Bootstrap
import NodeConformance.Runner

/-!
`node-sync-tests DIR`: header sync and the sync block, on the in-memory network, over a localnet chain of
the corpus (`tools/localnet/sync_tests.py` unpacks it as `node-chain-apply` has it).

A server node holds the whole chain (`Epoch.processBlock` over every block of `blocks.jsonl`) and answers
`BlockHeadersRequest` and `BlockRequest` as the connection loop of the node does. A client node starts from
the genesis, connects, and syncs through its `Driver`, which is the code that runs against `neard`:

* **headers**: every header is accepted (`Epoch.processHeader`: the checks of `sync_block_headers`, the epochs
  finalized from the headers alone), the chain state of the client equals the server's in every `BlockInfo`
  and epoch, byte for byte, and all of it without a block body;
* **bodies**: every block's body is then attached (`attachBody`);
* **a header that was changed** (a flipped signature) stops the client with an `InvalidSignature` at that
  height, and a missing header leaves the client at the height before it without an error (the next
  request would fetch it); **a body that was changed** is refused;
* **the sync block** (`syncHash`) is found in every epoch with two new chunks in each shard before it, once
  it is final, is the same from every later tip of the epoch, is the child of the first block with two new
  chunks of every shard, and `extraSyncBlocks` lists the blocks down to the lowest chunk of its parent.
-/

open Near.Node Near.Node.Net Near.Node.Network Near.Node.Chain Near.Node.Borsh Near.Node.Bootstrap
  Near.Node.Conformance

private initialize checks : IO.Ref Nat ←
  IO.mkRef 0

private def check (failures : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  checks.modify (· + 1)
  if !ok then
    IO.eprintln s!"FAIL {name}"
    failures.modify (· + 1)

private def keyOf (n : Nat) : NodeKey :=
  (NodeKey.ofSeed? (ByteArray.mk ((Array.range 32).map fun i => (i * 11 + n).toUInt8))).get!

/-- What a run of the client needs from its server: the chain, as the blocks in order. -/
private structure Served where
  blocks : Array Block
  /-- Changes what the server says; the identity serves the chain. -/
  headers : Array BlockHeader → Array BlockHeader := id
  block : Block → Block := id

private def addr : Addr :=
  ⟨ByteArray.mk #[10, 0, 0, 1], 24567⟩

/-- Runs a server that serves `served` and a client from the genesis of `boot` until the client has the
headers and bodies of `target` or `limit` seconds pass. Returns the client's driver and its failure. -/
private def syncRun (boot : Boot) (st : Near.Node.Chain.ChainState) (served : Served)
    (target : UInt64) (limit : Nat) (mode : SyncMode := .blocks) : IO (Driver × Option String) := do
  let hub ← Mem.Hub.new
  let clock : Clock := pure 1700000000
  let genesisId : GenesisId := ⟨boot.genesis.chainId, boot.genesisHash⟩
  let serverCfg : Near.Node.Network.Config :=
    { key := keyOf 1, genesisId, listenPort := some 24567 }
  let clientCfg : Near.Node.Network.Config :=
    { key := keyOf 2, genesisId, listenPort := some 24568 }
  -- the server
  let sharedS ← Shared.new 0
  let serverDriver ←
    Driver.new
        { key := keyOf 1, peer := (keyOf 2).peerId, setup := boot.genesis.setup, apply := false }
        sharedS st (← IO.mkRef #[]) (pure 1)
  serverDriver.state.modify fun s =>
      { s with cache := served.blocks.foldl (fun m b => m.insert b.header.hash.bytes b) {} }
  let stopS ← IO.mkRef false
  let envS : Env :=
    { cfg := serverCfg, clock, outbox := ← IO.mkRef #[], graph := ← IO.mkRef {}, stop := stopS,
      counts := ← IO.mkRef {}, edgesOk := ← IO.mkRef 0, edgesBad := ← IO.mkRef 0,
      log := fun _ => pure () }
  let hooksS : Hooks :=
    { tick := pure (), onHeaders := fun _ => pure (), onBlock := fun _ => pure (),
      onRouted := fun _ => pure (), onStateResponse := fun _ => pure (), latestBlock := pure none,
      headersAfter := fun hs => do
        pure (served.headers (← serverDriver.headersAfter hs)),
      blockOf := fun h => do
        pure ((← serverDriver.blockOf h).map served.block),
      status := pure "" }
  let listener ← hub.net.listen addr
  let serverTask ←
    IO.asTask (prio := .dedicated) do
        let some s ← listener.accept 5000 | return ()
        match ← handshakeInbound serverCfg clock s (fun _ => none) st.headHeight with
        | .ok link =>
          discard <| runLink envS hooksS link
        | .error _ =>
          pure ()
  -- the client
  let sharedC ← Shared.new 0
  let clientOutbox ← IO.mkRef #[]
  let client ←
    Driver.new
        { key := keyOf 2, peer := (keyOf 1).peerId, setup := boot.genesis.setup, apply := false,
          mode, blockRate := 100000 }
        sharedC boot.state clientOutbox (pure 1)
  let stopC := sharedC.stop
  let started ← IO.monoMsNow
  let envC : Env :=
    { cfg := clientCfg, clock, outbox := clientOutbox, graph := ← IO.mkRef {}, stop := stopC,
      counts := ← IO.mkRef {}, edgesOk := ← IO.mkRef 0, edgesBad := ← IO.mkRef 0,
      log := fun _ => pure () }
  let hooksC : Hooks :=
    { tick := do
        client.tick
        let s ← client.state.get
        let done := s.st.headHeight == target && s.bodyTipHeight == target
        if done || (← sharedC.failure.get).isSome || (← IO.monoMsNow) - started > limit * 1000 then
          stopC.set true
      onHeaders := client.onHeaders, onBlock := client.onBlock, onRouted := client.onRouted,
      onStateResponse := client.onStateResponse, latestBlock := pure none,
      headersAfter := client.headersAfter, blockOf := client.blockOf, status := pure "" }
  let stream ← hub.net.connect addr 1000
  match ← handshakeOutbound clientCfg clock stream (keyOf 1).peerId .t2 none 0 with
  | .ok link =>
    client.state.modify fun s => { s with peerHeight := target }
    discard <| runLink envC hooksC link
  | .error e =>
    throw (IO.userError s!"handshake: {e.describe}")
  stopS.set true
  discard <| IO.wait serverTask
  listener.close
  pure (client, ← sharedC.failure.get)

private def epochBytes (e : EpochData) : ByteArray :=
  Codec.encode (e.info, e.layout)

def main (args : List String) : IO UInt32 := do
  let some dir := args.head? | do IO.eprintln "usage: node-sync-tests DIR"; return 2
  let dir : System.FilePath := dir
  let configs : System.FilePath := (args.drop 1).head?.getD "near-lean/vm/configs"
  let failures ← IO.mkRef 0
  let boot ← Boot.load (dir / "meta.json") (dir / "genesis.json") (dir / "blocks.jsonl") configs
  -- the server's chain: every block, validated as M5a does
  let mut st := boot.state
  let mut blocks : Array Block := #[boot.genesisBlock]
  for line in (← lines (dir / "blocks.jsonl")).extract 1 100000 do
    let block ← orThrow (do decode Block "block" (← bytes line "block"))
    match Epoch.processBlock boot.genesis.setup st block with
    | .ok (st', _) =>
      st := st'
      blocks := blocks.push block
    | .error e =>
      throw (IO.userError s!"the chain does not validate: {e.kind} {e.detail}")
  let target := st.headHeight
  IO.println s!"{boot.genesis.chainId}: {blocks.size} blocks up to height {target}"
  -- headers and bodies
  let started ← IO.monoMsNow
  let (client, failure) ← syncRun boot st { blocks } target 120
  let cs ← client.state.get
  IO.println s!"headers and bodies synced in {(← IO.monoMsNow) - started} ms"
  check failures "sync: no failure" failure.isNone
  check failures "sync: all headers accepted" (cs.st.headHeight == target)
  check failures "sync: all bodies attached" (cs.bodyTipHeight == target)
  check failures "sync: same blocks" (cs.st.blocks.size == st.blocks.size)
  check failures "sync: same head" (cs.st.head == st.head)
  let sameInfo :=
    st.blocks.toList.all fun (k, r) =>
      match cs.st.blocks[k]? with
      | some c =>
        Codec.encode (BlockInfo.v4 c.info) == Codec.encode (BlockInfo.v4 r.info) &&
          Codec.encode c.tree == Codec.encode r.tree && c.hasBody == r.hasBody
      | none => false
  check failures "sync: every BlockInfo, merkle tree and body is the server's" sameInfo
  let sameEpochs :=
    st.epochs.toList.all fun (k, e) =>
      match cs.st.epochs[k]? with
      | some c => epochBytes c == epochBytes e
      | none => false
  check failures "sync: every epoch (computed from headers) is the server's"
      (sameEpochs && cs.st.epochs.size == st.epochs.size)
  -- the sync block of every epoch
  let mut found := 0
  let mut stable := true
  let mut sound := true
  let mut extrasOk := true
  let mut perEpoch : Std.HashMap ByteArray CryptoHash := {}
  for (_, tip) in st.blocks.toList do
    if tip.hash == CryptoHash.zero then
      continue
    match syncHash st tip.hash with
    | .error e =>
      sound := false
      IO.eprintln s!"syncHash {tip.view.height}: {e.kind} {e.detail}"
    | .ok none => pure ()
    | .ok (some s) =>
      found := found + 1
      let sRec ← orThrow ((st.block s).mapError (·.kind))
      let pRec ← orThrow ((st.block sRec.view.prevHash).mapError (·.kind))
      -- in the epoch of the tip, final, the child of a block with two new chunks per shard
      let blocksOfEpoch ← orThrow ((epochBlocks st tip.hash).mapError (·.kind))
      let counts := newChunkCounts blocksOfEpoch
      let idx (b : BlockRec) := blocksOfEpoch.findIdx? (·.hash == b.hash)
      let final ← orThrow ((st.block tip.view.lastFinalBlock).mapError (·.kind))
      let ok :=
        sRec.info.epochId == tip.info.epochId && pRec.info.epochId == tip.info.epochId &&
          sRec.view.height ≤ final.info.height &&
          (match idx pRec with
            | some i => (counts[i]!).all (· ≥ 2) && (i == 0 || !(counts[i - 1]!).all (· ≥ 2))
            | none => false)
      if !ok then
        sound := false
        IO.eprintln s!"syncHash at tip {tip.view.height} is {sRec.view.height}: not a sync block"
      -- the same block from every tip of the epoch
      match perEpoch[tip.info.epochId.hash.bytes]? with
      | some other => if other != s then stable := false
      | none => perEpoch := perEpoch.insert tip.info.epochId.hash.bytes s
      -- the blocks to fetch with it
      match extraSyncBlocks st s with
      | .error _ => extrasOk := false
      | .ok extras =>
        let minIncluded := pRec.chunks.foldl (fun m c => min m c.heightIncluded) pRec.view.height
        let heights := extras.filterMap fun h => (st.blocks[h.bytes]?).map (·.view.height)
        let descending := (List.range heights.size).all fun i => i == 0 || heights[i]! + 1 == heights[i - 1]!
        let lowOk := heights.back?.all (· ≥ minIncluded)
        let startsRight := heights[0]?.all (· + 1 == pRec.view.height)
        if !(descending && lowOk && startsRight && extras.size == heights.size) then
          extrasOk := false
  IO.println s!"sync blocks found at {found} tips"
  check failures "sync block: found" (found > 0)
  check failures "sync block: sound at every tip" sound
  check failures "sync block: the same from every tip of the epoch" stable
  check failures "sync block: the extra blocks" extrasOk
  -- a changed header
  let flipAt : UInt64 := target / 2
  let flip (h : BlockHeader) : BlockHeader :=
    match h with
    | .v4 x => .v4 { x with signature := match x.signature with
                      | .ed25519 s => .ed25519 (s.set! 3 (s.get! 3 ^^^ 1))
                      | s => s }
    | .v5 x => .v5 { x with signature := match x.signature with
                      | .ed25519 s => .ed25519 (s.set! 3 (s.get! 3 ^^^ 1))
                      | s => s }
    | .v6 x => .v6 { x with signature := match x.signature with
                      | .ed25519 s => .ed25519 (s.set! 3 (s.get! 3 ^^^ 1))
                      | s => s }
    | h => h
  let (client, failure) ←
    syncRun boot st
      { blocks, headers := fun hs => hs.map fun h => if h.view?.map (·.height) == some flipAt then flip h else h }
      target 20
  let cs ← client.state.get
  check failures "flipped signature: refused" (failure.any (·.startsWith s!"header {flipAt} rejected: InvalidSignature"))
  check failures "flipped signature: the client stops before it" (cs.st.headHeight + 1 == flipAt)
  -- a missing header: the headers after it are orphans, nothing is accepted past the gap
  let (client, failure) ←
    syncRun boot st
      { blocks, headers := fun hs => hs.filter fun h => h.view?.map (·.height) != some flipAt }
      target 4
  let cs ← client.state.get
  check failures "missing header: no failure" failure.isNone
  check failures "missing header: the client waits at the height before" (cs.st.headHeight + 1 == flipAt)
  -- a changed body
  let swap (b : Block) : Block :=
    match b with
    | .v4 ⟨h, .v2 body⟩ =>
      if h.view?.map (·.height) == some flipAt then
        .v4 ⟨h, .v2 { body with vrfValue := ⟨body.vrfValue.bytes.set! 0 (body.vrfValue.bytes.get! 0 ^^^ 1)⟩ }⟩
      else b
    | b => b
  let (client, failure) ← syncRun boot st { blocks, block := swap } target 20
  let cs ← client.state.get
  IO.println s!"changed body: {failure}, bodies up to {cs.bodyTipHeight}"
  check failures "changed body: refused as not the block of the header"
      (failure.any (·.startsWith s!"block {flipAt} rejected: InvalidSignature"))
  check failures "changed body: headers all accepted, bodies stop before it"
      (cs.st.headHeight == target && cs.bodyTipHeight + 1 == flipAt)
  let n ← checks.get
  let f ← failures.get
  IO.println s!"{n} checks, {f} failures"
  return if f == 0 then 0 else 1
