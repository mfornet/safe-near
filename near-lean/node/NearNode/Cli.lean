import NearNode
import NearNode.Net.Uv
import NearNode.Network.Run
import NearNode.Validator.Run

/-!
`near-lean-node`: the node executable.

* `--version`: the nearcore release and protocol version the node implements.
* `peer --chain-dir DIR --node-key FILE --boot PEERID@IP:PORT [...]`: runs the node as a peer of a
  boot node, syncing and applying the chain (see `NearNode.Network.Run`).
-/

open Near.Node Near.Node.Net Near.Node.Network

def usage : String :=
  "usage: near-lean-node --version\n" ++
    "       near-lean-node peer --chain-dir DIR --node-key FILE --boot PEERID@IP:PORT\n" ++
    "           [--listen PORT] [--store DIR] [--no-apply] [--seconds N] [--follow N] [--drain N]\n" ++
    "           [--applied-log FILE] [--report FILE] [--configs DIR] [--quiet]\n" ++
    "           [--sync-mode blocks|state|auto] [--track-shards ID,ID,...] [--public-addr IP:PORT]\n" ++
    "           [--lag-log FILE] [--reach-lag N] [--profile] [--save-state DIR]\n" ++
    "       near-lean-node validator --chain-dir DIR --node-key FILE --validator-key FILE --boot PEERID@IP:PORT\n" ++
    "           [--listen PORT] [--seconds N] [--report FILE] [--applied-log FILE] [--stop-file FILE] [--configs DIR] [--quiet]\n" ++
    "           [--rpc-addr IP:PORT] [--genesis-config FILE] [--store DIR]\n" ++
    "           [--home NEARD_HOME] [--log-format text|json]\n" ++
    "           [--delays ENDORSEMENT,BASE,CAP]"

/-- The value after a flag. -/
private def flagValue (args : List String) (flag : String) : Option String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: _ => some v
  | _ => none

/-- Every value after a repeated flag. -/
private partial def flagValues (args : List String) (flag : String) : List String :=
  match args.dropWhile (· != flag) with
  | _ :: v :: rest => v :: flagValues rest flag
  | _ => []

private def parsePeer (s : String) : Option (PeerId × Addr) := do
  let [key, addr] := s.splitOn "@" | none
  let pk ← PublicKey.parse? key
  let a ← Addr.parse? addr
  pure (⟨pk⟩, a)

def peerCommand (args : List String) : IO UInt32 := do
  let some chainDir := flagValue args "--chain-dir" |
    IO.eprintln usage;
    return 2
  let some keyFile := flagValue args "--node-key" |
    IO.eprintln usage;
    return 2
  let peers := (flagValues args "--boot").filterMap parsePeer
  if peers.isEmpty then
    IO.eprintln "--boot PEERID@IP:PORT is required"
    return 2
  let mode ←
    match (flagValue args "--sync-mode") with
    | none =>
      pure SyncMode.blocks
    | some m =>
      match SyncMode.parse? m with
      | some x =>
        pure x
      | none =>
        IO.eprintln "--sync-mode is blocks, state or auto"
        return 2
  let tracked? : Option (Array UInt64) :=
    (flagValue args "--track-shards").map fun t =>
      ((t.splitOn ",").filterMap String.toNat?).toArray.map (·.toUInt64)
  run
      { mode, tracked := tracked?, publicAddr := (flagValue args "--public-addr").bind Addr.parse?,
        lagLog := flagValue args "--lag-log", saveState := flagValue args "--save-state",
        profile := args.contains "--profile",
        reachLag := ((flagValue args "--reach-lag").bind String.toNat?).getD 5, chainDir, keyFile,
        peers := peers.toArray, configs := (flagValue args "--configs").getD "near-lean/vm/configs",
        listen := (flagValue args "--listen").bind String.toNat? |>.map (·.toUInt16),
        store := flagValue args "--store", apply := !args.contains "--no-apply",
        seconds := (flagValue args "--seconds").bind String.toNat?,
        follow := (flagValue args "--follow").bind String.toNat?,
        drain := ((flagValue args "--drain").bind String.toNat?).getD 0,
        appliedLog := flagValue args "--applied-log", report := flagValue args "--report",
        quiet := args.contains "--quiet" }

/-- The flags a neard home directory stands for (`--home DIR`): `node_key.json`, `validator_key.json`,
`genesis.json`, `data/` for the store and, from `config.json`, `rpc.addr`, `network.addr` (the listen port) and
`network.boot_nodes`. A flag given on the command line wins. -/
def withHome (args : List String) : IO (List String) := do
  let some home := flagValue args "--home" | return args
  let add (flag value : String) (acc : List String) : List String :=
    if (flagValue args flag).isSome then acc else acc ++ [flag, value]
  let mut out := args
  out := add "--node-key" s!"{home}/node_key.json" out
  out := add "--validator-key" s!"{home}/validator_key.json" out
  out := add "--genesis-config" s!"{home}/genesis.json" out
  out := add "--store" s!"{home}/data/lean-store" out
  out := add "--chain-dir" s!"{home}/data/lean-chain" out
  let configFile : System.FilePath := s!"{home}/config.json"
  if ← configFile.pathExists then
    match Lean.Json.parse (← IO.FS.readFile configFile) with
    | .error e =>
      throw (IO.userError s!"{configFile}: {e}")
    | .ok cfg =>
      if let .ok (.str a) := (cfg.getObjVal? "rpc" >>= (·.getObjVal? "addr")) then
        out := add "--rpc-addr" a out
      if let .ok (.str a) := (cfg.getObjVal? "network" >>= (·.getObjVal? "addr")) then
        if let some port := (a.splitOn ":").getLast? then
          out := add "--listen" port out
      if (flagValue args "--boot").isNone then
        if let .ok (.str b) := (cfg.getObjVal? "network" >>= (·.getObjVal? "boot_nodes")) then
          for n in b.splitOn "," do
            if n != "" then
              out := out ++ ["--boot", n]
  return out

def validatorCommand (args : List String) : IO UInt32 := do
  let args ← withHome args
  let some chainDir := flagValue args "--chain-dir" |
    IO.eprintln usage;
    return 2
  let some nodeKey := flagValue args "--node-key" |
    IO.eprintln usage;
    return 2
  let some validatorKey := flagValue args "--validator-key" |
    IO.eprintln usage;
    return 2
  let some peer := (flagValues args "--boot").filterMap parsePeer |>.head? |
    IO.eprintln "--boot PEERID@IP:PORT is required"
    return 2
  let delays :=
    ((flagValue args "--delays").map fun t => (t.splitOn ",").filterMap String.toNat?).getD []
  let opts : Validator.Options :=
    { chainDir, nodeKey, validatorKey, peer,
      configs := (flagValue args "--configs").getD "near-lean/vm/configs",
      listen := (flagValue args "--listen").bind String.toNat? |>.map (·.toUInt16),
      seconds := (flagValue args "--seconds").bind String.toNat?,
      report := flagValue args "--report", appliedLog := flagValue args "--applied-log",
      stopFile := flagValue args "--stop-file", quiet := args.contains "--quiet",
      logFormat := (flagValue args "--log-format").getD "text",
      rpcAddr := (flagValue args "--rpc-addr").bind Addr.parse?, store := flagValue args "--store",
      genesisConfig := flagValue args "--genesis-config", endorsementDelay := delays.getD 0 600,
      baseDelay := delays.getD 1 2000, capDelay := delays.getD 2 6000 }
  Validator.run opts

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] =>
    IO.println s!"near-lean-node (nearcore {nearcoreRelease}, protocol {Near.Node.protocolVersion})"
    return 0
  | "peer" :: rest =>
    peerCommand rest
  | "validator" :: rest =>
    validatorCommand rest
  | _ =>
    IO.eprintln usage
    return 2
