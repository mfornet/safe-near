import NearNode
import NearNode.Net.Uv
import NearNode.Network.Run

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
    "           [--applied-log FILE] [--report FILE] [--configs DIR] [--quiet]"

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
  run
      { chainDir, keyFile, peers := peers.toArray,
        configs := (flagValue args "--configs").getD "near-lean/vm/configs",
        listen := (flagValue args "--listen").bind String.toNat? |>.map (·.toUInt16),
        store := flagValue args "--store", apply := !args.contains "--no-apply",
        seconds := (flagValue args "--seconds").bind String.toNat?,
        follow := (flagValue args "--follow").bind String.toNat?,
        drain := ((flagValue args "--drain").bind String.toNat?).getD 0,
        appliedLog := flagValue args "--applied-log", report := flagValue args "--report",
        quiet := args.contains "--quiet" }

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] =>
    IO.println s!"near-lean-node (nearcore {nearcoreRelease}, protocol {Near.Node.protocolVersion})"
    return 0
  | "peer" :: rest =>
    peerCommand rest
  | _ =>
    IO.eprintln usage
    return 2
