import NearNode

/-! `near-lean-node`: the node executable. Only `--version` exists so far. -/

open Near.Node

def usage : String :=
  "usage: near-lean-node --version"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["--version"] =>
    IO.println s!"near-lean-node (nearcore {nearcoreRelease}, protocol {protocolVersion})"
    return 0
  | _ =>
    IO.eprintln usage
    return 2
