import NodeBench.Harness
import NearRuntime.Sha256

/-!
`node-bench [--filter SUBSTRING] [--out FILE]`: run the node benchmarks and
print (or write) their JSON report. Baselines for M2 start from the existing
`Near.Sha256.hash`.
-/

open Near.Node.Bench

def input (size seed : Nat) : List UInt8 :=
  (List.range size).map fun i => UInt8.ofNat (i * 31 + seed)

def sha256 (size iterations : Nat) : Benchmark :=
  { name := s!"sha256/{size}B", iterations,
    run := fun i => ((Near.Sha256.hash (input size i)).foldl (fun a b => a * 31 + b.toUInt64) 0) }

def benchmarks : List Benchmark :=
  [sha256 64 2000, sha256 1024 200, sha256 65536 4]

structure Options where
  filter : String := ""
  out : Option System.FilePath := none

def parse : Options → List String → Except String Options
  | o, [] => .ok o
  | o, "--filter" :: f :: rest => parse { o with filter := f } rest
  | o, "--out" :: f :: rest => parse { o with out := some f } rest
  | _, arg :: _ => .error s!"unknown argument: {arg}"

def main (args : List String) : IO UInt32 := do
  match parse {} args with
  | .error e =>
    IO.eprintln s!"{e}\nusage: node-bench [--filter SUBSTRING] [--out FILE]"
    return 2
  | .ok o =>
    let selected := benchmarks.filter fun b => (b.name.splitOn o.filter).length > 1 || o.filter.isEmpty
    let mut results := #[]
    for b in selected do
      let r ← measure b
      IO.eprintln s!"{r.name}: {r.nanosPerIteration} ns/iter"
      results := results.push r
    let json := (report results).pretty
    match o.out with
    | some path => IO.FS.writeFile path (json ++ "\n")
    | none => IO.println json
    return 0
