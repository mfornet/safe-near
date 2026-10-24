import Lean.Data.Json

/-!
# Benchmark harness

Each benchmark runs a pure computation a fixed number of times and records
wall time per iteration. Results fold into a checksum so the compiler cannot
drop the work. `node-bench` writes them as JSON for comparison across runs.
-/

namespace Near.Node.Bench

open Lean

structure Benchmark where
  name : String
  iterations : Nat
  /-- One iteration; the result feeds the checksum. -/
  run : Nat → UInt64

structure Result where
  name : String
  iterations : Nat
  totalNanos : Nat
  checksum : UInt64
  deriving ToJson

def Result.nanosPerIteration (r : Result) : Nat :=
  r.totalNanos / max r.iterations 1

def measure (b : Benchmark) : IO Result := do
  let start ← IO.monoNanosNow
  let mut checksum : UInt64 := 0
  for i in [0:b.iterations] do
    checksum := checksum ^^^ b.run i
  let stop ← IO.monoNanosNow
  return { name := b.name, iterations := b.iterations, totalNanos := stop - start, checksum }

def report (results : Array Result) : Json :=
  Json.mkObj [
    ("schema", "node-bench/1"),
    ("results", toJson (results.map fun r =>
      Json.mkObj [
        ("name", r.name), ("iterations", r.iterations), ("totalNanos", r.totalNanos),
        ("nanosPerIteration", r.nanosPerIteration), ("checksum", r.checksum.toNat)]))]

end Near.Node.Bench
