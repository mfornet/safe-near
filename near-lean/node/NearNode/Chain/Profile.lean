import Std.Data.HashMap

/-!
# Stage timers of the chunk application

`Prof` sums the wall time of named stages (`near-lean-node peer --profile`, `node-chain-apply
--profile`). `timed` runs a pure stage and charges it to its name; without a `Prof` it only runs the
stage. The stage is evaluated between the two clock reads because `timed` is not inlined and the
result is inspected before the second read.
-/

namespace Near.Node.Apply

/-- Calls and nanoseconds by stage name, in first-use order. -/
structure Prof where
  cells : IO.Ref (Array (String × Nat × Nat))

def Prof.new : IO Prof := do
  pure { cells := ← IO.mkRef #[] }

def Prof.add (p : Prof) (name : String) (ns : Nat) : IO Unit :=
  p.cells.modify fun cells =>
    match cells.findIdx? (·.1 == name) with
    | some i => cells.modify i fun (n, calls, t) => (n, calls + 1, t + ns)
    | none => cells.push (name, 1, ns)

/-- The stages, as `(name, calls, milliseconds)`. -/
def Prof.rows (p : Prof) : IO (Array (String × Nat × Nat)) := do
  pure ((← p.cells.get).map fun (n, calls, ns) => (n, calls, ns / 1000000))

/-- One line per stage with its share of the sum of all stages (the stages do not overlap). -/
def Prof.render (p : Prof) : IO String := do
  let rows ← p.rows
  let all := rows.foldl (fun a r => a + r.2.2) 0
  let line (r : String × Nat × Nat) : String :=
    let pct := if all == 0 then "" else s!" ({r.2.2 * 100 / all}%)"
    s!"  {r.1}: {r.2.2} ms in {r.2.1} calls{pct}"
  pure ("\n".intercalate (rows.toList.map line) ++ s!"\n  total: {all} ms")

/-- Effects of a stage: failure with a message, and the clock. -/
abbrev AM :=
  ExceptT String IO

/-- Runs `f`, charging its wall time to `name` when a profile is kept. -/
@[noinline]
def timed (p : Option Prof) (name : String) (f : Unit → Except String α) : AM α := do
  match p with
  | none =>
    match f () with
    | .ok a =>
      pure a
    | .error e =>
      throw e
  | some prof =>
    let t0 ← IO.monoNanosNow
    match f () with
    | .ok a =>
      let t1 ← IO.monoNanosNow
      prof.add name (t1 - t0)
      pure a
    | .error e =>
      let t1 ← IO.monoNanosNow
      prof.add name (t1 - t0)
      throw e

end Near.Node.Apply
