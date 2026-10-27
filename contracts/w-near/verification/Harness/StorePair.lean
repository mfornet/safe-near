import Harness.Builtins

/-! Executable contract for deployed f566 (local code entry 518).
This validates the actual runtime; it does not claim a kernel proof. -/
namespace WNear.Testing
open Wasm Wasm.Near

/-- Eight low-to-high bytes, independent of the runtime's store operation. -/
def wordBytes (word : Nat) : List UInt8 :=
  (List.range 8).map fun byte => UInt8.ofNat (word / 2 ^ (8 * byte) % 256)

/-- f566 writes the low word at out and high word at out+8, returning void.
Unaligned output is permitted. Its three parameters occupy 20 activation
bytes: activationGas charges 11 units, followed by six ordinary instructions. -/
def storePair : Contract Unit where
  name := "U128::from/store-pair"
  func := 566
  pre h i :=
    match i.args with
    | [.i32 out, .i64 _, .i64 _] =>
      if out.toNat + 16 ≤ h.memSize i.store then none else some "out + 16 beyond memory"
    | _ => some "expected exactly [i32, i64, i64]"
  footprint _ i := [(u32Arg i.args 0, 16)]
  post h i r :=
    match r.ending with
    | .returned [] =>
      if h.read r.after (u32Arg i.args 0) 16 ==
          wordBytes (u64Arg i.args 1) ++ wordBytes (u64Arg i.args 2) then none
      else some "output differs from low/high little-endian words"
    | _ => some s!"expected void return, got {r.ending.describe}"
  cost h _ := activationGas h.cfg.wasm.regularOpCost #[.i32 0, .i64 0, .i64 0] + op h 6
  ghostOf _ _ := some ()

/-- Border and reproducible random inputs, including every pair of word
patterns, unaligned/cross-page writes and the last valid output address. -/
def storePairInputs (h : Harness) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  if top < 65552 then throw "store-pair tests require memory beyond one page"
  let mk (label : String) (out low high : Nat) : Except String (Input Unit) := do
    let store ← h.write h.store out (List.replicate 16 0xA5)
    pure { label, store, args := [i32 out, i64 low, i64 high], ghost := () }
  let patterns := [0, 1, 255, 256, 2 ^ 32 - 1, 2 ^ 32, 2 ^ 63, 2 ^ 64 - 1,
    0x0123456789abcdef, 0xfedcba9876543210, 0xaaaaaaaaaaaaaaaa, 0x5555555555555555]
  let mut inputs := []
  for (addr, name) in [(0, "zero address"), (3, "unaligned"), (65529, "cross page"),
      (65536, "page boundary"), (top - 16, "last valid")] do
    for (low, j) in patterns.zipIdx do
      for (high, k) in patterns.zipIdx do
        inputs := inputs ++ [← mk s!"{name}, patterns {j}/{k}" addr low high]
  let mut gen := mkStdGen 566
  for k in [0:200] do
    let (addr, gen1) := randNat gen 0 (top - 16)
    let (low, gen2) := randNat gen1 0 (2 ^ 64 - 1)
    let (high, gen3) := randNat gen2 0 (2 ^ 64 - 1)
    gen := gen3
    inputs := inputs ++ [← mk s!"random {k}" addr low high]
  let raw (label : String) (args : List Value) : Input Unit :=
    { label, store := h.store, args, ghost := () }
  let probes := [raw "one byte beyond last valid" [i32 (top - 15), i64 1, i64 2],
    raw "output at memory end" [i32 top, i64 1, i64 2],
    raw "wrapped-negative output" [i32 (2 ^ 32 - 1), i64 1, i64 2]]
  pure (inputs, probes)

/-- Malformed raw harness arguments must fail the contract precondition.
They are not executed: Harness.call/Exec.startWasm assumes validated caller
arguments, so malformed locals may panic rather than report a Wasm trap. -/
def storePairTypeProbes (h : Harness) : List (Input Unit) :=
  let raw (label : String) (args : List Value) : Input Unit :=
    { label, store := h.store, args, ghost := () }
  [raw "no arguments" [], raw "missing argument" [i32 0, i64 1],
    raw "extra argument" [i32 0, i64 1, i64 2, i64 3],
    raw "wrong output type" [i64 0, i64 1, i64 2],
    raw "wrong low type" [i32 0, i32 1, i64 2],
    raw "wrong high type" [i32 0, i64 1, i32 2]]

end WNear.Testing
