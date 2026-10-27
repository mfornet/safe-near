import Harness.Builtins

/-! Executable accepted-branch contract for deployed f158 (`Result::expect`).
The panic branch for discriminant one is explicitly outside this contract. -/
namespace WNear.Testing
open Wasm Wasm.Near

/-- The second source load observes the first eight-byte output write. -/
def expectResultBytes (h : Harness) (store : Store NearState) (out src : Nat) : List UInt8 :=
  let low := h.read store (src + 4) 8
  let high := (List.range 4).map fun i =>
    let address := src + 12 + i
    if out ≤ address && address < out + 8 then low[address - out]!
    else (h.read store address 1).head!
  low ++ high

def expectResult : Contract Unit where
  name := "Result::expect/accepted"
  func := 158
  pre h i :=
    match i.args, h.global i.store 0 with
    | [.i32 out, .i32 src, .i32 _], .i32 _ =>
      if out.toNat + 12 > h.memSize i.store then some "out + 12 beyond memory"
      else if src.toNat + 16 > h.memSize i.store then some "src + 16 beyond memory"
      else if h.readNat i.store src.toNat 4 == 1 then some "panic discriminant one"
      else none
    | _, _ => some "expected exactly [i32, i32, i32] and i32 stack global"
  footprint _ i := [(u32Arg i.args 0, 12)]
  post h i r :=
    match r.ending with
    | .returned [] =>
      if h.read r.after (u32Arg i.args 0) 12 ==
          expectResultBytes h r.before (u32Arg i.args 0) (u32Arg i.args 1) then none
      else some "output differs from sequential accepted payload copy"
    | _ => some s!"expected void return, got {r.ending.describe}"
  -- 64 fixed bytes + three i32 parameters + one i32 local =10 activation
  -- units; 26 paid instructions on the accepted branch, with a free block.
  cost h _ := activationGas h.cfg.wasm.regularOpCost #[.i32 0, .i32 0, .i32 0, .i32 0] + op h 26
  ghostOf h e := if h.readNat e.store (u32Arg e.args 1) 4 == 1 then none else some ()

def expectResultInputs (h : Harness) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mk (label : String) (out src sp tag seed : Nat) : Except String (Input Unit) := do
    let s := h.setGlobal h.store 0 (i32 sp)
    let s ← h.write s out (List.replicate 12 0xA5)
    let tagBytes := (List.range 4).map fun i => UInt8.ofNat (tag / 2 ^ (8 * i))
    let payload := (List.range 12).map fun i => UInt8.ofNat (seed + 17 * i)
    let s ← h.write s src (tagBytes ++ payload)
    pure { label, store := s, args := [i32 out, i32 src, i32 (2 ^ 32 - 1)], ghost := () }
  let mut inputs := []
  for (out, src, label) in [(0, 64, "zero output"), (64, 0, "zero source"),
      (3, 101, "unaligned"), (65529, 100, "output crosses page"),
      (100, 65529, "source crosses page"), (top - 12, 64, "last output"),
      (64, top - 16, "last source"), (100, 100, "same address"),
      (108, 100, "second read overwritten by first write")] do
    for tag in [0, 2, 2 ^ 32 - 1] do
      inputs := inputs ++ [← mk s!"{label}/tag{tag}" out src (h.stackPointer h.store) tag 3]
  for delta in [0:33] do
    inputs := inputs ++ [← mk s!"alias offset {delta}-16" 1016 (1000 + delta) 1024 0 (delta * 11)]
  for sp in [0, 1, 15, 16, 2 ^ 32 - 1] do
    inputs := inputs ++ [← mk s!"wrapping stack arithmetic {sp}" 128 256 sp 0 19]
  let mut gen := mkStdGen 158
  for k in [0:150] do
    let (out, g1) := randNat gen 0 (top - 12)
    let (src, g2) := randNat g1 0 (top - 16)
    let (seed, g3) := randNat g2 0 255
    gen := g3
    inputs := inputs ++ [← mk s!"random {k}" out src (h.stackPointer h.store) 0 seed]
  let raw (label : String) (out src : Nat) : Input Unit :=
    { label, store := h.store, args := [i32 out, i32 src, i32 0], ghost := () }
  pure (inputs, [raw "output beyond memory" (top - 11) 0,
    raw "source beyond memory" 0 (top - 15), raw "wrapped-negative source" 0 (2 ^ 32 - 1)])

def expectResultTypeProbes (h : Harness) : List (Input Unit) :=
  let raw (label : String) (args : List Value) : Input Unit :=
    { label, store := h.store, args, ghost := () }
  [raw "no arguments" [], raw "missing location" [i32 0, i32 0],
   raw "extra argument" [i32 0, i32 0, i32 0, i32 0],
   raw "wrong output type" [i64 0, i32 0, i32 0],
   raw "wrong source type" [i32 0, i64 0, i32 0],
   raw "wrong location type" [i32 0, i32 0, i64 0]]

end WNear.Testing
