import Harness.Builtins

/-! Executable accepted-branch contract for actual deployed f155. -/
namespace WNear.Testing
open Wasm Wasm.Near

/-- The actual memcpy951 loop reads each source byte after earlier writes.
The oracle retains that sequential behavior even for overlapping pointers. -/
def unwrapStateBytes (h : Harness) (s : Store NearState) (out source : Nat) : List UInt8 :=
  (List.range 40).foldl (fun written i =>
    let address := source + i
    let byte := if out ≤ address && address < out + i then written[address - out]!
      else (h.read s address 1).head!
    written ++ [byte]) []

def unwrapState : Contract Unit where
  name := "unwrap-state/some/sequential40"
  func := 155
  pre h i := match i.args with
    | [.i32 out, .i32 source] =>
      if out.toNat + 40 > h.memSize i.store then some "out + 40 beyond memory"
      else if source.toNat + 40 > h.memSize i.store then some "source + 40 beyond memory"
      else if h.readNat i.store (source.toNat + 24) 4 == 0 then some "absent state tag"
      else none
    | _ => some "expected exactly [i32, i32]"
  footprint _ i := [(u32Arg i.args 0, 40)]
  post h i r := match r.ending with
    | .returned [] =>
      if h.read r.after (u32Arg i.args 0) 40 ==
          unwrapStateBytes h r.before (u32Arg i.args 0) (u32Arg i.args 1) then none
      else some "output differs from sequential forty-byte copy"
    | _ => some s!"expected void return, got {r.ending.describe}"
  -- Entry9; accepted scalar path7; call951opcode1; actual memcpy40 cost736.
  cost h _ := op h 753
  ghostOf h e := if h.readNat e.store (u32Arg e.args 1 + 24) 4 == 0 then none else some ()

def unwrapStateInputs (h : Harness) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  if top < 65580 then throw "unwrap tests require memory beyond one page"
  let mk (label : String) (out source seed tag : Nat) : Except String (Input Unit) := do
    let s ← h.write h.store out (List.replicate 40 0xA5)
    let s ← h.write s source ((List.range 40).map (fun i => UInt8.ofNat (seed + 17 * i)))
    let tagBytes := (List.range 4).map (fun i => UInt8.ofNat (tag >>> (8 * i)))
    let s ← h.write s (source + 24) tagBytes
    pure { label, store := s, args := [i32 out, i32 source], ghost := () }
  let mut inputs := []
  for (out, source, label) in [(0, 128, "zero output"), (128, 0, "zero source"),
      (3, 103, "unaligned"), (65517, 128, "output crosses page"),
      (128, 65517, "source crosses page"), (top - 40, 128, "last output"),
      (128, top - 40, "last source"), (1000, 1000, "same address"),
      (1000, 1040, "getter adjacent ranges"), (1040, 1000, "reverse adjacent ranges")] do
    inputs := inputs ++ [← mk label out source 3 1]
  for delta in [0:79] do
    inputs := inputs ++ [← mk s!"alias delta {delta}-39" 1039 (1000 + delta) (delta * 11) 1]
  for tag in [1, 2, 2 ^ 31, 2 ^ 32 - 1] do
    inputs := inputs ++ [← mk s!"nonzero tag {tag}" 100 200 0 tag]
  let mut gen := mkStdGen 155
  for k in [0:150] do
    let (out, g1) := randNat gen 0 (top - 40)
    let (source, g2) := randNat g1 0 (top - 40)
    let (seed, g3) := randNat g2 0 255
    gen := g3
    inputs := inputs ++ [← mk s!"random {k}" out source seed 1]
  let raw (label : String) (out source : Nat) (store : Store NearState) : Input Unit :=
    { label, store, args := [i32 out, i32 source], ghost := () }
  let absent ← h.write h.store 224 [0, 0, 0, 0]
  pure (inputs, [raw "output one byte beyond" (top - 39) 200 h.store,
    raw "source one byte beyond" 100 (top - 39) h.store,
    raw "absent state tag" 100 200 absent])

def unwrapStateTypeProbes (h : Harness) : List (Input Unit) :=
  let raw (label : String) (args : List Value) : Input Unit :=
    { label, store := h.store, args, ghost := () }
  [raw "no arguments" [], raw "missing source" [i32 0], raw "extra argument" [i32 0, i32 0, i32 0],
   raw "wrong output type" [i64 0, i32 0], raw "wrong source type" [i32 0, i64 0]]

end WNear.Testing
