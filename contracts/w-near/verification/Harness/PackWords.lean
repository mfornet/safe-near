import Harness.Builtins

/-! Executable, alias-aware contract for actual deployed f779. -/
namespace WNear.Testing
open Wasm Wasm.Near

/-- f779 reads the source's word at +8, writes out+4, then reads the source's
word at +0 from that updated memory before writing out+0. In particular,
source=out+4 duplicates the first word written, rather than the original low
word. This oracle uses byte selection, not the interpreter's memory writer. -/
def packWordsBytes (h : Harness) (store : Store NearState) (out src : Nat) : List UInt8 :=
  let high := h.read store (src + 8) 4
  let low := (List.range 4).map fun i =>
    let address := src + i
    if out + 4 ≤ address && address < out + 8 then high[address - (out + 4)]!
    else (h.read store address 1).head!
  low ++ high

def packWords : Contract Unit where
  name := "pack-two-u32/sequential"
  func := 779
  pre h i :=
    match i.args with
    | [.i32 out, .i32 src] =>
      if out.toNat + 8 > h.memSize i.store then some "out + 8 beyond memory"
      else if src.toNat + 12 > h.memSize i.store then some "src + 12 beyond memory"
      else none
    | _ => some "expected exactly [i32, i32]"
  footprint _ i := [(u32Arg i.args 0, 8)]
  post h i r :=
    match r.ending with
    | .returned [] =>
      if h.read r.after (u32Arg i.args 0) 8 ==
          packWordsBytes h r.before (u32Arg i.args 0) (u32Arg i.args 1) then none
      else some "output differs from sequential two-word copy"
    | _ => some s!"expected void return, got {r.ending.describe}"
  cost h _ := activationGas h.cfg.wasm.regularOpCost #[.i32 0, .i32 0] + op h 8
  ghostOf _ _ := some ()

/-- Alias offsets exercise the first write overlapping the second read,
including partial-byte overlap; the expected result follows the actual order. -/
def packWordsInputs (h : Harness) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  if top < 65560 then throw "pack-words tests require memory beyond one page"
  let mk (label : String) (out src seed : Nat) : Except String (Input Unit) := do
    let s ← h.write h.store out (List.replicate 8 0xA5)
    let bytes := (List.range 12).map fun i => UInt8.ofNat (seed + 17 * i)
    let s ← h.write s src bytes
    pure { label, store := s, args := [i32 out, i32 src], ghost := () }
  let mut inputs := []
  for (out, src, label) in [(0, 64, "zero output"), (64, 0, "zero source"),
      (3, 101, "unaligned"), (65533, 100, "output crosses page"),
      (100, 65529, "source crosses page"), (top - 8, 64, "last output"),
      (64, top - 12, "last source"), (100, 100, "same address"),
      (100, 104, "second read overwritten by first write"),
      (104, 100, "output after source")] do
    inputs := inputs ++ [← mk label out src 3]
  for delta in [0:25] do
    inputs := inputs ++ [← mk s!"alias offset {delta}-12" 1012 (1000 + delta) (delta * 11)]
  let mut gen := mkStdGen 779
  for k in [0:150] do
    let (out, g1) := randNat gen 0 (top - 8)
    let (src, g2) := randNat g1 0 (top - 12)
    let (seed, g3) := randNat g2 0 255
    gen := g3
    inputs := inputs ++ [← mk s!"random {k}" out src seed]
  let raw (label : String) (out src : Nat) : Input Unit :=
    { label, store := h.store, args := [i32 out, i32 src], ghost := () }
  pure (inputs, [raw "output one byte beyond" (top - 7) 0,
    raw "source one byte beyond" 0 (top - 11),
    raw "wrapped-negative source" 0 (2 ^ 32 - 1)])

/-- Malformed ABI probes are checked without invoking unvalidated Wasm locals. -/
def packWordsTypeProbes (h : Harness) : List (Input Unit) :=
  let raw (label : String) (args : List Value) : Input Unit :=
    { label, store := h.store, args, ghost := () }
  [raw "no arguments" [], raw "missing source" [i32 0],
   raw "extra argument" [i32 0, i32 0, i32 0],
   raw "wrong output type" [i64 0, i32 0], raw "wrong source type" [i32 0, i64 0]]

end WNear.Testing
