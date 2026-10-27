import Harness.StorePair

/-! Executable contract for deployed f414, the ft_total_supply caller of f566.
The stack slot and output may alias the source or each other. The expected
memory follows the actual sequence: snapshot source, write stack slot, write
output. No disjointness premise is introduced. -/
namespace WNear.Testing
open Wasm Wasm.Near

def storePairCaller : Contract Unit where
  name := "ft_total_supply/store-pair-caller"
  func := 414
  pre h i :=
    match i.args, h.global i.store 0 with
    | [.i32 out, .i32 src], .i32 sp =>
      if out.toNat + 16 > h.memSize i.store then some "out + 16 beyond memory"
      else if src.toNat + 16 > h.memSize i.store then some "src + 16 beyond memory"
      else if sp.toNat < 16 then some "stack pointer underflows its 16-byte slot"
      else if sp.toNat > h.memSize i.store then some "stack slot beyond memory"
      else none
    | _, _ => some "expected exactly [i32, i32] and an i32 stack global"
  footprint _ i := [(u32Arg i.args 0, 16)]
  stack := 16
  post h i r :=
    match r.ending with
    | .returned [] =>
      let bytes := h.read i.store (u32Arg i.args 1) 16
      let scratch := h.stackPointer i.store - 16
      match h.write i.store scratch bytes >>= fun s => h.write s (u32Arg i.args 0) bytes with
      | .error e => some s!"invalid expected write sequence: {e}"
      | .ok expected =>
        if h.read r.after (u32Arg i.args 0) 16 != h.read expected (u32Arg i.args 0) 16 then
          some "output differs from initial source bytes"
        else if h.read r.after scratch 16 != h.read expected scratch 16 then
          some "stack slot differs from sequential alias-aware writes"
        else none
    | _ => some s!"expected void return, got {r.ending.describe}"
  -- Own activation: 64+4+4+4+8 bytes =>11 units. Body29, nested f566
  -- activation11 and body6. The outer caller's call opcode is separate.
  cost h _ := activationGas h.cfg.wasm.regularOpCost #[.i32 0, .i32 0, .i32 0, .i64 0] + op h (29 + 11 + 6)
  ghostOf _ _ := some ()

def storePairCallerInputs (h : Harness) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mk (label : String) (out src sp low high : Nat) : Except String (Input Unit) := do
    let store := h.setGlobal h.store 0 (i32 sp)
    let store ← h.write store (sp - 16) (List.replicate 16 0xA5)
    let store ← h.write store src (wordBytes low ++ wordBytes high)
    pure { label, store, args := [i32 out, i32 src], ghost := () }
  let patterns := [(0, 0), (1, 2 ^ 64 - 1), (2 ^ 64 - 1, 0),
    (2 ^ 63, 2 ^ 32), (0x0123456789abcdef, 0xfedcba9876543210),
    (0xaaaaaaaaaaaaaaaa, 0x5555555555555555)]
  let placements := [("disjoint", 128, 256, 1024), ("unaligned", 3, 101, 1027),
    ("output equals source", 256, 256, 1024), ("source equals stack slot", 128, 1008, 1024),
    ("output equals stack slot", 1008, 256, 1024), ("all equal", 1008, 1008, 1024),
    ("output after source overlap", 261, 256, 1024), ("output before source overlap", 251, 256, 1024),
    ("output before stack overlap", 1001, 256, 1024), ("output after stack overlap", 1015, 256, 1024),
    ("source crosses stack slot", 128, 1001, 1024), ("three overlapping ranges", 1011, 1005, 1024),
    ("cross-page output", 65529, 256, 1024), ("cross-page source", 128, 65529, 1024),
    ("cross-page stack", 128, 256, 65543), ("last valid output", top - 16, 256, 1024),
    ("last valid source", 128, top - 16, 1024), ("last valid stack", 128, 256, top),
    ("first valid stack", 128, 256, 16)]
  let mut inputs := []
  for (label, out, src, sp) in placements do
    for (low, high) in patterns do
      inputs := inputs ++ [← mk label out src sp low high]
  let mut gen := mkStdGen 414
  for k in [0:200] do
    let (out, g1) := randNat gen 0 (top - 16)
    let (src, g2) := randNat g1 0 (top - 16)
    let (sp, g3) := randNat g2 16 top
    let (low, g4) := randNat g3 0 (2 ^ 64 - 1)
    let (high, g5) := randNat g4 0 (2 ^ 64 - 1)
    gen := g5
    inputs := inputs ++ [← mk s!"random {k}" out src sp low high]
  let raw (label : String) (out src sp : Nat) : Input Unit :=
    { label, store := h.setGlobal h.store 0 (i32 sp), args := [i32 out, i32 src], ghost := () }
  pure (inputs, [raw "output out of bounds" (top - 15) 256 1024,
    raw "source out of bounds" 128 (top - 15) 1024,
    raw "stack underflow" 128 256 15,
    raw "stack out of bounds" 128 256 (top + 1)])

/-- ABI rejection is checked before raw Harness.call, whose entry assumes
validated typed arguments, as for f566. -/
def storePairCallerTypeProbes (h : Harness) : List (Input Unit) :=
  [{label := "missing argument", store := h.store, args := [i32 128], ghost := ()},
   {label := "extra argument", store := h.store, args := [i32 128, i32 256, i32 0], ghost := ()},
   {label := "wrong output type", store := h.store, args := [i64 128, i32 256], ghost := ()},
   {label := "wrong source type", store := h.store, args := [i32 128, i64 256], ghost := ()},
   {label := "wrong stack global type", store := h.setGlobal h.store 0 (i64 1024),
     args := [i32 128, i32 256], ghost := ()}]

end WNear.Testing
