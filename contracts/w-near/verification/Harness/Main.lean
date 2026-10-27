import Harness.Builtins
import Harness.StorePair
import Wasm.Binary

/-!
# `wnear-harness`: stress the function contracts

```
lake exe wnear-harness [-v]
```

For each contract of `Harness/Builtins.lean`: border-case and random inputs
(each must satisfy the precondition, and then every check), inputs captured
from the exported methods' real call sites (which must satisfy the
precondition: a call site outside it means the contract is too strong for
its callers), and probes outside the precondition (on which some check must
fail: each clause of the precondition is needed). Prints, per contract, the
inputs checked and how close the stated cost is to the gas burnt. Exits
nonzero on any failure.
-/

open Wasm Wasm.Near WNear.Testing

/-- A deterministic pseudo-random source. -/
structure Rng where
  gen : StdGen

def Rng.nat (r : Rng) (lo hi : Nat) : Nat × Rng :=
  let (n, g) := randNat r.gen lo hi
  (n, ⟨g⟩)

def Rng.bytes (r : Rng) (n : Nat) : List UInt8 × Rng := Id.run do
  let mut r := r
  let mut out := #[]
  for _ in [0:n] do
    let (b, r') := r.nat 0 255
    out := out.push (UInt8.ofNat b)
    r := r'
  pure (out.toList, r)

def orThrow : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- Results of one contract, for the report. -/
structure Tally where
  inputs : Nat := 0
  captured : Nat := 0
  exact : Nat := 0
  /-- The largest ratio of stated cost to gas burnt, in percent. -/
  maxSlack : Nat := 100
  failures : Array String := #[]

def Tally.add (t : Tally) (v : Verdict) (captured : Bool := false) : Tally :=
  { t with
    inputs := t.inputs + 1
    captured := t.captured + (if captured then 1 else 0)
    exact := t.exact + (if v.gas == v.cost then 1 else 0)
    maxSlack := max t.maxSlack (if v.gas == 0 then 100 else v.cost * 100 / v.gas)
    failures := t.failures ++ v.failures.toArray.map (s!"{v.label}: " ++ ·) }

/-- Check generated inputs: each must satisfy the precondition, then pass. -/
def checkInputs (h : Harness) (c : Contract α) (t : Tally) (inputs : List (Input α)) : Tally :=
  inputs.foldl (init := t) fun t i =>
    match c.pre h i with
    | some why => { t with failures := t.failures.push s!"{i.label}: generator outside the precondition: {why}" }
    | none => t.add (c.check h i)

/-- Probes: inputs outside the precondition, on which some check must fail. -/
def checkProbes (h : Harness) (c : Contract α) (t : Tally) (probes : List (Input α)) : Tally :=
  probes.foldl (init := t) fun t i =>
    if (c.pre h i).isNone then
      { t with failures := t.failures.push s!"probe {i.label}: inside the precondition" }
    else if (c.check h i).failures.isEmpty then
      { t with failures := t.failures.push s!"probe {i.label}: passes, so the clause it breaks is not needed" }
    else t

/-! ## Generators -/

/-- Store `bytes` at `addr` in `s`. -/
def put (h : Harness) (s : Store NearState) (writes : List (Nat × List UInt8)) : Except String (Store NearState) :=
  writes.foldlM (fun s (a, bs) => h.write s a bs) s

def memcpyInput (h : Harness) (r : Rng) (label : String) (dst src n : Nat) : Except String (Input Unit × Rng) := do
  let (bs, r) := r.bytes n
  let (junk, r) := r.bytes n
  let s ← put h h.store [(dst, junk), (src, bs)]
  pure ({ label, store := s, args := [i32 dst, i32 src, i32 n], ghost := () }, r)

def memcpyInputs (h : Harness) (r : Rng) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mut r := r
  let mut out := []
  for (label, dst, src, n) in [("empty", 0, 0, 0), ("one byte", 100, 200, 1), ("adjacent", 1000, 1010, 10),
      ("a page", 0, 70000, 65536), ("unaligned", 3, 9001, 77), ("up to the end of memory", top - 50, 0, 50),
      ("from the end of memory", 0, top - 50, 50), ("from the data segment", 5000, 1048576, 200)] do
    let (i, r') ← memcpyInput h r label dst src n
    out := out ++ [i]; r := r'
  for k in [0:200] do
    let (n, r1) := r.nat 0 300
    let (dst, r2) := r1.nat 0 (top - n)
    let (src, r3) := r2.nat 0 (top - n)
    r := r3
    if overlap dst n src n && n > 0 then continue
    let (i, r') ← memcpyInput h r s!"random {k}" dst src n
    out := out ++ [i]; r := r'
  let (overlapping, _) ← memcpyInput h r "overlap, dst after src" 101 100 10
  -- Memory past its end cannot be written: these probes copy zeros.
  let raw (label : String) (dst src n : Nat) : Input Unit :=
    { label, store := h.store, args := [i32 dst, i32 src, i32 n], ghost := () }
  pure (out, [overlapping, raw "dst beyond memory" (top - 4) 0 5, raw "src beyond memory" 0 (top - 4) 5])

def memsetInputs (h : Harness) (r : Rng) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mut r := r
  let mut out := []
  let cases := [("empty", 0, 7, 0), ("one byte", 9, 255, 1), ("high bits of c ignored", 64, 0x1234, 40),
    ("a page", 65536, 0, 65536), ("up to the end of memory", top - 33, 1, 33)]
  let mut randoms := []
  for k in [0:100] do
    let (n, r1) := r.nat 0 300
    let (dst, r2) := r1.nat 0 (top - n)
    let (c, r3) := r2.nat 0 (2 ^ 32 - 1)
    r := r3
    randoms := randoms ++ [(s!"random {k}", dst, c, n)]
  for (label, dst, c, n) in cases ++ randoms do
    let (junk, r') := r.bytes n
    r := r'
    let s ← put h h.store [(dst, junk)]
    out := out ++ [{ label, store := s, args := [i32 dst, i32 c, i32 n], ghost := () }]
  let probes := [{ label := "beyond memory", store := h.store, args := [i32 (top - 2), i32 0, i32 3], ghost := () }]
  pure (out, probes)

def bcmpInputs (h : Harness) (r : Rng) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mut r := r
  let mut out := []
  let one (label : String) (a b : Nat) (xs ys : List UInt8) : Except String (Input Unit) := do
    let s ← put h h.store [(a, xs), (b, ys)]
    pure { label, store := s, args := [i32 a, i32 b, i32 xs.length], ghost := () }
  out := out ++ [← one "empty" 0 0 [] [], ← one "equal" 100 200 [1, 2, 3] [1, 2, 3],
    ← one "same range" 300 300 [5, 6] [5, 6], ← one "first differs, above" 400 500 [9, 0] [1, 0],
    ← one "first differs, below" 600 700 [1, 0] [255, 0], ← one "last differs" 800 900 [1, 2, 3] [1, 2, 4],
    ← one "up to the end of memory" (top - 3) 0 [7, 7, 7] [7, 7, 7]]
  for k in [0:100] do
    let (n, r1) := r.nat 1 200
    let (xs, r2) := r1.bytes n
    let (d, r3) := r2.nat 0 (n - 1)
    let (v, r4) := r3.nat 0 255
    let (same, r5) := r4.nat 0 3
    r := r5
    let ys := if same == 0 then xs else xs.set d (UInt8.ofNat v)
    out := out ++ [← one s!"random {k}" 10000 20000 xs ys]
  let probes := [{ label := "beyond memory", store := h.store, args := [i32 (top - 2), i32 0, i32 3], ghost := () }]
  pure (out, probes)

def multi3Inputs (h : Harness) (r : Rng) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let m64 := 2 ^ 64 - 1
  let mk (label : String) (out : Nat) (a b : Nat) : Input Unit :=
    { label, store := h.store, ghost := (),
      args := [i32 out, i64 (a % 2 ^ 64), i64 (a / 2 ^ 64 % 2 ^ 64), i64 (b % 2 ^ 64), i64 (b / 2 ^ 64 % 2 ^ 64)] }
  let mut r := r
  let mut out := [mk "zero" 0 0 7, mk "one" 16 1 (2 ^ 128 - 1), mk "max squared" 32 (2 ^ 128 - 1) (2 ^ 128 - 1),
    mk "carry out of the low word" 48 m64 m64, mk "high words only" 64 (2 ^ 64) (2 ^ 64),
    mk "unaligned out" 3 12345 67890, mk "at the end of memory" (top - 16) (2 ^ 100) 3,
    mk "a deposit times a price" 80 (10 ^ 24) (10 ^ 12)]
  for k in [0:200] do
    let (bits, r1) := r.nat 0 128
    let (a, r2) := r1.nat 0 (2 ^ bits - 1)
    let (b, r3) := r2.nat 0 (2 ^ 128 - 1)
    r := r3
    out := out ++ [mk s!"random {k}" 256 a b]
  pure (out, [mk "beyond memory" (top - 15) 1 1])

/-- A sequence of allocations and frees from the fresh heap, each allocation
an input whose ghost is the live blocks; every live block is filled with
bytes, so a change to one is seen. -/
def allocInputs (h : Harness) (r : Rng) : Except String (List (Input (List (Nat × Nat))) × List (Input (List (Nat × Nat)))) := do
  let mut r := r
  let mut s := h.store
  let mut live : List (Nat × Nat × Nat) := []
  let mut out := []
  let sizes := [1, 8, 16, 24, 100, 1, 4096, 70000, 3, 200000]
  let mut randoms : List (Nat × Nat × Bool) := []
  for _ in [0:150] do
    let (size, r1) := r.nat 1 2000
    let (alignLog, r2) := r1.nat 0 4
    let (free, r3) := r2.nat 0 2
    r := r3
    randoms := randoms ++ [(size, 2 ^ alignLog, free == 0)]
  let plan : List (Nat × Nat × Bool) := sizes.map (·, 1, false) ++ randoms
  for ((size, align, free), k) in plan.zipIdx do
    -- Free a live block first, a third of the time, to fragment the free list.
    if free && !live.isEmpty then
      let (j, r') := r.nat 0 (live.length - 1)
      r := r'
      let (p, n, a) := live[j]!
      let d := h.call s 311 [i32 p, i32 n, i32 a]
      if let some e := ended d then throw s!"dealloc {p}: {e}"
      s := d.after
      live := live.eraseIdx j
    let i : Input (List (Nat × Nat)) :=
      { label := s!"allocation {k} of {size} bytes aligned {align}", store := s,
        args := [i32 size, i32 align], ghost := live.map fun (p, n, _) => (p, n) }
    out := out ++ [i]
    let run := h.call s alloc.func i.args
    match returnsU32 run with
    | some p =>
      if p == 0 then throw s!"{i.label}: out of memory"
      let (bs, r') := r.bytes (min size 64)
      r := r'
      s ← put h run.after [(p, bs)]
      live := (p, size, align) :: live
    | none => throw s!"{i.label}: {run.ending.describe}"
  let probes : List (Input (List (Nat × Nat))) :=
    [{ label := "zero-sized", store := h.store, args := [i32 0, i32 8], ghost := [] }]
  pure (out, probes)

/-! ## Call sites -/

def account (s : String) : List UInt8 := s.toUTF8.toList

/-- The methods whose call sites are captured, in order, threading storage. -/
def calls : List (String × String × String × Nat) := [
  ("alice.near", "new", "{}", 0),
  ("alice.near", "near_deposit", "{}", 10 ^ 24),
  ("alice.near", "storage_deposit", "{\"account_id\":\"bob.near\"}", 10 ^ 22),
  ("alice.near", "ft_transfer", "{\"receiver_id\":\"bob.near\",\"amount\":\"1000\",\"memo\":\"thanks é\"}", 1),
  ("alice.near", "ft_transfer_call", "{\"receiver_id\":\"bob.near\",\"amount\":\"10\",\"msg\":\"hi\"}", 1),
  ("alice.near", "ft_balance_of", "{\"account_id\":\"alice.near\"}", 0),
  ("alice.near", "ft_total_supply", "{}", 0),
  ("alice.near", "ft_metadata", "{}", 0),
  ("alice.near", "storage_balance_of", "{\"account_id\":\"bob.near\"}", 0),
  ("alice.near", "near_withdraw", "{\"amount\":\"1000\"}", 1),
  ("bob.near", "ft_transfer", "{\"receiver_id\":\"alice.near\",\"amount\":\"1\"}", 1),
  ("alice.near", "ft_transfer", "[\"bob.near\",\"x\"]", 1)]

def contextFor (pred args : String) (deposit : Nat) : VMContext :=
  { internalContext with
    predecessorAccountId := account pred, signerAccountId := account pred,
    input := account args, attachedDeposit := deposit }

/-- Capture the entries into `funcs` across `calls`. -/
def captureAll (protocol : RuntimeConfig) (module : Module) (size : Nat) (funcs : List Nat) :
    IO (Std.HashMap Nat (Array (String × Entry))) := do
  let mut storage := []
  let mut out : Std.HashMap Nat (Array (String × Entry)) := {}
  for (pred, method, args, deposit) in calls do
    let ctx := contextFor pred args deposit
    let (seen, ending) ← orThrow (Harness.capture protocol module method ctx storage funcs)
    if let .stopped e := ending then throw (IO.userError s!"{method}: {repr e}")
    for (f, es) in seen.toList do
      out := out.insert f ((out.getD f #[]) ++ es.map (method, ·))
    let vm := run protocol module size method ctx storage
    if vm.aborted.isNone then storage := vm.storage
  pure out

def report (name : String) (func : Nat) (t : Tally) (verbose : Bool) : IO Bool := do
  let status := if t.failures.isEmpty then "PASS" else "FAIL"
  IO.println s!"{status} {name} ({func}): {t.inputs} inputs, {t.captured} from call sites; \
    stated cost exact on {t.exact}, at most {t.maxSlack}% of the gas burnt"
  for f in (if verbose then t.failures else t.failures.extract 0 10) do IO.println s!"  {f}"
  if !verbose && t.failures.size > 10 then IO.println s!"  ... {t.failures.size - 10} more"
  pure t.failures.isEmpty

def stress (h : Harness) (c : Contract α) (gen : Rng → Except String (List (Input α) × List (Input α)))
    (captured : Array (String × Entry)) (verbose : Bool) : IO Bool := do
  let (inputs, probes) ← orThrow (gen ⟨mkStdGen c.func⟩)
  let mut t := checkInputs h c {} inputs
  t := checkProbes h c t probes
  for (method, e) in captured do
    match c.ghostOf h e with
    | none => pure ()
    | some ghost =>
      let i : Input α := { label := s!"call site in {method}", store := e.store, args := e.args, ghost }
      match c.pre h i with
      | some why => t := { t with failures := t.failures.push s!"{i.label}: precondition too strong: {why}" }
      | none => t := t.add (c.check h i) (captured := true)
  report c.name c.func t verbose

def main (args : List String) : IO UInt32 := do
  let verbose := args.contains "-v"
  let pairOnly := args.contains "--store-pair-only"
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok m => pure m
    | .error e => throw (IO.userError e.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let captured ← captureAll protocol module bytes.size (if pairOnly then [storePair.func] else [memcpy.func, memset.func, bcmp.func, multi3.func, alloc.func, storePair.func])
  let sites (f : Nat) := captured.getD f #[]
  let pairSites := (sites storePair.func).filter (fun (method, _) => method == "ft_total_supply")
  if pairSites.isEmpty then throw (IO.userError "f566: ft_total_supply produced no captured call")
  if !(pairSites.any fun (_, e) => u64Arg e.args 1 != 0 || u64Arg e.args 2 != 0) then
    throw (IO.userError "f566: ft_total_supply capture has no representative nonzero supply")
  for (_, e) in pairSites do
    IO.println s!"f566 ft_total_supply capture: out={u32Arg e.args 0}, low={u64Arg e.args 1}, high={u64Arg e.args 2}"
  match h.store.funcs[h.inst.funcAddrs[storePair.func]!]? with
  | some (.wasm ty _ code) =>
    IO.println s!"f566: type={repr ty}, locals={code.locals.length}, actual body instructions={code.body.length}, activation units={activationGas 1 #[.i32 0, .i64 0, .i64 0]}"
    if code.body.length != 6 || !code.locals.isEmpty then throw (IO.userError "f566: unexpected actual body shape")
  | _ => throw (IO.userError "f566 is not a Wasm function")
  for i in storePairTypeProbes h do
    if (storePair.pre h i).isNone then throw (IO.userError s!"f566 malformed precondition accepted: {i.label}")
  let sample := h.call h.store storePair.func [i32 3, i64 1, i64 2]
  IO.println s!"f566 measured gas={sample.gas}, regular_op_cost={protocol.wasm.regularOpCost}, measured units={sample.gas / protocol.wasm.regularOpCost}; 6 malformed argument prechecks, 3 executable memory probes"
  let pairResult ← stress h storePair (fun _ => storePairInputs h) (sites storePair.func) verbose
  let results ← if pairOnly then pure [pairResult] else pure [
    ← stress h memcpy (memcpyInputs h) (sites memcpy.func) verbose,
    ← stress h memset (memsetInputs h) (sites memset.func) verbose,
    ← stress h bcmp (bcmpInputs h) (sites bcmp.func) verbose,
    ← stress h multi3 (multi3Inputs h) (sites multi3.func) verbose,
    ← stress h alloc (allocInputs h) (sites alloc.func) verbose, pairResult]
  pure (if results.all id then 0 else 1)
