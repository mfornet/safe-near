import Harness.BalanceOf

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

def vecDerefInputs (h : Harness) (r : Rng) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mut r := r
  let mut out := []
  for k in [0:100] do
    let (vec, r1) := r.nat 0 (top - 12)
    let (dst, r2) := r1.nat 0 (top - 8)
    let (bs, r3) := r2.bytes 12
    r := r3
    if overlap (dst + 4) 4 vec 4 then continue
    let s ← put h h.store [(vec, bs)]
    out := out ++ [{ label := s!"random {k}", store := s, args := [i32 dst, i32 vec], ghost := () }]
  let (bs, _) := r.bytes 12
  let s ← put h h.store [(100, bs.set 8 77)]
  let s' ← put h h.store [(100, bs)]
  let harmless : Input Unit :=
    { label := "out over the capacity and length", store := s', args := [i32 104, i32 100], ghost := () }
  let probe : Input Unit :=
    { label := "the length's slot over the pointer", store := s, args := [i32 96, i32 100], ghost := () }
  pure (out ++ [harmless], [probe])

/-- Every method's prologue: `setup_panic_hook` (522), then
`set_blockchain_interface` (520) with near-sdk's zero-sized interface and
its vtable. Its postcondition is the ghost "environment set up". -/
def prologue (h : Harness) (s : Store NearState) : Except String (Store NearState) := do
  let r1 := h.call s 522 []
  if let some e := ended r1 then throw s!"setup_panic_hook: {e}"
  let r2 := h.call r1.after 520 [i32 1, i32 1050188]
  if let some e := ended r2 then throw s!"set_blockchain_interface: {e}"
  pure r2.after

/-- `base` is a store from inside a method, where the environment is set up. -/
def stateInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let top := h.memSize base
  let mut r := r
  let mut out := []
  -- An absent state: tag word zero.
  let (bs0, r0) := r.bytes 40
  r := r0
  let none0 := bs0.set 24 0 |>.set 25 0 |>.set 26 0 |>.set 27 0
  let s0 ← put h base [(200, none0)]
  out := out ++ [{ label := "not initialized", store := s0, args := [i32 1000, i32 200], ghost := true }]
  -- The same from a fresh store after the method's prologue: the ghost is
  -- the prologue's postcondition.
  let fresh ← prologue h h.store
  let s1 ← put h fresh [(200, none0)]
  let afterPrologue : Input Bool :=
    { label := "not initialized, after the prologue", store := s1, args := [i32 1000, i32 200], ghost := true }
  out := out ++ [afterPrologue]
  for k in [0:50] do
    let (opt, r1) := r.nat 0 (top - 40)
    let (dst, r2) := r1.nat 0 (top - 40)
    let (bs, r3) := r2.bytes 40
    r := r3
    if overlap dst 40 opt 40 then continue
    let bs := bs.set 24 1
    let s ← put h base [(opt, bs)]
    out := out ++ [{ label := s!"random {k}", store := s, args := [i32 dst, i32 opt], ghost := true }]
  let p0 ← put h h.store [(200, none0)]
  let probe : Input Bool :=
    { label := "not initialized, environment not set up", store := p0, args := [i32 1000, i32 200], ghost := false }
  pure (out, [probe])

def u128FromInputs (h : Harness) (r : Rng) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mut r := r
  let mut out := []
  for k in [0:50] do
    let (dst, r1) := r.nat 0 (top - 16)
    let (lo, r2) := r1.nat 0 (2 ^ 64 - 1)
    let (hi, r3) := r2.nat 0 (2 ^ 64 - 1)
    r := r3
    out := out ++ [{ label := s!"random {k}", store := h.store, args := [i32 dst, i64 lo, i64 hi], ghost := () }]
  let pargs := [i32 (top - 8), i64 1, i64 1]
  let probe : Input Unit := { label := "beyond memory", store := h.store, args := pargs, ghost := () }
  pure (out, [probe])

def ftTotalSupplyInputs (h : Harness) (r : Rng) : Except String (List (Input Unit) × List (Input Unit)) := do
  let top := h.memSize h.store
  let mut r := r
  let mut out := []
  for k in [0:50] do
    let (ft, r1) := r.nat 0 (top - 16)
    let (dst, r2) := r1.nat 0 (top - 16)
    let (bs, r3) := r2.bytes 16
    r := r3
    let s ← put h h.store [(ft, bs)]
    out := out ++ [{ label := s!"random {k}", store := s, args := [i32 dst, i32 ft], ghost := () }]
  pure (out, [])

def expectInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let top := h.memSize base
  let mut r := r
  let mut out : List (Input Bool) := []
  let mut probes : List (Input Bool) := []
  for k in [0:50] do
    let (res, r1) := r.nat 0 (top - 16)
    let (dst, r2) := r1.nat 0 (top - 12)
    let (bs, r3) := r2.bytes 16
    let (err, r4) := r3.nat 0 3
    r := r4
    if overlap dst 8 (res + 12) 4 then continue
    let bs := if err == 0 then bs.set 0 1 |>.set 1 0 |>.set 2 0 |>.set 3 0 else bs.set 0 0
    let s ← put h base [(res, bs)]
    let i : Input Bool := { label := s!"random {k}", store := s, args := [i32 dst, i32 res, i32 1049036], ghost := true }
    -- One garbage error is enough to show the clause is needed.
    if err == 0 then
      if probes.isEmpty then probes := [{ i with label := s!"Err with a garbage error {k}" }]
    else out := out ++ [i]
  pure (out, probes)

/-- `base` with `v` (or nothing) stored at `key`. -/
def withStorage (base : Store NearState) (key : List UInt8) (v : Option (List UInt8)) : Store NearState :=
  { base with host := { base.host with storage := fun k => if k == key then v else base.host.storage k } }

def leBytes (n len : Nat) : List UInt8 := (List.range len).map fun i => UInt8.ofNat (n / 256 ^ i)

def stateReadInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let absent : Input Bool := { label := "absent", store := withStorage base stateKey none, args := [i32 1000], ghost := true }
  let mut out : List (Input Bool) := [absent]
  for k in [0:30] do
    let (n, r1) := r.nat 0 10
    let (pre, r2) := r1.bytes n
    let (supply, r3) := r2.nat 0 (2 ^ 128 - 1)
    let (usage, r4) := r3.nat 0 (2 ^ 64 - 1)
    r := r4
    let v := leBytes n 4 ++ pre ++ leBytes supply 16 ++ leBytes usage 8
    out := out ++ [{ label := s!"random {k}", store := withStorage base stateKey (some v), args := [i32 1000], ghost := true }]
  let bad : Input Bool := { label := "a state that does not decode", store := withStorage base stateKey (some [1, 2, 3]), args := [i32 1000], ghost := true }
  pure (out, [bad])

def toVecInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let mut out : List (Input Bool) := []
  let border := [0, 1, 9, 10, 10 ^ 24, 2 ^ 64 - 1, 2 ^ 64, 2 ^ 128 - 1]
  let mut randoms := []
  for _ in [0:30] do
    let (bits, r1) := r.nat 0 128
    let (n, r2) := r1.nat 0 (2 ^ bits - 1)
    r := r2
    randoms := randoms ++ [n]
  for (n, k) in (border ++ randoms).zipIdx do
    let s ← put h base [(2000, leBytes n 16)]
    out := out ++ [{ label := s!"{n} ({k})", store := s, args := [i32 1000, i32 2000], ghost := true }]
  pure (out, [])

def valueReturnInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let mut out : List (Input Bool) := []
  for k in [0:30] do
    let (n, r1) := r.nat 0 200
    let (bs, r2) := r1.bytes n
    r := r2
    let s ← put h base [(3000, bs)]
    out := out ++ [{ label := s!"{n} bytes ({k})", store := s, args := [i32 3000, i32 n], ghost := true }]
  pure (out, [])

def envInputInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let mut out : List (Input Bool) := []
  for k in [0:30] do
    let (n, r1) := r.nat 0 300
    let (bs, r2) := r1.bytes n
    r := r2
    let s : Store NearState :=
      { base with host := { base.host with context := { base.host.context with input := bs } } }
    out := out ++ [{ label := s!"{n} bytes ({k})", store := s, args := [i32 1000], ghost := true }]
  pure (out, [])

def optionExpectInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let mut out : List (Input Bool) := []
  for k in [0:30] do
    let (bs, r1) := r.bytes 12
    let (none?, r2) := r1.nat 0 3
    r := r2
    let bs := if none? == 0 then bs.set 0 0 |>.set 1 0 |>.set 2 0 |>.set 3 0 else bs.set 0 1
    let s ← put h base [(4000, bs)]
    out := out ++ [{ label := s!"random {k}", store := s, args := [i32 1000, i32 4000, i32 1049036], ghost := true }]
  pure (out, [])

/-- A contract struct at 6000 with the prefix `"a"` (at 6100), and an
account id `String` whose buffer is a real heap allocation, at 6200. -/
def balanceInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let mut out : List (Input Bool) := []
  for k in [0:30] do
    let (n, r1) := r.nat 2 20
    let (name, r2) := r1.bytes n
    let (present, r3) := r2.nat 0 2
    let (bal, r4) := r3.nat 0 (2 ^ 128 - 1)
    r := r4
    let alloc := h.call base 310 [i32 n, i32 1]
    let some buf := returnsU32 alloc | throw "alloc failed"
    let s ← put h alloc.after [(6100, [97]), (6000 + 24, leBytes 6100 4 ++ leBytes 1 4 ++ leBytes 1 4),
      (buf, name), (6200, leBytes buf 4 ++ leBytes n 4 ++ leBytes n 4)]
    let key := [97] ++ leBytes n 4 ++ name
    let s := if present == 0 then s else withStorage s key (some (leBytes bal 16))
    out := out ++ [{ label := s!"random {k}", store := s, args := [i32 1000, i32 6000, i32 6200], ghost := true }]
  pure (out, [])

/-- Border-case arguments of `ft_balance_of`, as JSON. -/
def balanceOfArgs : List String := [
  "{\"account_id\":\"bob.near\"}", " { \"account_id\" : \"bob.near\" } ", "{\"\\u0061ccount_id\":\"bob.near\"}",
  "{\"account_id\":\"b\\u006fb.near\"}", "[\"bob.near\"]", "{\"account_id\":\"bob.near\",\"x\":1}",
  "{\"account_id\":\"bob.near\",\"account_id\":\"bob.near\"}", "{\"account_id\":\"A\"}",
  "{\"account_id\":\"a\"}", "{\"account_id\":1}", "{}", "", "garbage", "{\"account_id\":\"bob.near\"",
  "{\"account_id\":\"bob.near\"} x", "{\"account_id\":\"\"}", "{\"account_id\":null}",
  "{\"account_id\":\"alice.near\\u0000\"}", "{\"x\":{\"y\":[1,2,{\"z\":\"w\"}]},\"account_id\":\"carol.near\"}",
  "[\"bob.near\",1]", "{\"account_id\":\"" ++ String.ofList (List.replicate 64 'a') ++ "\"}",
  "{\"account_id\":\"" ++ String.ofList (List.replicate 65 'a') ++ "\"}"]

def fromSliceInputs (h : Harness) (base : Store NearState) (_ : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut out : List (Input Bool) := []
  let cases : List (List UInt8) := balanceOfArgs.map (fun s : String => s.toUTF8.toList) ++ [[255, 254]]
  for (j, k) in cases.zipIdx do
    let s ← put h base [(7000, j)]
    out := out ++ [{ label := s!"case {k}", store := s, args := [i32 1000, i32 7000, i32 j.length], ghost := true }]
  pure (out, [])

def storageMinimumInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let mut out : List (Input Bool) := []
  let border := [0, 1, 125, 2 ^ 32, 2 ^ 64 - 1]
  let mut randoms := []
  for _ in [0:20] do
    let (n, r1) := r.nat 0 (2 ^ 64 - 1)
    r := r1
    randoms := randoms ++ [n]
  for (n, k) in (border ++ randoms).zipIdx do
    let s ← put h base [(6000 + 16, leBytes n 8)]
    out := out ++ [{ label := s!"usage {n} ({k})", store := s, args := [i32 1000, i32 6000], ghost := true }]
  pure (out, [])

def ftMetadataInputs (h : Harness) (base : Store NearState) (_ : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) :=
  pure ([{ label := "the contract", store := base, args := [i32 1000, i32 6000], ghost := true }], [])

def storageBoundsInputs (h : Harness) (base : Store NearState) (r : Rng) :
    Except String (List (Input Bool) × List (Input Bool)) := do
  let mut r := r
  let mut out : List (Input Bool) := []
  for (n, k) in ([0, 1, 125, 2 ^ 64 - 1] ++ (List.range 10).map (· * 1234567)).zipIdx do
    let s ← put h base [(6000 + 16, leBytes n 8)]
    out := out ++ [{ label := s!"usage {n} ({k})", store := s, args := [i32 1000, i32 6000], ghost := true }]
  pure (out, [])

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
  ("alice.near", "storage_minimum_balance", "{}", 0),
  ("alice.near", "storage_balance_bounds", "{}", 0),
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
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok m => pure m
    | .error e => throw (IO.userError e.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let captured ← captureAll protocol module bytes.size
    [memcpy.func, memset.func, bcmp.func, multi3.func, alloc.func, vecDeref.func, stateOrPanic.func,
      u128From.func, ftTotalSupply.func, resultExpect.func, stateRead.func, toVecU128.func,
      valueReturn.func, envInput.func, optionExpect.func, balanceOf.func, fromSliceBalanceOf.func,
      storageMinimum.func, ftMetadata.func, storageBounds.func]
  let sites (f : Nat) := captured.getD f #[]
  -- A fresh store after the method prologue: the environment is set up.
  let envBase ← orThrow (prologue h h.store)
  let results := [
    ← stress h memcpy (memcpyInputs h) (sites memcpy.func) verbose,
    ← stress h memset (memsetInputs h) (sites memset.func) verbose,
    ← stress h bcmp (bcmpInputs h) (sites bcmp.func) verbose,
    ← stress h multi3 (multi3Inputs h) (sites multi3.func) verbose,
    ← stress h alloc (allocInputs h) (sites alloc.func) verbose,
    ← stress h vecDeref (vecDerefInputs h) (sites vecDeref.func) verbose,
    ← stress h stateOrPanic
        (stateInputs h (((sites stateOrPanic.func)[0]?.map (·.2.store)).getD h.store))
        (sites stateOrPanic.func) verbose,
    ← stress h u128From (u128FromInputs h) (sites u128From.func) verbose,
    ← stress h ftTotalSupply (ftTotalSupplyInputs h) (sites ftTotalSupply.func) verbose,
    ← stress h resultExpect
        (expectInputs h (((sites stateOrPanic.func)[0]?.map (·.2.store)).getD h.store))
        (sites resultExpect.func) verbose,
    ← stress h stateRead
        (stateReadInputs h (((sites stateRead.func)[0]?.map (·.2.store)).getD h.store))
        (sites stateRead.func) verbose,
    ← stress h toVecU128
        (toVecInputs h (((sites stateRead.func)[0]?.map (·.2.store)).getD h.store))
        (sites toVecU128.func) verbose,
    ← stress h valueReturn (valueReturnInputs h envBase) (sites valueReturn.func) verbose,
    ← stress h envInput (envInputInputs h envBase) (sites envInput.func) verbose,
    ← stress h optionExpect (optionExpectInputs h envBase) (sites optionExpect.func) verbose,
    ← stress h balanceOf (balanceInputs h envBase) (sites balanceOf.func) verbose,
    ← stress h fromSliceBalanceOf (fromSliceInputs h envBase) (sites fromSliceBalanceOf.func) verbose,
    ← stress h storageMinimum (storageMinimumInputs h envBase) (sites storageMinimum.func) verbose,
    ← stress h ftMetadata (ftMetadataInputs h envBase) (sites ftMetadata.func) verbose,
    ← stress h storageBounds (storageBoundsInputs h envBase) (sites storageBounds.func) verbose]
  pure (if results.all id then 0 else 1)
