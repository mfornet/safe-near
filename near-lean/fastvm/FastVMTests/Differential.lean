import FastVMTests.Module

/-!
# `fastvm-differential`

The fast engine against the specification.

`lake exe fastvm-differential [--configs DIR] [--seed N] [--programs N] [--exhaustive N] [--wnear FILE.wat]`

* random modules (`FastVMTests.Module`), each run with the gas limits swept over the whole run: every
  instruction boundary of a short run, a sample of points (and the points next to them) of a longer one, for
  both limits (`prepaid` and `max_gas_burnt`); the outcomes must agree field by field (`outcomeKey`) and, for
  the unlimited run, the final machines must agree (memory, globals, gas profile);
* the same for the wNEAR contract of the VM's own test suite, when `--wnear` names its `.wat`.

Exit code 1 on any difference.
-/

open FastVMTests Wasm Wasm.Near NearFastVM

structure Counts where
  programs : Nat := 0
  rejected : Nat := 0
  runs : Nat := 0
  fastRan : Nat := 0
  fellBack : Nat := 0
  mismatches : Nat := 0
  machineChecks : Nat := 0

def ctxFor (input : List UInt8) (prepaid : Nat) (view : Option Nat := none) : VMContext :=
  { currentAccountId := "wrap.near".toUTF8.toList, signerAccountId := "alice.near".toUTF8.toList
    signerAccountPk := 0 :: List.replicate 32 1, predecessorAccountId := "alice.near".toUTF8.toList
    input, attachedDeposit := 1000, prepaidGas := prepaid, accountBalance := 100 * 10 ^ 24,
    storageUsage := 150000, blockHeight := 77, blockTimestamp := 1_000_000_007, epochHeight := 3,
    randomSeed := List.replicate 32 9, viewConfig := view.map fun m => { maxGasBurnt := m } }

def withMaxBurnt (cfg : RuntimeConfig) (m : Nat) : RuntimeConfig :=
  { cfg with wasm := { cfg.wasm with limits := { cfg.wasm.limits with maxGasBurnt := m } } }

/-- Compare one run; `true` when the two agree. -/
def compareRun (counts : IO.Ref Counts) (label : String) (cfg : RuntimeConfig) (code : Module)
    (method : String) (ctx : VMContext) (storage : List (List UInt8 × List UInt8)) : IO Bool := do
  let spec := Wasm.Near.run cfg code 1000 method ctx storage
  let fast := NearFastVM.run cfg code 1000 method ctx storage
  counts.modify fun c => { c with runs := c.runs + 1 }
  let a := outcomeKey spec
  let b := outcomeKey fast
  if a == b then
    return true
  counts.modify fun c => { c with mismatches := c.mismatches + 1 }
  IO.println s!"MISMATCH {label}\n  spec: {a}\n  fast: {b}"
  return false

/-- Whether the engine ran the call (and did not fall back to the specification). -/
def engineRan (cfg : RuntimeConfig) (code : Module) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) : Option (Option String) :=
  match prepare cfg code 1000 method ctx storage with
  | .failed _ => none
  | .ready store addr c =>
    match execute cfg.wasm store addr with
    | none => some none
    | some fast =>
      let spec := runInitialized cfg.wasm (fuelFor cfg code ctx) (.next c)
      some (some ((machineDiff spec fast).getD ""))

def sweepProgram (counts : IO.Ref Counts) (label : String) (cfg : RuntimeConfig) (code : Module)
    (method : String) (input : List UInt8) (storage : List (List UInt8 × List UInt8)) (rng : Rng)
    (exhaustive : Nat) (samples : Nat) : IO Unit := do
  let big := 40_000_000_000
  let ctx0 := ctxFor input big
  match engineRan cfg code method ctx0 storage with
  | none =>
    counts.modify fun c => { c with rejected := c.rejected + 1 }
  | some r =>
    match r with
    | none =>
      counts.modify fun c => { c with fellBack := c.fellBack + 1 }
    | some d =>
      counts.modify fun c =>
          { c with
            fastRan := c.fastRan + 1, machineChecks := c.machineChecks + 1 }
      if d != "" then
        counts.modify fun c => { c with mismatches := c.mismatches + 1 }
        IO.println s!"MACHINE MISMATCH {label}: {d}"
    let full := Wasm.Near.run cfg code 1000 method ctx0 storage
    let burnt := full.burntGas
    let _ ← compareRun counts s!"{label} full" cfg code method ctx0 storage
    -- the points to try: prepaid values around the burnt gas of the full run
    let reg := cfg.wasm.regularOpCost
    let n := burnt / reg
    let mut points : Array Nat := #[0, 1, burnt - 1, burnt, burnt + 1]
    let mut r := rng
    if n ≤ exhaustive then
      for k in [0:n + 2] do
        points := points ++ #[k * reg - 1, k * reg, k * reg + 1]
    else
      for _ in [0:samples] do
        let (v, r') := r.next
        r := r'
        let k := (v % (n + 2).toUInt64).toNat
        let (w, r'') := r.next
        r := r''
        let delta := (w % (reg.toUInt64 + 2)).toNat
        points := points ++ #[k * reg, k * reg + 1, k * reg - 1, k * reg + delta]
    for p in points do
      let _ ← compareRun counts s!"{label} prepaid={p}" cfg code method (ctxFor input p) storage
      -- the same limit as the per-call burn limit: GasLimitExceeded instead of GasExceeded
      let _ ←
        compareRun counts s!"{label} maxBurnt={p}" (withMaxBurnt cfg p) code method ctx0 storage

def probeModule (body : List Instr) (locals : List ValType := [.i32, .i32, .i32, .i32]) : Module :=
  { types := #[{ params := [], results := [] }], funcs := #[{ type := 0, locals, body }],
    mems := #[{ type := { limits := { min := 1, max := none } } }],
    exports := #[{ name := "main", desc := .func 0 }] }

def probeModule2 (body callee : List Instr) : Module :=
  { types := #[{ params := [], results := [] }, { params := [.i32], results := [] }],
    funcs :=
      #[{ type := 0, locals := [.i32], body },
        { type := 1, locals := [.i32, .i64], body := callee }],
    mems := #[{ type := { limits := { min := 1, max := none } } }],
    exports := #[{ name := "main", desc := .func 0 }] }

def probes2 : List (String × List Instr × List Instr) :=
  [("call", [.i32_const 5, .call 1], [.local_get 0, .drop]),
    ("call-fill", [.i32_const 5, .call 1],
      [.i32_const 1897, .i32_const 16843009, .i32_const 13, .memory_fill]),
    ("call-copy", [.i32_const 5, .call 1],
      [.i32_const 850, .i32_const 1174, .i32_const 255, .memory_copy]),
    ("call-twice", [.i32_const 5, .call 1, .i32_const 5, .call 1], [.local_get 0, .drop]),
    ("store", [.i32_const 5, .call 1],
      [.i32_const 0, .i64_const 7, .store .i64 (some 32) { align := 0, offset := 65535 }]),
    ("c0", [.i32_const 5, .call 1], []), ("c1", [.i32_const 5, .call 1], [.i32_const 1, .drop]),
    ("c2", [.i32_const 5, .call 1], [.i32_const 1, .drop, .i32_const 1, .drop]),
    ("c3", [.i32_const 5, .call 1], [.i64_const 1, .i64_const 1, .i64_binop .add, .drop]),
    ("f32", [.i32_const 5, .call 1],
      [.f32_const 31, .cvt .f64_promote_f32, .f64_const 7, .f64_relop .le, .drop])]

def runProbes (cfg : RuntimeConfig) : IO Nat := do
  let mut bad := 0
  for (name, body, callee) in probes2 do
    let m := probeModule2 body callee
    let counts ← IO.mkRef ({} : Counts)
    let ok ← compareRun counts s!"probe {name}" cfg m "main" (ctxFor [] 40_000_000_000) []
    let a := Wasm.Near.run cfg m 1000 "main" (ctxFor [] 40_000_000_000) []
    let b := NearFastVM.run cfg m 1000 "main" (ctxFor [] 40_000_000_000) []
    IO.println
        s!"{name}: spec {a.gasProfile.wasm / cfg.wasm.regularOpCost} units, fast {b.gasProfile.wasm / cfg.wasm.regularOpCost}"
    if !ok then
      bad := bad + 1
  return bad

def probes : List (String × List Instr) :=
  [("fill", [.i32_const 100, .i32_const 7, .i32_const 13, .memory_fill]),
    ("copy", [.i32_const 100, .i32_const 7, .i32_const 255, .memory_copy]),
    ("grow", [.i32_const 1, .memory_grow, .drop]),
    ("loop",
      [.i32_const 5, .local_set 0,
        .loop .empty [.local_get 0, .i32_const 1, .i32_binop .sub, .local_tee 0, .br_if 0]]),
    ("block-br", [.block .empty [.i32_const 1, .br_if 0, .nop], .nop]),
    ("if", [.i32_const 1, .«if» .empty [.nop] [.nop, .nop], .nop]),
    ("brtable", [.block .empty [.block .empty [.i32_const 1, .br_table [0, 1] 1], .nop], .nop])]

def runProbes1 (cfg : RuntimeConfig) : IO Nat := do
  let mut bad := 0
  for (name, body) in probes do
    let m := probeModule body
    let counts ← IO.mkRef ({} : Counts)
    let ok ← compareRun counts s!"probe {name}" cfg m "main" (ctxFor [] 40_000_000_000) []
    if !ok then
      bad := bad + 1
  return bad

def benchBody (n : UInt64) : List Instr :=
  [.i64_const n, .local_set 0,
    .block .empty
      [.loop .empty
          [.local_get 0, .i64_eqz, .br_if 1, .local_get 1, .local_get 0, .i64_binop .add,
            .local_set 1, .local_get 0, .i64_const 1, .i64_binop .sub, .local_set 0, .br 0]]]

def runBench (cfg : RuntimeConfig) (n : UInt64) (specToo : Bool) : IO Unit := do
  let m := probeModule (benchBody n) [.i64, .i64]
  let ctx := ctxFor [] 300_000_000_000_000
  let t0 ← IO.monoNanosNow
  let b := NearFastVM.run cfg m 1000 "main" ctx []
  IO.println s!"burnt {b.burntGas}"
  let t1 ← IO.monoNanosNow
  IO.println
      s!"fast: {(t1 - t0) / 1000000} ms, wasm units {b.gasProfile.wasm / cfg.wasm.regularOpCost}, aborted {b.aborted.isSome}"
  if specToo then
    let a := Wasm.Near.run cfg m 1000 "main" ctx []
    IO.println s!"burnt {a.burntGas}"
    let t2 ← IO.monoNanosNow
    IO.println s!"spec: {(t2 - t1) / 1000000} ms, same {outcomeKey a == outcomeKey b}"

/-- The wNEAR contract of the VM's test suite: the calls of `vm-tests` threaded through one storage, each compared
with the gas swept over a sample of limits. -/
def runWNear (cfg : RuntimeConfig) (path : String) : IO Nat := do
  let text ← IO.FS.readFile path
  let code ← Wasm.Wat.compile! text
  let counts ← IO.mkRef ({} : Counts)
  let wrap := "wrap.near".toUTF8.toList
  let alice := "alice.near".toUTF8.toList
  let bob := "bob.near".toUTF8.toList
  let oneNear := 10 ^ 24
  let reg := 125 * 10 ^ 19
  let call (pred : List UInt8) (input : String) (deposit : Nat) (gas : Nat) : VMContext :=
    let c := ctxFor input.toUTF8.toList gas
    { c with currentAccountId := wrap, signerAccountId := pred, predecessorAccountId := pred, attachedDeposit := deposit, accountBalance := 100 * oneNear }
  let steps : List (String × List UInt8 × String × Nat) :=
    [("near_deposit", alice, "{}", oneNear), ("storage_deposit", bob, "{}", 2 * reg),
     ("ft_balance_of", bob, "{\"account_id\":\"alice.near\"}", 0),
     ("ft_total_supply", bob, "{}", 0),
     ("ft_transfer", alice, "{\"receiver_id\":\"bob.near\",\"amount\":\"5000\"}", 1),
     ("ft_transfer_call", alice, "{\"receiver_id\":\"bob.near\",\"amount\":\"1000\",\"msg\":\"hi\"}", 1),
     ("near_withdraw", alice, "{\"amount\":\"1000\"}", 1),
     ("near_withdraw", alice, "{\"amount\":\"1000\"}", 0),
     ("near_withdraw", alice, "{\"amount\":\"99999999999999999999999999\"}", 1),
     ("near_deposit", alice, "{}", 0), ("no_such_method", alice, "{}", 0),
     ("ft_resolve_transfer", wrap, "{\"sender_id\":\"alice.near\",\"receiver_id\":\"bob.near\",\"amount\":\"1000\"}", 0),
     ("ft_resolve_transfer", alice, "{\"sender_id\":\"alice.near\",\"receiver_id\":\"bob.near\",\"amount\":\"1000\"}", 0),
     ("storage_balance_of", bob, "{\"account_id\":\"bob.near\"}", 0)]
  let mut storage : List (List UInt8 × List UInt8) := []
  let mut bad := 0
  for (method, pred, input, deposit) in steps do
    let ctx := call pred input deposit (300 * 10 ^ 12)
    let spec := Wasm.Near.run cfg code 200000 method ctx storage
    let ok ← compareRun counts s!"wnear {method}" cfg code method ctx storage
    if !ok then bad := bad + 1
    -- the gas limits: every tenth of the burnt gas, and the points around them
    let burnt := spec.burntGas
    for k in [0:41] do
      let p := burnt * k / 40
      for q in [p - 1, p, p + 1] do
        let ok ← compareRun counts s!"wnear {method} prepaid={q}" cfg code method (call pred input deposit q) storage
        if !ok then bad := bad + 1
        let ok ← compareRun counts s!"wnear {method} maxBurnt={q}" (withMaxBurnt cfg q) code method ctx storage
        if !ok then bad := bad + 1
    if spec.succeeded then storage := spec.storage
  let c ← counts.get
  IO.println s!"wnear: {c.runs} comparisons, {c.mismatches} mismatches"
  return bad

def parseArgs (args : List String) : List (String × String) :=
  let rec go : List String → List (String × String)
    | k :: v :: rest => if k.startsWith "--" then (k, v) :: go rest else go (v :: rest)
    | _ => []
  go args

def main (args : List String) : IO UInt32 := do
  let opts := parseArgs args
  let get (k : String) (d : String) : String := ((opts.find? (·.1 == k)).map (·.2)).getD d
  let configs := get "--configs" "../vm/configs"
  let seed := (get "--seed" "1").toNat!
  let programs := (get "--programs" "200").toNat!
  let exhaustive := (get "--exhaustive" "300").toNat!
  let samples := (get "--samples" "40").toNat!
  let cfg ← RuntimeConfig.load configs 86
  if get "--wnear" "" != "" then
    return (← runWNear cfg (get "--wnear" "")).toUInt32
  if get "--bench" "" != "" then
    runBench cfg (get "--bench" "0").toNat!.toUInt64 (get "--spec" "0" == "1")
    return 0
  if get "--probes" "" == "1" then
    return ((← runProbes cfg) + (← runProbes1 cfg)).toUInt32
  let counts ← IO.mkRef ({} : Counts)
  let hosts := meteredHostFns cfg
  for i in [0:programs] do
    let ps := (seed + i).toUInt64 * 0x2545F4914F6CDD1D
    let ((module, input), rng) :=
      (do
            let m ← genModule hosts
            let len ← below 40
            let mut bytes : List UInt8 := []
            for _ in [0:len] do
              bytes := (← rand).toUInt8 :: bytes
            return (m, bytes) : Gen _).run
        { state := ps }
    counts.modify fun c => { c with programs := c.programs + 1 }
    if get "--show" "" == toString (seed + i) then
      IO.println (repr module.funcs).pretty
    let storage : List (List UInt8 × List UInt8) := [([1, 2, 3], [4, 5, 6]), ([7], [8, 9])]
    sweepProgram counts s!"program seed={seed + i}" cfg module "main" input storage rng exhaustive
        samples
    if i % 25 == 24 then
      let c ← counts.get
      IO.println s!"... {i + 1} programs, {c.runs} runs, {c.mismatches} mismatches"
  let c ← counts.get
  IO.println
      s!"programs {c.programs} (rejected by the validator {c.rejected}, engine ran {c.fastRan}, fell back {c.fellBack}); \
    {c.runs} outcome comparisons, {c.machineChecks} machine comparisons; {c.mismatches} mismatches"
  return if c.mismatches == 0 then 0 else 1
