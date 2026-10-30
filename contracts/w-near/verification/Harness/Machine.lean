import NearRuntime.Boundary
import Wasm.Binary

/-!
# Running one function of the binary

The internal-function harness (milestone M1 of
`notes/todo/wnear_refinement_proof.md`, section 5.1). `Harness.load`
instantiates the module exactly as `Wasm.Near.runAttempt` does (prepared
memory, validation, the metered host, linking), and `Harness.call` runs one
function of it, given by its Wasm index, from a store the test has prepared:
memory, `__stack_pointer` and host state. The run charges gas as
`runInitialized` does, so the burnt gas is what a call of the function costs
its caller, apart from the caller's own `call` instruction.

`capture` runs an exported method and records the store and arguments at
every entry into a given function: the inputs real call sites produce.
-/

namespace WNear.Testing

open Wasm Wasm.Near

/-- The instantiated binary: the store just after instantiation (data
segments in memory, globals at their initial values) and the module
instance. -/
structure Harness where
  cfg : RuntimeConfig
  store : Store NearState
  inst : ModuleInst
  /-- Wasm function index of each function address. -/
  indexOf : Std.HashMap Nat Nat

/-- How a run ended. -/
inductive Ending where
  | returned (values : List Value)
  /-- A trap, with the error nearcore reports for it (a host error for a guest panic). -/
  | trapped (error : FunctionCallError)
  /-- The metered loop stopped: out of gas, or an interpreter limit. -/
  | stopped (error : FunctionCallError)

def Ending.describe : Ending → String
  | .returned values => s!"returned {repr values}"
  | .trapped e => s!"trapped: {repr e}"
  | .stopped e => s!"stopped: {repr e}"

structure Run where
  before : Store NearState
  after : Store NearState
  ending : Ending
  /-- Gas burnt by the call, its entry activation included. -/
  gas : Nat

/-- Instantiate `module` under `ctx`, with `storage`, as `runAttempt` does. -/
def Harness.load (cfg : RuntimeConfig) (module : Module) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) : Except String Harness := do
  let code := prepareMemory cfg module
  let valid ← match code.validate (Features.nearcore true) with
    | .ok v => pure v
    | .error e => throw s!"validation: {e.message}"
  let env ← match resolveMetered cfg code with
    | .ok env => pure env
    | .error imp => throw s!"unresolved import {imp}"
  let (store, imports) := env.allocate (Store.empty (ctx.toNearState cfg storage))
  let (store, inst) ← match Link.instantiateModule store valid imports with
    | .ok r => pure r
    | .error e => throw s!"link: {e.message}"
  let indexOf := inst.funcAddrs.toList.zipIdx.foldl (fun m (addr, i) => m.insert addr i) {}
  pure { cfg, store, inst, indexOf }

/-- A context for internal calls: plenty of gas, nothing else that matters. -/
def internalContext : VMContext :=
  { currentAccountId := "wrap.near".toUTF8.toList, signerAccountId := "alice.near".toUTF8.toList,
    signerAccountPk := [], predecessorAccountId := "alice.near".toUTF8.toList, input := [],
    prepaidGas := 300 * 10 ^ 12, accountBalance := 10 ^ 26, storageUsage := 1000 }

namespace Harness

variable (h : Harness)

def memAddr : Nat := h.inst.memAddrs[0]!

def mem (s : Store NearState) : Memory := s.mems[h.memAddr]!

def setMem (s : Store NearState) (m : Memory) : Store NearState :=
  { s with mems := s.mems.set! h.memAddr m }

/-- Global `i` of the module (0 is `__stack_pointer`). -/
def global (s : Store NearState) (i : Nat) : Value := s.globals[h.inst.globalAddrs[i]!]!.value

def setGlobal (s : Store NearState) (i : Nat) (v : Value) : Store NearState :=
  let a := h.inst.globalAddrs[i]!
  { s with globals := s.globals.modify a fun g => { g with value := v } }

def stackPointer (s : Store NearState) : Nat :=
  match h.global s 0 with
  | .i32 v => v.toNat
  | _ => 0

/-- Write bytes at `addr`; fails out of bounds. -/
def write (s : Store NearState) (addr : Nat) (bytes : List UInt8) : Except String (Store NearState) :=
  match (h.mem s).writeBytes addr ⟨bytes.toArray⟩ with
  | some m => pure (h.setMem s m)
  | none => throw s!"write of {bytes.length} bytes at {addr} out of bounds"

def read (s : Store NearState) (addr len : Nat) : List UInt8 :=
  (List.range len).map fun i => (h.mem s).read8 (addr + i)

def readNat (s : Store NearState) (addr len : Nat) : Nat :=
  ((h.mem s).readNat addr len).getD 0

def memSize (s : Store NearState) : Nat := (h.mem s).byteSize

/-- The Wasm function type of function `func`. -/
def funcType? (func : Nat) : Option FuncType :=
  h.inst.funcAddrs[func]? >>= fun a => h.store.funcs[a]? |>.map FuncInst.type

/-- Run function `func` (Wasm index) on `args` from store `s`. -/
def call (s : Store NearState) (func : Nat) (args : List Value) : Run :=
  match h.inst.funcAddrs[func]? >>= fun a => Exec.startWasm s execLimits a args with
  | none => { before := s, after := s, ending := .stopped (.executionIssue
      (.interpreterError s!"function {func} is not a Wasm function")), gas := 0 }
  | some c =>
    let (final, err) := runInitialized h.cfg.wasm 1_000_000_000 (.next c)
    let after : Store NearState := match final with
      | .next c => c.store
      | .done _ st | .trap _ st => st
    let ending : Ending := match err, final with
      | some e, _ => .stopped e
      | none, .done values _ => .returned values
      | none, .trap reason st => .trapped (trapError reason st.host)
      | none, .next _ => .stopped (.executionIssue .fuelExhausted)
    { before := s, after, ending, gas := after.host.gas.burnt - s.host.gas.burnt }

/-- The function a configuration is about to enter, with its arguments:
the target of a `call` or `call_indirect` at the head of the current frame. -/
def callee? (c : Config NearState) : Option (Nat × List Value) := do
  let frame ← c.thread.frames.head?
  let inst ← c.store.modules[frame.inst]?
  let addr ← match ← c.nextInstr? with
    | .call i => inst.funcAddrs[i]?
    | .call_indirect _ t => do
      let tbl ← c.store.tables[← inst.tableAddrs[t]?]?
      let i ← match ← c.stackTop? with
        | .i32 v => some v.toNat
        | _ => none
      match ← tbl.elems[i]? with
      | .func a => some a
      | _ => none
    | _ => none
  let index ← h.indexOf[addr]?
  let ty := (c.store.funcs[addr]?).map FuncInst.type
  let n := (ty.map (·.params.length)).getD 0
  -- `call_indirect` has the table index on top of the arguments.
  let stack := match c.nextInstr? with
    | some (.call_indirect ..) => c.thread.stack.pop
    | _ => c.thread.stack
  pure (index, (stack.extract (stack.size - n) stack.size).toList)

end Harness

/-- A call-site input of a function: the store when it was entered, and its
arguments. -/
structure Entry where
  store : Store NearState
  args : List Value

/-- Run exported `method` under `ctx` on `storage`, and record every entry into
one of `funcs` (at most `limit` per function). Returns the entries by
function, and the method's ending. -/
def Harness.capture (cfg : RuntimeConfig) (module : Module) (method : String) (ctx : VMContext)
    (storage : List (List UInt8 × List UInt8)) (funcs : List Nat) (limit : Nat := 200) :
    Except String (Std.HashMap Nat (Array Entry) × Ending) := do
  let hm ← Harness.load cfg module ctx storage
  let entry ← match hm.inst.export? method with
    | some (.func a) => pure a
    | _ => throw s!"no exported method {method}"
  let some c := Exec.startWasm hm.store execLimits entry [] | throw s!"{method} is not Wasm"
  let charged := chargeWasm (.next c) (entryCost cfg.wasm (.next c))
  if let some e := charged.2 then return ({}, .stopped (.hostError e))
  let mut m := charged.1
  let mut seen : Std.HashMap Nat (Array Entry) := {}
  for _ in [0:200_000_000] do
    match m with
    | .done values _ => return (seen, .returned values)
    | .trap reason st => return (seen, .trapped (trapError reason st.host))
    | .next c =>
      if let some (f, args) := hm.callee? c then
        if funcs.contains f then
          let es := seen.getD f #[]
          if es.size < limit then seen := seen.insert f (es.push { store := c.store, args })
      -- One metered step: fuel 1 stops with `fuelExhausted` on a running machine.
      let (m', err) := runMetered cfg.wasm 1 m
      match err with
      | none | some (.executionIssue .fuelExhausted) => m := m'
      | some e => return (seen, .stopped e)
  throw s!"{method}: step limit"

end WNear.Testing
