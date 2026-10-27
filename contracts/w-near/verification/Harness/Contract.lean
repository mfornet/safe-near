import Harness.Machine

/-!
# Executable contracts

The executable form of a function contract (plan, section 5.1). A contract
is about one function, given by its Wasm index, and states over the store
and arguments the function is entered with, plus ghost data `α` the
statement is about but the store does not hold (the live allocations, say):

- `pre`: the precondition, decided;
- `footprint`: the byte ranges the function may write;
- `post`: the postcondition, on the run;
- `cost`: the gas it may burn, its entry activation included;
- `stack`: how far below `__stack_pointer` it may write.

`Contract.check` runs the function on one input and checks, besides `post`:
the footprint (no byte outside it, or the stack window, changed; memory did
not grow unless `grows`), every global restored (`__stack_pointer` among
them), no host effect but gas, and the burnt gas against `cost`.

Inputs come from generators (border cases, random), which must satisfy
`pre`, and from call sites, captured while the methods run
(`Harness.capture`), which must satisfy `pre` too: a captured input outside
it means the precondition is too strong for a caller. `probes` are inputs
outside the precondition on which some check must fail: they show that each
clause of `pre` is needed.
-/

namespace WNear.Testing

open Wasm Wasm.Near

structure Input (α : Type) where
  label : String
  store : Store NearState
  args : List Value
  ghost : α

structure Contract (α : Type) where
  name : String
  func : Nat
  pre : Harness → Input α → Option String
  footprint : Harness → Input α → List (Nat × Nat)
  post : Harness → Input α → Run → Option String
  cost : Harness → Input α → Nat
  /-- Bytes below `__stack_pointer` the function may use for its frames. -/
  stack : Nat := 0
  /-- Whether the function may grow memory. -/
  grows : Bool := false
  /-- The ghost data of a captured call-site input, if it can be recovered. -/
  ghostOf : Harness → Entry → Option α

/-- The outcome of checking one input. -/
structure Verdict where
  label : String
  /-- Every check that failed. -/
  failures : List String
  gas : Nat
  cost : Nat

/-- `memcmp` of two pages, through `read8` so an unmaterialised page reads as zeros. -/
private def changedIn (before after : Memory) (page : Nat) : List Nat :=
  let b := before.pages[page]?.getD .empty
  let a := after.pages[page]?.getD .empty
  if b == a then [] else
  (List.range pageSize).filterMap fun i =>
    let addr := page * pageSize + i
    if before.read8 addr == after.read8 addr then none else some addr

/-- The addresses whose byte changed between two memories of the same size. -/
def changedBytes (before after : Memory) : List Nat :=
  (List.range (min before.pages.size after.pages.size)).flatMap (changedIn before after)

def within (ranges : List (Nat × Nat)) (addr : Nat) : Bool :=
  ranges.any fun (a, n) => a ≤ addr && addr < a + n

namespace Contract

variable {α : Type} (c : Contract α) (h : Harness)

/-- The checks that do not depend on the postcondition. -/
def frame (i : Input α) (r : Run) : List String := Id.run do
  -- A trap aborts the call and the receipt rolls back: only the postcondition
  -- says which traps are allowed.
  if let .trapped _ := r.ending then return []
  let mut out := []
  let sp := h.stackPointer i.store
  let allowed := (sp - c.stack, c.stack) :: c.footprint h i
  let before := h.mem r.before
  let after := h.mem r.after
  if after.pages.size != before.pages.size && !c.grows then
    out := out ++ [s!"memory grew from {before.pages.size} to {after.pages.size} pages"]
  let outside := (changedBytes before after).filter (!within allowed ·)
  if let a :: _ := outside then
    out := out ++ [s!"{outside.length} bytes outside the footprint changed, the first at {a}"]
  for g in [0:h.inst.globalAddrs.size] do
    if h.global r.before g != h.global r.after g then
      out := out ++ [s!"global {g} not restored: {repr (h.global r.before g)} to {repr (h.global r.after g)}"]
  let hb := r.before.host
  let ha := r.after.host
  if ha.logs != hb.logs || ha.storageKeys != hb.storageKeys ||
      ha.storageLog.length != hb.storageLog.length || ha.promises.length != hb.promises.length ||
      ha.returnData != hb.returnData || ha.lastError.isSome then
    out := out ++ ["host state changed beyond gas"]
  pure out

/-- Run `c` on `i` and check everything. -/
def check (i : Input α) : Verdict :=
  let r := h.call i.store c.func i.args
  let cost := c.cost h i
  let post := (c.post h i r).toList.map (s!"postcondition: " ++ ·)
  let gas := if r.gas ≤ cost then [] else [s!"burnt {r.gas} gas, above the stated {cost}"]
  { label := i.label, failures := post ++ c.frame h i r ++ gas, gas := r.gas, cost }

end Contract

end WNear.Testing
