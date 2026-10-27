import Harness.Main
import Binary.ValueReturnDispatch
import NearVM.MeteredPrefix

/-! Executable captured-state validation of the exact f456 dispatch fragment.
Run from contracts/w-near/verification:
    lake env lean Proofs/ValueReturnDispatchValidation.lean
This test checks the real table selection, byte return, gas, caller suffix,
stack and memory after fourteen actual metered steps. -/
namespace WNear.Proofs.ValueReturnDispatchValidation
open Wasm Wasm.Near WNear.Testing

def seek (cfg : WasmConfig) : Nat → Machine → Except String (Config NearState)
  | 0, _ => .error "f456 dispatch fragment not reached"
  | fuel + 1, .next current =>
    match current.thread.frames.head? with
    | none => .error "f456 has no frame"
    | some frame =>
      if reprStr (frame.code.take 10) == reprStr WNear.Binary.ValueReturnDispatch.dispatch then
        .ok current
      else
        let next := MeteredPrefix.advance cfg (.next current)
        match next.2 with
        | some error => .error s!"f456 stopped before dispatch: {repr error}"
        | none => seek cfg fuel next.1
  | _, .trap reason _ => .error s!"f456 trapped before dispatch: {repr reason}"
  | _, .done _ _ => .error "f456 returned before dispatch"

def steps (cfg : WasmConfig) : Nat → Machine → Except String Machine
  | 0, machine => .ok machine
  | fuel + 1, machine =>
    let next := MeteredPrefix.advance cfg machine
    match next.2 with
    | some error => .error s!"dispatch stopped: {repr error}"
    | none => steps cfg fuel next.1

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← match Wasm.Binary.decode bytes with
    | .ok module => pure module
    | .error error => throw (IO.userError error.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [456]
  let captures := seen.getD 456 #[]
  if captures.isEmpty then throw (IO.userError "no actual f456 captures")
  for (method, entry) in captures do
    let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[456]! entry.args
      | throw (IO.userError "cannot start actual f456")
    let before ← orThrow (seek h.cfg.wasm 100000 (.next initial))
    let some frame := before.thread.frames.head? | throw (IO.userError "dispatch has no caller frame")
    let cell := match before.thread.stack.back! with | .i32 cell => cell.toNat | _ => 0
    let slice := match frame.locals[1]! with | .i32 slice => slice.toNat | _ => 0
    let len := h.readNat before.store (slice + 4) 4
    let ptr := h.readNat before.store slice 4
    let vtable := h.readNat before.store (cell + 4) 4
    let element := h.readNat before.store (vtable + 92) 4
    let table := before.store.tables[h.inst.tableAddrs[0]!]!
    match table.elems[element]? with
    | some (.func address) =>
      if h.indexOf.get? address != some 260 then throw (IO.userError "vtable did not select f260")
    | _ => throw (IO.userError "vtable target is not a function")
    let final ← orThrow (steps h.cfg.wasm 14 (.next before))
    let .next after := final | throw (IO.userError "dispatch failed to resume its caller")
    let expected := h.read before.store ptr len
    let fees := before.store.host.fees.newDataReceiptByte
    let dataCost := (before.store.host.outputDataReceivers.map fun receiver =>
      fees.send (receiver == before.store.host.context.currentAccountId) * len + fees.execution * len).sum
    let expectedGas := op h 24 + before.store.host.extCosts.cost "base" +
      before.store.host.extCosts.cost "read_memory_base" + before.store.host.extCosts.cost "read_memory_byte" * len + dataCost
    let gas := after.store.host.gas.burnt - before.store.host.gas.burnt
    if after.store.host.returnData != some expected || gas != expectedGas then
      throw (IO.userError s!"wrong f456 dispatch bytes/gas: {method},gas={gas},expected={expectedGas}")
    let some afterFrame := after.thread.frames.head? | throw (IO.userError "dispatch lost caller frame")
    if reprStr after.thread.stack != reprStr before.thread.stack.pop ||
        reprStr afterFrame.code != reprStr (frame.code.drop 10) ||
        after.thread.frames.length != before.thread.frames.length then
      throw (IO.userError "dispatch did not restore the saved caller/operand prefix")
    if !(changedBytes (h.mem before.store) (h.mem after.store)).isEmpty then
      throw (IO.userError "dispatch changed memory")
    if method == "ft_total_supply" then
      IO.println s!"f456 dispatch actual totalSupply: cell={cell},slice={slice},vtable={vtable},tableIndex={element},target=f260,len={len},gas={gas}"
  IO.println s!"PASS actual f456 dispatch: {captures.size} captured checks, exact 14-step caller return, bytes, memory and gas"

#eval validate

end WNear.Proofs.ValueReturnDispatchValidation
