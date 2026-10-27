import Harness.UnwrapState
import Wasm.Binary

open Wasm Wasm.Near WNear.Testing

private def orFail : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def main (_args : List String) : IO UInt32 := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orFail ((Wasm.Binary.decode bytes).mapError (·.message))
  let ctx := { internalContext with input := "{}".toUTF8.toList }
  let initial := run protocol module bytes.size "new" ctx []
  if initial.aborted.isSome then throw (IO.userError s!"new failed: {repr initial.aborted}")
  let funded := run protocol module bytes.size "near_deposit" {ctx with attachedDeposit := 10 ^ 24} initial.storage
  if funded.aborted.isSome then throw (IO.userError s!"near_deposit failed: {repr funded.aborted}")
  let (seen, ending) ← orFail (Harness.capture protocol module "ft_total_supply" ctx funded.storage [155, 156, 951])
  match ending with
  | .returned _ => pure ()
  | _ => throw (IO.userError s!"getter did not return: {ending.describe}")
  let h ← orFail (Harness.load protocol module ctx funded.storage)
  let captured := seen.getD 155 #[]
  if captured.isEmpty then throw (IO.userError "no actual ft_total_supply f155 capture")
  if !(seen.getD 156 #[]).isEmpty then throw (IO.userError "initialized getter entered f156 panic")
  for i in unwrapStateTypeProbes h do
    if (unwrapState.pre h i).isNone then throw (IO.userError s!"accepted malformed ABI: {i.label}")
  let (inputs, probes) ← orFail (unwrapStateInputs h)
  let mut count := 0
  let mut exact := 0
  for i in inputs ++ captured.toList.map (fun e => { label := "ft_total_supply captured", store := e.store, args := e.args, ghost := () }) do
    if let some why := unwrapState.pre h i then throw (IO.userError s!"{i.label}: bad precondition: {why}")
    let verdict := unwrapState.check h i
    if !verdict.failures.isEmpty then throw (IO.userError s!"{i.label}: {verdict.failures}")
    count := count + 1
    if verdict.gas == verdict.cost then exact := exact + 1
  for i in probes do
    if (unwrapState.pre h i).isNone then throw (IO.userError s!"probe inside precondition: {i.label}")
    if (unwrapState.check h i).failures.isEmpty then throw (IO.userError s!"probe passed: {i.label}")
  let fuelProbe (function fuel : Nat) (e : Entry) : IO Unit := do
    let some c := Exec.startWasm e.store execLimits h.inst.funcAddrs[function]! e.args |
      throw (IO.userError "fuel probe could not start")
    let exactRun := runInitialized protocol.wasm fuel (.next c)
    let belowRun := runInitialized protocol.wasm (fuel - 1) (.next c)
    match exactRun with
    | (.done _ _, none) => pure ()
    | _ => throw (IO.userError s!"f{function} expected completion at fuel {fuel}")
    match belowRun.2 with
    | some (.executionIssue .fuelExhausted) => pure ()
    | _ => throw (IO.userError s!"f{function} expected exhaustion below fuel {fuel}")
    IO.println s!"f{function} exact fuel boundary={fuel}"
  for e in captured do fuelProbe 155 701 e
  for e in (seen.getD 951 #[]) do
    if u32Arg e.args 2 == 40 then fuelProbe 951 691 e
  for e in captured do
    let measured := h.call e.store 155 e.args
    IO.println s!"f155 capture: out={u32Arg e.args 0}, source={u32Arg e.args 1}, tag={h.readNat e.store (u32Arg e.args 1 + 24) 4}, gas={measured.gas}, units={measured.gas / protocol.wasm.regularOpCost}"
  for e in (seen.getD 951 #[]) do
    if u32Arg e.args 2 == 40 then
      let measured := h.call e.store 951 e.args
      IO.println s!"f951 memcpy40 capture: gas={measured.gas}, units={measured.gas / protocol.wasm.regularOpCost}"
  IO.println s!"PASS f155: {count} inputs ({captured.size} captured), exact-cost={exact}, ABI prechecks=5, executable probes={probes.length}"
  pure 0
