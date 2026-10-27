import Proofs.AllocateValidation
import Proofs.AllocateGrowthResources

/-! Independent replay of the actual getter's successful f577 capture. -/
namespace WNear.Proofs.AllocateGrowthValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [577]
  let mut checked := 0
  for (_,entry) in ((seen.getD 577 #[]).filter (fun e=>e.1=="ft_total_supply")) do
    let memory := h.mem entry.store
    let record := UInt32.ofNat (u32Arg entry.args 0)
    let words := UInt32.ofNat (u32Arg entry.args 2)
    let alignment := UInt32.ofNat (u32Arg entry.args 3)
    let units := words <<< (2 : UInt32)
    let requested := AllocateGrowth.paddedSize units alignment
    let delta := AllocateGrowth.growPages requested
    let some grown := memory.grow delta.toNat
      | throw (IO.userError "getter f577 capture does not grow successfully")
    let header := AllocateGrowth.pageBytes (UInt32.ofNat memory.size)
    let blockBytes := AllocateGrowth.pageBytes delta
    let fresh := AllocateGrowth.freshMemory grown header blockBytes
    let expected := AllocateGrowth.recordMemory fresh record header
    let result := h.call entry.store 577 entry.args
    if ended result != none then throw (IO.userError "getter f577 failed to return normally")
    if (h.mem result.after).pages != expected.pages || (h.mem result.after).max != expected.max then
      throw (IO.userError "getter f577 exact sequential final memory mismatch")
    if h.global result.after 0 != h.global entry.store 0 then
      throw (IO.userError "getter f577 changed the stack pointer")
    let expectedGas := op h 177 + memoryGrowCost h.cfg.wasm delta
    if result.gas != expectedGas then
      throw (IO.userError s!"getter f577 exact linear gas mismatch: got {result.gas}, expected {expectedGas}")
    let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[577]! entry.args
      | throw (IO.userError "f577 start failed")
    let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
    let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
    if fuel != 136 then throw (IO.userError s!"getter f577 expected136 root steps, got {fuel}")
    match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
    | some (.executionIssue .fuelExhausted) => pure ()
    | _ => throw (IO.userError "getter f577 one-less-fuel mismatch")
    IO.println s!"PASS actual getter f577: pages={memory.size}+{delta.toNat},177 root opcode units+exact linear fee/{fuel} steps, exact whole memory/SP"
    checked := checked+1
  if checked != 1 then throw (IO.userError s!"expected one successful getter growth capture, got {checked}")
#eval validate
end WNear.Proofs.AllocateGrowthValidation
