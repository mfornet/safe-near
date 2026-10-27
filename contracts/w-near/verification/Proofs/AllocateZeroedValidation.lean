import Proofs.AllocateValidation
import Proofs.DeallocateAlignNative
import Proofs.ZeroFillMemory

/-! Independent f153 allocation-and-zero-fill replays from captured f581 input stores.
The direct getter capture of f153 is outside the selected branch; it is not counted as a passing capture. -/
namespace WNear.Proofs.AllocateZeroedValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [153,581]
  for (_,entry) in ((seen.getD 153 #[]).filter (fun e=>e.1=="ft_total_supply")) do
    IO.println s!"SCOPE actual getter f153: size={u32Arg entry.args 1}, alignment={u32Arg entry.args 2}; separate from the replay fixtures"
  let mut checked := 0
  let mut outside := 0
  for (_,entry) in ((seen.getD 581 #[]).filter (fun e=>e.1=="ft_total_supply")) do
    let allocator := u32Arg entry.args 0
    let size := UInt32.ofNat (u32Arg entry.args 1)
    let alignment := u32Arg entry.args 2
    let memory := h.mem entry.store
    let scratch := (UInt32.ofNat (h.stackPointer entry.store)-16).toNat
    let saved := writeI32 memory (scratch+12) (readI32 memory allocator)
    let head := readI32 saved (scratch+12)
    let words := DeallocateAlign.quotient size 4
    if size==0 || alignment != 1 || head==0 || !AllocateValidation.native saved head words then
      outside := outside+1
      continue
    let result := h.call entry.store 153 entry.args
    let split := AllocateValidation.splitMemory saved head words
    let allocated := writeI32 split allocator (readI32 split (scratch+12))
    let pointer := Allocate.splitPointer saved head words
    let expected := ZeroFill.filledMemory allocated pointer 0 size.toNat
    if returnsU32 result != some (Allocate.splitPointer saved head words).toNat then
      throw (IO.userError "f153 direct-fit result differs from the original computed split pointer")
    if (h.mem result.after).pages != expected.pages || (h.mem result.after).max != expected.max then
      throw (IO.userError "f153 direct-fit sequential final memory mismatch")
    if h.global result.after 0 != h.global entry.store 0 then
      throw (IO.userError "f153 failed to restore its original stack pointer")
    let expectedGas := 13*size.toNat+396
    if result.gas != op h expectedGas then
      throw (IO.userError s!"f153 direct-fit expected{expectedGas} root gas units, got {result.gas/(op h 1)}")
    let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[153]! entry.args
      | throw (IO.userError "f153 start failed")
    let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
    let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
    let expectedFuel := 12*size.toNat+325
    if fuel != expectedFuel then throw (IO.userError s!"f153 direct-fit expected{expectedFuel} root steps, got {fuel}")
    match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
    | some (.executionIssue .fuelExhausted) => pure ()
    | _ => throw (IO.userError "f153 direct-fit one-less-fuel mismatch")
    IO.println s!"PASS f153 replay from f581 input size={size.toNat}:{expectedGas} root gas units/{expectedFuel} steps, exact whole memory, SP and pointer"
    checked := checked+1
  if checked != 2 then throw (IO.userError s!"expected two direct-fitting replay fixtures, got {checked}; outside={outside}")
  IO.println s!"SCOPE: {outside} other f581 input stores remain outside the direct-fitting replay branch"
#eval validate
end WNear.Proofs.AllocateZeroedValidation
