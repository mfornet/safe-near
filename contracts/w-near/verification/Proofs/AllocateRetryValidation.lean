import Proofs.AllocateBranchesValidation
import Proofs.AllocateRetryState
import Proofs.DeallocateAlignNative
import Proofs.ZeroFillMemory

/-! Independent whole-memory replay of actual getter581 and153 size29 captures.
The expected state follows original scratch save, growth, sequential relinking,
flags-two split and optional memset; no expected execution outcome is reused. -/
namespace WNear.Proofs.AllocateRetryValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def expected (memory : Memory) (allocator sp size : UInt32) : Except String (Memory × UInt32 × UInt32) := do
  let scratch := sp-16
  let saved := writeI32 memory (scratch.toNat+12) (readI32 memory allocator.toNat)
  let words := DeallocateAlign.quotient size 4
  let requested := AllocateGrowth.paddedSize (words <<< (2:UInt32)) 1
  let delta := AllocateGrowth.growPages requested
  let some grown := saved.grow delta.toNat | throw "expected original growth failed"
  let header := AllocateGrowth.pageBytes (UInt32.ofNat saved.size)
  let blockBytes := AllocateGrowth.pageBytes delta
  let fresh := AllocateGrowth.freshMemory grown header blockBytes
  let recorded := AllocateGrowth.recordMemory fresh scratch header
  let oldLinked := writeI32 recorded (header.toNat+8) (readI32 recorded (scratch.toNat+12))
  let relinked := writeI32 oldLinked (scratch.toNat+12) header
  let split := AllocateBranchesValidation.flaggedMemory relinked header words
  let allocated := writeI32 split allocator.toNat (readI32 split (scratch.toNat+12))
  return (allocated,Allocate.splitPointer relinked header words,delta)

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [153,581]
  let mut checked581 := 0
  let mut checked153 := 0
  let mut outside := 0
  for target in [581,153] do
    for (_,entry) in ((seen.getD target #[]).filter (fun e=>e.1=="ft_total_supply")) do
      let allocator := UInt32.ofNat (u32Arg entry.args 0)
      let size := UInt32.ofNat (u32Arg entry.args 1)
      let memory := h.mem entry.store
      let sp := UInt32.ofNat (h.stackPointer entry.store)
      if size != 29 || u32Arg entry.args 2 != 1 then
        outside := outside+1
        continue
      if !decide memory.wf || memory.byteSize>2^32 || sp.toNat<16 || sp.toNat>memory.byteSize ||
          allocator.toNat+4>memory.byteSize then throw (IO.userError "retry original native memory/stack bounds failed")
      let scratch := (sp-16).toNat
      if readI32 memory allocator.toNat != 0 || size.toNat+4≥2^32 then
        throw (IO.userError "retry original empty head/rounding predicate failed")
      if !(scratch+16≤1057464+16 || 1057464+20≤scratch) || 1057464+20>memory.byteSize then
        throw (IO.userError "retry original scratch/callback-word separation failed")
      let (allocated,pointer,delta) ← orThrow (expected memory allocator sp size)
      let words := DeallocateAlign.quotient size 4
      let requested := AllocateGrowth.paddedSize (words <<< (2:UInt32)) 1
      if memory.size==0 || memory.size≥65536 || memory.size+delta.toNat≥65536 ||
          words==0 || delta==0 || delta.toNat≥65536 || requested.toNat+65536≥2^32 ||
          80+words.toNat*4>delta.toNat*65536 then
        throw (IO.userError "retry original growth/page/word/room Native predicate failed")
      let wanted := if target==153 then ZeroFill.filledMemory allocated pointer 0 size.toNat else allocated
      let result := h.call entry.store target entry.args
      if returnsU32 result != some pointer.toNat then throw (IO.userError s!"actual{target} retry pointer mismatch")
      if (h.mem result.after).pages != wanted.pages || (h.mem result.after).max != wanted.max then
        throw (IO.userError s!"actual{target} retry exact whole-memory mismatch")
      if h.global result.after 0 != h.global entry.store 0 then
        throw (IO.userError s!"actual{target} retry SP mismatch")
      let units := if target==153 then 641+13*size.toNat else 602
      let fee := memoryGrowCost h.cfg.wasm delta
      if result.gas != op h units+fee then
        throw (IO.userError s!"actual{target} retry gas mismatch got{result.gas},expected{op h units+fee}; ordinary={units},fee={fee}")
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[target]! entry.args
        | throw (IO.userError s!"actual{target} retry start failed")
      let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
      let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
      let steps := if target==153 then 517+12*size.toNat else 490
      if fuel != steps then throw (IO.userError s!"actual{target} retry fuel got{fuel},expected{steps}")
      match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ => throw (IO.userError s!"actual{target} retry one-less-fuel mismatch")
      if target==153 then checked153:=checked153+1 else checked581:=checked581+1
      IO.println s!"PASS actual getter{target} size29 growth/retry: {units} ordinary root units + linear fee {fee}; {steps} steps; exact entire memory/max/SP/pointer"
  if (checked581,checked153)!=(1,1) then throw (IO.userError s!"unexpected retry capture counts{checked581}/{checked153},outside{outside}")
  IO.println s!"SCOPE: {outside} other actual captures excluded; no synthetic1/24-byte replay counted"
#eval validate
end WNear.Proofs.AllocateRetryValidation
