import Proofs.AllocateBranchesValidation
import Proofs.AllocateRetryState
import Proofs.DeallocateAlignNative
import Proofs.ZeroFillMemory

/-! Whole-memory replays of actual686/687 getter captures. The independent
expected sequence includes685 stack writes, growth, zero fill, two record
copies and cached outer output, all computed from the original input store. -/
namespace WNear.Proofs.AllocateVectorValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing

private def growthExpected (memory : Memory) (allocator sp size : UInt32) : Except String (Memory × UInt32 × UInt32) := do
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

private def expected686 (memory : Memory) (sp out size : UInt32) : Except String (Memory × UInt32 × UInt32) := do
  let reserved := sp-32
  let scratch := reserved-16
  let setup := writeI32 (writeI32 memory (scratch.toNat+12) 1) (scratch.toNat+8) size
  let laid := writeI32 (writeI32 setup (scratch.toNat+4) 1) scratch.toNat size
  let copiedLayout := writeI64 laid ((reserved+24).toNat) (readI64 laid scratch.toNat)
  let (allocated,pointer,delta) ← growthExpected copiedLayout 1074896 scratch size
  let zeroed := ZeroFill.filledMemory allocated pointer 0 size.toNat
  let record := writeI32 (writeI32 zeroed (scratch.toNat+12) size) (scratch.toNat+8) pointer
  let lowCopied := writeI32 record ((reserved+8).toNat) (readI32 record (scratch.toNat+8))
  let copied := writeI32 lowCopied ((reserved+8).toNat+4) (readI32 lowCopied (scratch.toNat+12))
  let cachedHigh := readI32 copied (reserved.toNat+12)
  let cachedLow := readI32 copied (reserved.toNat+8)
  return (writeI32 (writeI32 copied out.toNat cachedLow) (out.toNat+4) cachedHigh,pointer,delta)

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [686,687]
  let mut checked := 0
  for target in [686,687] do
    for (_,entry) in ((seen.getD target #[]).filter (fun e=>e.1=="ft_total_supply")) do
      let memory := h.mem entry.store
      let sp := UInt32.ofNat (h.stackPointer entry.store)
      let out := UInt32.ofNat (u32Arg entry.args 0)
      let size := UInt32.ofNat (u32Arg entry.args (if target==687 then 2 else 1))
      let flag := UInt32.ofNat (u32Arg entry.args (if target==687 then 1 else 2))
      if !decide memory.wf || memory.byteSize>2^32 || sp.toNat>memory.byteSize ||
          sp.toNat<(if target==687 then 96 else 64) || size==0 ||size.toNat≥2^31 ||
          out.toNat+(if target==687 then 12 else 8)>memory.byteSize ||1074900>memory.byteSize ||
          sp.toNat>1074896 ||sp.toNat>1057480 ||1057484>memory.byteSize ||readI32 memory 1074896 != 0 then
        throw (IO.userError "vector original Native memory/SP/size/output/head/static separation failed")
      if (target==687 && flag &&& 255 != 0)||(target==686 && flag != 1) then
        throw (IO.userError "vector original selected byte/zeroed flag failed")
      let words := DeallocateAlign.quotient size 4
      let requested := AllocateGrowth.paddedSize (words <<< (2:UInt32)) 1
      let delta := AllocateGrowth.growPages requested
      if memory.size==0 ||delta==0 ||delta.toNat≥65536 ||memory.size+delta.toNat≥65536 ||
          requested.toNat+65536≥2^32 ||80+words.toNat*4>delta.toNat*65536 then
        throw (IO.userError "vector original growth predicates failed")
      let childSP := if target==687 then sp-32 else sp
      let childOut := if target==687 then sp-32+8 else out
      let (inner,pointer,grownDelta) ← orThrow (expected686 memory childSP childOut size)
      if grownDelta != delta then throw (IO.userError "vector independently computed growth delta mismatch")
      let cached := readI64 inner childOut.toNat
      let expected := if target==687 then writeI64 (writeI32 inner (out.toNat+8) size) out.toNat cached else inner
      let result := h.call entry.store target entry.args
      match result.ending with
      | .returned [] => pure ()
      | _ => throw (IO.userError "vector expected normal void result")
      if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
        throw (IO.userError s!"actual{target} full sequential memory mismatch")
      if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError "vector original SP not restored")
      if readI32 expected out.toNat != pointer ||readI32 expected (out.toNat+4) != size then
        throw (IO.userError "vector canonical pointer/size mismatch")
      if target==687 && readI32 expected (out.toNat+8) != size then throw (IO.userError "vector length mismatch")
      let units := 13*size.toNat+(if target==687 then 910 else 870)
      let steps := 12*size.toNat+(if target==687 then 720 else 688)
      let fee := memoryGrowCost h.cfg.wasm delta
      if result.gas != op h units+fee then throw (IO.userError s!"actual{target} gas got{result.gas},expected{op h units+fee}")
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[target]! entry.args
        | throw (IO.userError "vector start failed")
      let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
      let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
      if fuel != steps then throw (IO.userError s!"actual{target} fuel got{fuel},expected{steps}")
      match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ => throw (IO.userError "vector one-less-fuel mismatch")
      checked:=checked+1
      IO.println s!"PASS actual getter{target} size{size.toNat}: {units} ordinary root units +fee{fee}/{steps} steps; full memory/max/SP/void/record"
  if checked != 2 then throw (IO.userError s!"unexpected vector capture count{checked}")
#eval validate
end WNear.Proofs.AllocateVectorValidation
