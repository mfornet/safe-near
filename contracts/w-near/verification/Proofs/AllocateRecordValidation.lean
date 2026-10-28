import Proofs.AllocateBranchesValidation
import Proofs.AllocateRetryState
import Proofs.DeallocateAlignNative
import Proofs.ZeroFillMemory

/-! Independent deployed236/310/689/690 getter captures. Expected memories follow
original input reads and sequential stores, not observed callee outcomes. -/
namespace WNear.Proofs.AllocateRecordValidation
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

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [236,310,689,690]
  let mut raw := 0
  let mut skipped := 0
  let mut records := 0
  for target in [236,310,689,690] do
    for (_,entry) in ((seen.getD target #[]).filter (fun e=>e.1=="ft_total_supply")) do
      let memory := h.mem entry.store
      let sp := UInt32.ofNat (h.stackPointer entry.store)
      let isRecord := target==689 || target==690
      let size := UInt32.ofNat (u32Arg entry.args (if isRecord then 1 else 0))
      let alignment := u32Arg entry.args (if isRecord then 2 else 1)
      let out := UInt32.ofNat (u32Arg entry.args 0)
      if alignment != 1 || size==0 || !decide memory.wf || memory.byteSize>2^32 ||
          sp.toNat<32 || sp.toNat>memory.byteSize || size.toNat+4≥2^32 ||1074900>memory.byteSize then
        throw (IO.userError "record/raw original width/stack/alignment/rounding predicates failed")
      let innerSp := if target==690 then sp-16 else sp
      let scratch := innerSp-16
      let words := DeallocateAlign.quotient size 4
      let saved := writeI32 memory (scratch.toNat+12) (readI32 memory 1074896)
      let head := readI32 saved (scratch.toNat+12)
      let hop := head != 0 && words.toNat*4>(Allocate.endWord saved head).toNat-head.toNat-8
      let (wanted,pointer,fee,units,steps) ← if isRecord then do
        if size != 29 || head != 0 || out.toNat+8>memory.byteSize ||
            (target==689 && u32Arg entry.args 3 != 1) then
          throw (IO.userError "unexpected actual689/690 original branch")
        if !((scratch.toNat+16≤1057464+16)||(1057464+20≤scratch.toNat)) ||1057484>memory.byteSize then
          throw (IO.userError "record original scratch/vtable separation failed")
        let (allocated,pointer,delta) ← orThrow (growthExpected memory 1074896 innerSp size)
        if memory.size==0 ||memory.size+delta.toNat≥65536 ||delta==0 ||
            80+words.toNat*4>delta.toNat*65536 then
          throw (IO.userError "record original growth predicates failed")
        let filled := ZeroFill.filledMemory allocated pointer 0 size.toNat
        let recordOut := if target==690 then (sp-16).toNat+8 else out.toNat
        let written := writeI32 (writeI32 filled (recordOut+4) size) recordOut pointer
        let lowCopied := writeI32 written out.toNat (readI32 written ((sp-16).toNat+8))
        let copied := writeI32 lowCopied (out.toNat+4) (readI32 lowCopied ((sp-16).toNat+12))
        pure (if target==690 then copied else written,pointer,memoryGrowCost h.cfg.wasm delta,
          13*size.toNat+(if target==690 then 731 else 697),12*size.toNat+(if target==690 then 573 else 548))
      else do
        let candidate := if hop then readI32 saved (head.toNat+8) else head
        let searched := if hop then writeI32 saved (scratch.toNat+12) candidate else saved
        if !AllocateValidation.native saved candidate words then
          throw (IO.userError "raw original direct/one-hop split predicates failed")
        if head==0 || head.toNat+12>saved.byteSize || candidate &&& 1 != 0 ||
            head.toNat+8>(Allocate.endWord saved head).toNat ||1057484>saved.byteSize then
          throw (IO.userError "raw original first-head/candidate/vtable predicates failed")
        if hop && (!((scratch.toNat+16≤candidate.toNat)||(candidate.toNat+12≤scratch.toNat+12)) ||
            !((scratch.toNat+16≤1057480)||(1057484≤scratch.toNat+12))) then
          throw (IO.userError "raw original root/candidate separation failed")
        let split := AllocateValidation.splitMemory searched candidate words
        let result := Allocate.splitPointer searched candidate words
        let final := writeI32 split 1074896 (readI32 split (scratch.toNat+12))
        let gas := (if hop then 441 else 370)+(if target==310 then 16 else 0)
        let fuel := (if hop then 362 else 303)+(if target==310 then 6 else 0)
        pure (final,result,0,gas,fuel)
      let result := h.call entry.store target entry.args
      if isRecord then
        match result.ending with
        | .returned [] => pure ()
        | _ => throw (IO.userError "record result must be void")
      else if returnsU32 result != some pointer.toNat then throw (IO.userError "raw pointer mismatch")
      if (h.mem result.after).pages != wanted.pages ||(h.mem result.after).max != wanted.max then
        throw (IO.userError s!"actual{target} entire sequential memory mismatch")
      if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError "original SP not restored")
      if result.gas != op h units+fee then throw (IO.userError s!"actual{target} gas got{result.gas},expected{op h units+fee}")
      let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[target]! entry.args
        | throw (IO.userError "record/raw start failed")
      let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
      let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
      if fuel != steps then throw (IO.userError s!"actual{target} fuel got{fuel},expected{steps}")
      match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ =>throw (IO.userError "record/raw one-less-fuel mismatch")
      if isRecord then records:=records+1 else if hop then skipped:=skipped+1 else raw:=raw+1
      IO.println s!"PASS actual getter{target} size{size.toNat}: {units} ordinary root units +fee{fee}/{steps} steps; entire memory/max/SP/result"
  if (raw,skipped,records) != (4,2,2) then throw (IO.userError s!"unexpected capture counts{raw}/{skipped}/{records}")
#eval validate
end WNear.Proofs.AllocateRecordValidation
