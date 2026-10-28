import Proofs.AllocateVectorValidation
import Proofs.StateReadRegister

/-! Independent full-memory replay of the actual getter f523 register-read capture. -/
namespace WNear.Proofs.StateReadRegisterOuterValidation
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

private def borrowed (memory : Memory) (sp : UInt32) : Memory :=
  let b := sp-16
  let counted := writeI32 memory 1074904 (ValueReturnAcquire.nextCount memory 1074904)
  let record := ValueReturnAcquire.recordMemory counted b 1074904
  let high := writeI32 record (b.toNat+12) (readI32 record (b.toNat+4))
  writeI32 high (b.toNat+8) (readI32 high b.toNat)

private def released (memory : Memory) (sp : UInt32) : Memory :=
  let counter := readI32 memory (((sp-16+8)|||4).toNat)
  writeI32 memory counter.toNat (readI32 memory counter.toNat+4294967295)

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [523]
  let mut checked := 0
  for (_,entry) in ((seen.getD 523 #[]).filter (fun e=>e.1=="ft_total_supply")) do
    let memory := h.mem entry.store
    let sp := UInt32.ofNat (h.stackPointer entry.store)
    let scratch := sp-48
    let out := UInt32.ofNat (u32Arg entry.args 0)
    let some (Value.i64 register) := entry.args[1]? | throw (IO.userError "register ID missing")
    let some contents := entry.store.host.registers register.toNat | throw (IO.userError "expected present register")
    let size := UInt32.ofNat contents.length
    let vtable := readI32 memory 1074912
    if !decide memory.wf ||memory.byteSize>2^32 ||sp.toNat>memory.byteSize ||out.toNat+12>memory.byteSize ||
        sp.toNat>1074896 ||sp.toNat>1057480 ||sp.toNat>1055020 ||1074916>memory.byteSize ||
        readI32 memory 1074908==0 ||sp.toNat>vtable.toNat ||vtable.toNat+20>1074896 ||vtable.toNat+20>memory.byteSize then
      throw (IO.userError "original register wrapper memory/output/static/vtable bounds failed")
    if contents.length==0 ||contents.length≥2^31 ||sp.toNat<144 ||sp.toNat%16 != 0 ||
        readI32 memory 1074904 != 0 ||readI32 memory 1074900 != 1 ||readI32 memory 1074896 != 0 then
      throw (IO.userError "original register wrapper selected-domain predicates failed")
    let saved := writeI64 memory (scratch.toNat+24) register
    let input := writeI64 saved ((scratch-16).toNat+8) register
    let lengthBorrowed := borrowed input (scratch-16)
    let lengthReleased := released lengthBorrowed (scratch-16)
    let looked := writeI64 (writeI64 lengthReleased ((scratch+8).toNat+8) (UInt64.ofNat contents.length))
      (scratch+8).toNat 1
    let (vector,pointer,delta) ← orThrow (expected686 looked (scratch-32) (scratch-32+8) size)
    let words := DeallocateAlign.quotient size 4
    if memory.size==0 ||delta==0 ||delta.toNat≥65536 ||memory.size+delta.toNat≥65536 ||
        80+words.toNat*4>delta.toNat*65536 then
      throw (IO.userError "register wrapper original allocation growth/room predicates failed")
    let cached := readI64 vector (scratch-32+8).toNat
    let allocated := writeI64 (writeI32 vector ((scratch+32).toNat+8) size) (scratch+32).toNat cached
    let readBorrowed := borrowed allocated scratch
    let actualRegister := readI64 readBorrowed (scratch.toNat+24)
    let actualPointer := readI32 readBorrowed (scratch.toNat+32)
    if actualRegister != register ||actualPointer != pointer then throw (IO.userError "independent pre-read words mismatch")
    let copied := readBorrowed.writeList actualPointer.toNat contents
    let readReleased := released copied scratch
    let high := readI32 readReleased ((scratch+40).toNat)
    let highCopied := writeI32 readReleased ((out+8).toNat) high
    let low := readI64 highCopied ((scratch+32).toNat)
    let expected := writeI64 highCopied out.toNat low
    let result := h.call entry.store 523 entry.args
    match result.ending with
    | .returned [] => pure ()
    | _ => throw (IO.userError "register wrapper expected normal void result")
    if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
      throw (IO.userError "register wrapper independent whole-memory mismatch")
    if h.global result.after 0  != h.global entry.store 0 then throw (IO.userError "register wrapper SP not restored")
    if readI32 expected out.toNat != pointer ||readI32 expected (out.toNat+4) != size ||
        readI32 expected (out.toNat+8) != size ||readI32 expected 1074904 != 0 then
      throw (IO.userError "register wrapper final record/counter mismatch")
    let units := 13*contents.length+1510
    let fee := memoryGrowCost h.cfg.wasm delta+entry.store.host.extCosts.cost "base"+
      MeteredHosts.RegisterRead.readCost entry.store.host contents.length
    if result.gas != op h units+fee then throw (IO.userError s!"register wrapper gas got{result.gas},expected{op h units+fee}")
    let some initial := Exec.startWasm entry.store execLimits h.inst.funcAddrs[523]! entry.args
      | throw (IO.userError "register wrapper start failed")
    let active := (chargeWasm (.next initial) (entryCost h.cfg.wasm (.next initial))).1
    let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
    let steps := 12*contents.length+1126
    if fuel != steps then throw (IO.userError s!"register wrapper fuel got{fuel},expected{steps}")
    match (runInitialized h.cfg.wasm (fuel-1) (.next initial)).2 with
    | some (.executionIssue .fuelExhausted) => pure ()
    | _ => throw (IO.userError "register wrapper one-less-fuel mismatch")
    checked:=checked+1
    IO.println s!"PASS actual getter523 size{contents.length}: {units} ordinary root units+fee{fee}/{steps} steps; independent full memory/max/SP/void/record/counter"
  if checked != 1 then throw (IO.userError s!"unexpected register wrapper capture count{checked}")
#eval validate
end WNear.Proofs.StateReadRegisterOuterValidation
