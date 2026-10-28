import Proofs.AllocateVectorValidation
import Proofs.StateReadRegister
import NearVM.MeteredStorageReadRules

/-! Independent actual getter548 replay, augmented with fresh canonical storage accounting in both node-billing modes. -/
namespace WNear.Proofs.StateReadStorageOuterValidation
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

private def expected523 (memory : Memory) (sp out : UInt32) (contents : List UInt8) :
    Except String (Memory × UInt32 × UInt32) := do
  let scratch := sp-48
  let size := UInt32.ofNat contents.length
  let saved := writeI64 memory (scratch.toNat+24) 0
  let input := writeI64 saved ((scratch-16).toNat+8) 0
  let lengthReleased := released (borrowed input (scratch-16)) (scratch-16)
  let looked := writeI64 (writeI64 lengthReleased ((scratch+8).toNat+8) (UInt64.ofNat contents.length)) (scratch+8).toNat 1
  let (vector,pointer,delta) ← expected686 looked (scratch-32) (scratch-32+8) size
  let cached := readI64 vector (scratch-32+8).toNat
  let allocated := writeI64 (writeI32 vector ((scratch+32).toNat+8) size) (scratch+32).toNat cached
  let readBorrowed := borrowed allocated scratch
  let actualRegister := readI64 readBorrowed (scratch.toNat+24)
  let actualPointer := readI32 readBorrowed (scratch.toNat+32)
  if actualRegister != 0 ||actualPointer != pointer then throw "independent pre-read words mismatch"
  let readReleased := released (readBorrowed.writeList actualPointer.toNat contents) scratch
  let highCopied := writeI32 readReleased ((out+8).toNat) (readI32 readReleased ((scratch+40).toNat))
  return (writeI64 highCopied out.toNat (readI64 highCopied ((scratch+32).toNat)),pointer,delta)

def validate : IO Unit := do
  let protocol ← RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes ← IO.FS.readBinFile "../contract.wasm"
  let module ← orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h ← orThrow (Harness.load protocol module internalContext [])
  let seen ← captureAll protocol module bytes.size [548]
  let mut checked := 0
  for (_,captured) in ((seen.getD 548 #[]).filter (fun e=>e.1=="ft_total_supply")) do
    for accountNodes in [false,true] do
      let entries := captured.store.host.storageKeys.filterMap fun key =>
        (captured.store.host.storage key).map fun value =>
          (Near.TrieOverlay.contractKey captured.store.host.context.currentAccountId key,value)
      let initial ← orThrow (Near.TrieOverlay.start entries)
      let store := {captured.store with host:={captured.store.host with storageAccounting:=some initial,storageReadsFromTrie:=accountNodes}}
      let memory := h.mem store
      let sp := UInt32.ofNat (h.stackPointer store)
      let scratch := sp-32
      let out := UInt32.ofNat (u32Arg captured.args 0)
      let keyPtr := UInt32.ofNat (u32Arg captured.args 1)
      let keyLen := UInt32.ofNat (u32Arg captured.args 2)
      let some key := getMemOrReg ⟨memory,store.host⟩ (UInt64.ofNat keyPtr.toNat) (UInt64.ofNat keyLen.toNat)
        | throw (IO.userError "original548 key span invalid")
      let some contents := store.host.storage key | throw (IO.userError "expected actual present storage value")
      let size := UInt32.ofNat contents.length
      let vtable := readI32 memory 1074912
      if !decide memory.wf ||memory.byteSize>2^32 ||sp.toNat<176 ||sp.toNat%16 != 0 ||sp.toNat>memory.byteSize ||
          out.toNat+12>memory.byteSize ||sp.toNat>1055020 ||sp.toNat>1074900 ||
          sp.toNat>vtable.toNat ||vtable.toNat+192>memory.byteSize ||vtable.toNat+192>1074896 ||
          sp.toNat>keyPtr.toNat ||keyPtr.toNat+keyLen.toNat>memory.byteSize ||
          !(keyPtr.toNat+keyLen.toNat≤1074904 ||1074908≤keyPtr.toNat) then
        throw (IO.userError "548 original native stack/key/static/output domain failed")
      if contents.isEmpty ||contents.length≥2^31 ||readI32 memory 1074896 != 0 ||
          readI32 memory 1074904 != 0 ||readI32 memory 1074900 != 1 ||readI32 memory 1074908==0 then
        throw (IO.userError "548 original present/growth/interface domain failed")
      let setup := writeI32 (writeI32 memory (scratch.toNat+12) keyLen) (scratch.toNat+8) keyPtr
      let storageBorrowed := borrowed setup scratch
      let storageReleased := released storageBorrowed scratch
      let (registered,pointer,delta) ← orThrow (expected523 storageReleased scratch (scratch+16) contents)
      let words := DeallocateAlign.quotient size 4
      if memory.size==0 ||delta==0 ||delta.toNat≥65536 ||memory.size+delta.toNat≥65536 ||
          80+words.toNat*4>delta.toNat*65536 then
        throw (IO.userError "548 original growth capacity/room domain failed")
      let low := readI64 registered (scratch+16).toNat
      let lowCopied := writeI64 registered out.toNat low
      let high := readI32 lowCopied ((scratch+16+8).toNat)
      let expected := writeI32 lowCopied (out+8).toNat high
      let original : HostStore NearState := ⟨memory,store.host⟩
      let storageFee := StorageReadCalls.cost original initial (UInt64.ofNat keyLen.toNat) (UInt64.ofNat keyPtr.toNat) 0 key contents
      let plan := MeteredHosts.StorageRead.readPlan initial
        (Near.TrieOverlay.contractKey store.host.context.currentAccountId key) accountNodes
      if withinLimit store.host.config.maxStorageKeyLen key.length != true ||
          withinLimit store.host.config.maxRegisterLen contents.length != true ||
          recordedStorageError store.host plan.looked != none then
        throw (IO.userError "548 original canonical key/register/proof resource domain failed")
      if getMemOrReg ⟨storageBorrowed,store.host⟩ (UInt64.ofNat keyPtr.toNat) (UInt64.ofNat keyLen.toNat) != some key then
        throw (IO.userError "548 independent setup/borrow altered original key")
      let result := h.call store 548 captured.args
      match result.ending with
      | .returned [] => pure ()
      | _ => throw (IO.userError "548 expected normal void result")
      if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
        throw (IO.userError "548 independent whole-memory mismatch")
      if h.global result.after 0 != h.global store 0 then throw (IO.userError "548 SP not restored")
      if result.after.host.registers 0 != some contents ||readI32 expected out.toNat != pointer ||
          readI32 expected (out.toNat+4) != size ||readI32 expected (out.toNat+8) != size ||readI32 expected 1074904 != 0 then
        throw (IO.userError "548 final register/record/counter mismatch")
      if result.after.host.context.storageUsage != store.host.context.storageUsage ||result.after.host.logs != store.host.logs ||
          result.after.host.returnData != store.host.returnData ||result.after.host.returnedPromise != store.host.returnedPromise then
        throw (IO.userError "548 functional observation frame mismatch")
      let units := 13*contents.length+1847
      let fee := storageFee+memoryGrowCost h.cfg.wasm delta+store.host.extCosts.cost "base"+
        MeteredHosts.RegisterRead.readCost store.host contents.length
      if result.gas != op h units+fee then throw (IO.userError s!"548 gas got{result.gas},expected{op h units+fee}")
      let some started := Exec.startWasm store execLimits h.inst.funcAddrs[548]! captured.args
        | throw (IO.userError "548 start failed")
      let active := (chargeWasm (.next started) (entryCost h.cfg.wasm (.next started))).1
      let fuel := AllocateValidation.fuelUsed h.cfg.wasm active
      let steps := 12*contents.length+1357
      if fuel != steps then throw (IO.userError s!"548 fuel got{fuel},expected{steps}")
      match (runInitialized h.cfg.wasm (fuel-1) (.next started)).2 with
      | some (.executionIssue .fuelExhausted) => pure ()
      | _ => throw (IO.userError "548 one-less-fuel mismatch")
      checked:=checked+1
      IO.println s!"PASS actual getter548 canonical replay nodeBilling={accountNodes} valueBytes={contents.length}: {units} ordinary root units+fee{fee}/{steps} steps; whole memory/max/SP/void/register/record/counter"
  if checked != 2 then throw (IO.userError s!"unexpected548 getter replay count{checked}")
#eval validate
end WNear.Proofs.StateReadStorageOuterValidation
