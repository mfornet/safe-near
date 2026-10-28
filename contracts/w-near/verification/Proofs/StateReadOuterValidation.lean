import Proofs.StateReadStorageOuterValidation
import Proofs.StateDecodeBorshReadValidation
import Proofs.DeallocateInsertValidation

/-! Independent actual219 present29-byte replay. Private child oracles are
intentionally duplicated; no guest execution result supplies expected memory. -/
namespace WNear.Proofs.StateReadOuterValidation
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

private def expectedRaw (h : Harness) (index : Nat) (entry : Entry) : Option Memory := do
  let mut memory := h.mem entry.store
  let out := UInt32.ofNat (u32Arg entry.args 0)
  let size := UInt32.ofNat (u32Arg entry.args 1)
  let sp := UInt32.ofNat (h.stackPointer entry.store)
  if size==0 || size.toNat≥2^31 then none else do
    if index==767 then
      if u32Arg entry.args 2  !=  0 then none else pure ()
    else
      if u32Arg entry.args 2  !=  1 then none else pure ()
      if index==770 &&u32Arg entry.args 3  !=  0 then none else pure ()
    if index==767 then
      let wrapperScratch := sp-48
      memory:=writeI32 memory (wrapperScratch.toNat+12) 1
      memory:=writeI32 memory (wrapperScratch.toNat+8) size
      memory:=writeI32 memory (wrapperScratch.toNat+4) 1
      memory:=writeI32 memory wrapperScratch.toNat size
      memory:=writeI64 memory ((sp-32).toNat+24) (readI64 memory wrapperScratch.toNat)
    let allocSP := if index==767 then sp-48 else if index==769 then sp-16 else sp
    let saved := writeI32 memory ((allocSP-16).toNat+12) (readI32 memory 1074896)
    let head := readI32 saved ((allocSP-16).toNat+12)
    let words := DeallocateAlign.quotient size 4
    if head==0 || !AllocateValidation.native saved head words then none else do
      let ptr := Allocate.splitPointer saved head words
      let split := AllocateValidation.splitMemory saved head words
      memory:=writeI32 split 1074896 (readI32 split ((allocSP-16).toNat+12))
      let recordOut := if index==767 then sp-40 else if index==769 then sp-8 else out
      memory:=writeI32 memory (recordOut.toNat+4) size
      memory:=writeI32 memory recordOut.toNat ptr
      if index  !=  770 then
        let copyOut := if index==767 then sp-16 else out
        memory:=writeI32 memory copyOut.toNat (readI32 memory recordOut.toNat)
        memory:=writeI32 memory (copyOut.toNat+4) (readI32 memory (recordOut.toNat+4))
        if index==767 then
          let len := readI32 memory ((sp-32).toNat+20)
          let pointer := readI32 memory ((sp-32).toNat+16)
          memory:=writeI32 memory out.toNat pointer
          memory:=writeI32 memory (out.toNat+4) len
      return memory

private def expectedVector (h : Harness) (entry : Entry) : Option Memory := do
  let sp:=h.stackPointer entry.store
  let out:=UInt32.ofNat (u32Arg entry.args 0)
  let size:=UInt32.ofNat (u32Arg entry.args 1)
  if sp<80 ||out.toNat+12>h.memSize entry.store then none else do
    let child:Entry:={
      store:=h.setGlobal entry.store 0 (.i32 (UInt32.ofNat (sp-16))),
      args:=[.i32 (UInt32.ofNat (sp-8)),.i32 size,.i32 0]}
    let memory ←expectedRaw h 767 child
    let packed:=readI64 memory (sp-8)
    return writeI64 (writeI32 memory (out.toNat+8) 0) out.toNat packed

private def expectedPrefix (h : Harness) (entry : Entry) : Option Memory := do
  let mut m := h.mem entry.store
  let sp := h.stackPointer entry.store
  let r := sp-64
  let out := u32Arg entry.args 0
  let slice := u32Arg entry.args 1
  let ptr := readI32 m slice
  let len := readI32 m (slice+4)
  let n := (readI32 m ptr.toNat).toNat
  if sp<144 ||out<sp ||slice<sp ||out+16>m.byteSize ||slice+8>m.byteSize ||ptr.toNat<sp ||n==0 ||n≥2^31 ||len.toNat<4+n ||ptr.toNat+4+n>m.byteSize then none else do
    m:=writeI32 (writeI32 m (r+44) 4) (r+40) ptr
    m:=writeI32 (writeI32 m (r+36) (len-4)) (r+32) (ptr+4)
    m:=writeI64 m slice (readI64 m (r+32))
    m:=writeI32 (writeI32 m (r+24) 0) (r+28) (UInt32.ofNat n)
    m:=writeI32 (writeI32 m (r+20) (UInt32.ofNat n)) (r+16) (ptr+4)
    let child:Entry:={
      store:=h.setMem (h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))) m
      args:=[.i32 (UInt32.ofNat (r+48)),.i32 (UInt32.ofNat n)]}
    m←expectedVector h child
    let dest:=(readI32 m (r+48)).toNat
    if dest+n>m.byteSize then none else do
      for i in [0:n] do m:=writeByte m (dest+i) (UInt32.ofNat (m.read8 (ptr.toNat+4+i)).toNat)
      m:=writeI32 m (r+56) (UInt32.ofNat n)
      let currentPtr:=readI32 m slice
      let currentLen:=readI32 m (slice+4)
      if currentLen.toNat<n then none else do
        m:=writeI32 (writeI32 m (r+12) (currentLen-UInt32.ofNat n)) (r+8) (currentPtr+UInt32.ofNat n)
        let remainder:=readI64 m (r+8)
        m:=writeI32 m (out+12) (readI32 m (r+56))
        m:=writeI64 m (out+4) (readI64 m (r+48))
        m:=writeI32 m out 0
        return writeI64 m slice remainder

private def expected (h : Harness) (index : Nat) (entry : Entry) : Option Memory := do
  if index==316 then expectedPrefix h entry else do
    let sp:=h.stackPointer entry.store
    let r:=sp-16
    let child:Entry:={
      store:=h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))
      args:=[.i32 (UInt32.ofNat r),.i32 (UInt32.ofNat (u32Arg entry.args 1))]}
    -- The316 caller output is its parent's scratch, above its own entry SP.
    let m←expectedPrefix h child
    let packed:=readI64 m (r+4)
    let high:=readI32 m (r+12)
    let out:=u32Arg entry.args 0
    return writeI32 (writeI32 (writeI64 m (out+4) packed) (out+12) high) out 0


private def expectedScalar (h : Harness) (wide : Bool) (entry : Entry) : Memory := Id.run do
  let original := h.mem entry.store
  let out := UInt32.ofNat (u32Arg entry.args 0)
  let slice := UInt32.ofNat (u32Arg entry.args 1)
  let scratch := UInt32.ofNat (h.stackPointer entry.store)-48
  let width : UInt32 := if wide then 16 else 8
  let takeOut := scratch+(if wide then 8 else 16)
  let wordOut := scratch+(if wide then 16 else 24)
  let dropOut := scratch+(if wide then 0 else 8)
  let len := readI32 original (slice.toNat+4)
  let pointer := readI32 original slice.toNat
  -- Actual362 takes a slice: high length then low pointer.
  let mut memory := writeI32 (writeI32 original (takeOut.toNat+4) width) takeOut.toNat pointer
  let source := readI32 memory takeOut.toNat
  -- Actual694/710 writes the low word first, then reads/writes the high word.
  memory:=writeI64 memory (wordOut.toNat+1) (readI64 memory source.toNat)
  if wide then memory:=writeI64 memory (wordOut+9).toNat (readI64 memory (source+8).toNat)
  memory:=writeByte memory wordOut.toNat 0
  let high := if wide then readI64 memory (scratch+25).toNat else 0
  let low := readI64 memory (scratch.toNat+(if wide then 17 else 25))
  -- Actual361 re-reads the original descriptor on this current memory.
  let remainingPointer := readI32 memory slice.toNat
  let remainingLength := readI32 memory (slice.toNat+4)
  memory:=writeI32 (writeI32 memory (dropOut.toNat+4) (remainingLength-width)) dropOut.toNat (remainingPointer+width)
  let remainder := readI64 memory (scratch.toNat+(if wide then 0 else 8))
  if wide then memory:=writeI64 memory (out+16).toNat high
  memory:=writeI64 memory (out+8).toNat low
  memory:=writeI64 memory slice.toNat remainder
  memory:=writeI32 memory out.toNat 0
  -- len participates in the original guard even if later aliases overwrite it.
  let _ := len
  return memory

private def expectedBorsh (h:Harness) (entry:Entry):Option Memory:=do
  let sp:=h.stackPointer entry.store
  let r:=sp-96
  let out:=u32Arg entry.args 0
  let slice:=u32Arg entry.args 1
  let original:=h.mem entry.store
  let ptr:=(readI32 original slice).toNat
  let len:=(readI32 original (slice+4)).toNat
  let n:=(readI32 original ptr).toNat
  if sp<256 ||out<sp ||out+44>original.byteSize ||slice<sp ||ptr<sp ||len<4+n+24 ||ptr+4+n+24>original.byteSize then none else do
    let child:Entry:={
      store:=h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))
      args:=[.i32 (UInt32.ofNat (r+56)),.i32 (UInt32.ofNat slice)]}
    let mut m←expected h 315 child
    let prefixWord:=readI64 m (r+60)
    m:=writeI32 m (r+24) (readI32 m (r+68))
    m:=writeI64 m (r+16) prefixWord
    let wide:Entry:={child with store:=h.setMem child.store m}
    m:=expectedScalar h true wide
    m:=writeI64 m (r+40) (readI64 m (r+68))
    m:=writeI32 m (r+48) (readI32 m (r+76))
    m:=writeI64 m (r+32) (readI64 m (r+60))
    let high:=readI64 m (r+44)
    let low:=readI64 m (r+36)
    let narrow:Entry:={child with store:=h.setMem child.store m}
    m:=expectedScalar h false narrow
    m:=writeI32 m (r+88) (readI32 m (r+68))
    m:=writeI64 m (r+80) (readI64 m (r+60))
    let length:=readI32 m (r+24)
    m:=writeI32 m (r+8) length
    let packed:=readI64 m (r+16)
    m:=writeI64 m r packed
    let usage:=readI64 m (r+84)
    m:=writeI64 m (out+16) high
    m:=writeI64 m (out+8) low
    m:=writeI64 m (out+24) usage
    m:=writeI64 m (out+32) packed
    m:=writeI32 m (out+40) length
    return writeI32 m out 0

private def forward (memory : Memory) (dest source count : Nat) : Memory := Id.run do
  let mut memory := memory
  for i in [0:count] do memory := writeByte memory (dest+i) (UInt32.ofNat (memory.read8 (source+i)).toNat)
  return memory

private def expectedOuter (h : Harness) (entry : Entry) : Option Memory := do
  let sp := h.stackPointer entry.store
  let r := sp-96
  let out := u32Arg entry.args 0
  if sp<352 ||out+48>h.memSize entry.store then none else do
    let child : Entry := {
      store := h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))
      args := [.i32 (UInt32.ofNat (r+48)), .i32 (UInt32.ofNat (u32Arg entry.args 1))]}
    let mut memory ← expectedBorsh h child
    let cached := readI64 memory (r+52)
    let status := readI32 memory (r+48)
    if status != 0 then none else do
      memory := forward memory (r+12) (r+60) 36
      memory := writeI32 memory (out+8) (UInt32.ofNat (cached.toNat >>> 32))
      memory := forward memory (out+12) (r+12) 36
      return writeI32 memory out 0

private def expectedRead(h:Harness)(entry:Entry):Option Memory:=do
  let sp:=h.stackPointer entry.store
  let r:=sp-144
  let out:=u32Arg entry.args 0
  let pointer:=UInt32.ofNat (u32Arg entry.args 1)
  let length:=UInt32.ofNat (u32Arg entry.args 2)
  if sp<496 ||out<sp ||out+48>h.memSize entry.store then none else do
    let memory:=writeI32 (writeI32 (h.mem entry.store) (r+12) length) (r+8) pointer
    let child:Entry:={
      store:=h.setMem (h.setGlobal entry.store 0 (.i32 (UInt32.ofNat r))) memory
      args:=[.i32 (UInt32.ofNat (r+96)),.i32 (UInt32.ofNat (r+8))]}
    let mut m←expectedOuter h child
    let packed:=readI64 m (r+100)
    let tag:=readI32 m (r+96)
    m:=forward m (r+60) (r+108) 36
    if tag != 0 then none else do
      m:=writeI32 m (r+16) (UInt32.ofNat (packed.toNat >>>32))
      -- Actual OR4 remains explicit, including an unaligned original SP.
      m:=forward m ((r+16)|||4) (r+60) 36
      if readI32 m (r+12) != 0 then none else do
        m:=forward m (out+8) (r+16) 40
        return writeI32 m out 0

private def expected548(memory:Memory)(sp out:UInt32)(contents:List UInt8):Except String (Memory×UInt32):=do
  let r:=sp-32
  let setup:=writeI32 (writeI32 memory (r.toNat+12) 5) (r.toNat+8) 1049788
  let storage:=released (borrowed setup r) r
  let (registered,_,delta)←expected523 storage r (r+16) contents
  let low:=readI64 registered (r+16).toNat
  let lowCopied:=writeI64 registered out.toNat low
  let high:=readI32 lowCopied (r+16+8).toNat
  return (writeI32 lowCopied (out+8).toNat high,delta)

private def expected219(h:Harness)(entry:Entry)(contents:List UInt8):Except String (Memory×UInt32):=do
  let sp:=UInt32.ofNat (h.stackPointer entry.store)
  let r:=sp-96
  let out:=UInt32.ofNat (u32Arg entry.args 0)
  let (loaded,delta)←expected548 (h.mem entry.store) r (r+8) contents
  if readI32 loaded (r+8).toNat==0 then throw "219 missing storage result"
  let high:=writeI32 loaded (r+32).toNat (readI32 loaded (r+16).toNat)
  let copied:=writeI64 high (r.toNat+24) (readI64 high (r.toNat+8))
  let packedHigh:=writeI32 copied (r.toNat+4) (readI32 copied (r.toNat+32))
  let packed:=writeI32 packedHigh r.toNat (readI32 packedHigh (r.toNat+24))
  let child:Entry:={
    store:=h.setMem (h.setGlobal entry.store 0 (.i32 r)) packed
    args:=[.i32 (r+40),.i32 (readI32 packed r.toNat),.i32 (readI32 packed (r.toNat+4))]}
  let some decoded:=expectedRead h child | throw "219 independent161 outside accepted direct allocation geometry"
  if readI32 decoded (r+40).toNat != 0 then throw "219 decode status not accepted"
  let copiedOut:=forward decoded out.toNat (r+48).toNat 40
  let pointer:=readI32 copiedOut (r+24).toNat
  let length:=readI32 copiedOut ((r+24).toNat+4)
  let old:=DeallocateValidation.coreLayout h copiedOut 1074896 pointer length 1
  let drop:DeallocateCore.Layout:={old with previous:=Deallocate.previous (DeallocateCore.zeroMemory old) old.previousAddress}
  if !DeallocateInsertValidation.native drop then throw "219 original computed drop outside insertion domain"
  let marked:=writeI32 copiedOut drop.header.toNat (readI32 copiedOut drop.header.toNat&&&4294967294)
  let zeroed:=writeI32 marked drop.pointer.toNat 0
  let linked:=writeI32 zeroed drop.pointer.toNat (readI32 copiedOut 1074896)
  return (writeI32 linked 1074896 drop.header,delta)

private def check(h:Harness)(entry:Entry):IO Bool:=do
  let memory:=h.mem entry.store
  let sp:=h.stackPointer entry.store
  let out:=u32Arg entry.args 0
  let some key:=getMemOrReg ⟨memory,entry.store.host⟩ 1049788 5 | return false
  let some contents:=entry.store.host.storage key | return false
  if contents.length != 29 ||(readI32 memory 1074896)!=0 ||sp<592 ||sp%16 != 0 ||
      out<sp ||out+40>memory.byteSize ||contents.take 5 != [1,0,0,0,97] then return false
  let entries:=entry.store.host.storageKeys.filterMap fun k=>
    (entry.store.host.storage k).map fun value=>(Near.TrieOverlay.contractKey entry.store.host.context.currentAccountId k,value)
  let initial←orThrow (Near.TrieOverlay.start entries)
  let store:={entry.store with host:={entry.store.host with storageAccounting:=some initial}}
  let entry:Entry:={entry with store}
  let (expected,delta)←orThrow (expected219 h entry contents)
  let original:HostStore NearState:=⟨memory,store.host⟩
  let storageFee:=StorageReadCalls.cost original initial 5 1049788 0 key contents
  let fee:=storageFee+memoryGrowCost h.cfg.wasm delta+store.host.extCosts.cost "base"+
    MeteredHosts.RegisterRead.readCost store.host contents.length
  let result:=h.call store 219 entry.args
  match result.ending with
  | .returned []=>pure ()
  | _=>throw (IO.userError "219 expected normal void result")
  if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
    throw (IO.userError "219 whole sequential memory/max mismatch")
  if h.global result.after 0 != h.global store 0 then throw (IO.userError "219 SP not restored")
  if result.after.host.registers 0 != some contents ||readI32 expected 1074904 != 0 then
    throw (IO.userError "219 register/counter mismatch")
  if result.after.host.context.storageUsage != store.host.context.storageUsage ||result.after.host.logs != store.host.logs ||
      result.after.host.returnData != store.host.returnData ||result.after.host.returnedPromise != store.host.returnedPromise then
    throw (IO.userError "219 functional observation frame mismatch")
  if result.gas != op h 8294+fee then throw (IO.userError s!"219 ordinarygas got{(result.gas-fee)/(op h 1)},expected8294; actual{result.gas},fee{fee}")
  DeallocateValidation.checkFuel h 219 7140 entry
  return true

def validate:IO Unit:=do
  let protocol←RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes←IO.FS.readBinFile "../contract.wasm"
  let module←orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h←orThrow (Harness.load protocol module internalContext [])
  let seen←captureAll protocol module bytes.size [219]
  let mut accepted:=0
  let mut getter:=0
  let mut outside:=0
  let mut fixture:Option Entry:=none
  for (method,entry) in seen.getD 219 #[] do
    if ←check h entry then
      accepted:=accepted+1
      if method=="ft_total_supply" then getter:=getter+1;fixture:=some entry
    else outside:=outside+1
  let some original:=fixture | throw (IO.userError "219 missing accepted getter capture")
  let some key:=getMemOrReg ⟨h.mem original.store,original.store.host⟩ 1049788 5 | throw (IO.userError "219 key")
  let mut generated:=0
  for supply in [0,1,2^64-1,2^64,2^128-1] do
    for usage in [0,1,2^64-1] do
      let contents:List UInt8:=[1,0,0,0,97]++WNear.Borsh.leBytes 16 supply++WNear.Borsh.leBytes 8 usage
      for out in [u32Arg original.args 0,h.stackPointer original.store+1,h.memSize original.store-40] do
        for accountNodes in [false,true] do
          let host:={original.store.host with
            storage:=fun k=>if k==key then some contents else original.store.host.storage k
            storageReadsFromTrie:=accountNodes}
          let entry:Entry:={store:={original.store with host},args:=[.i32 (UInt32.ofNat out)]}
          if !(←check h entry) then throw (IO.userError "generated219 outside accepted domain")
          generated:=generated+1
  IO.println s!"PASS whole219: {accepted} captures ({getter} getter,{outside} outside present29/growth/output domain),{generated} generatedheaders/unalignedoutputs/boundaries/billing; wholememory/max/SP/host/register/counter/8294ordinary+fees/7140fuel/oneless"
#eval validate
end WNear.Proofs.StateReadOuterValidation
