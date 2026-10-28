import Proofs.DeallocateInsertCall
import Proofs.DeallocateValidation

/-! Independent original-state replay for the newly closed insertion branch. -/
namespace WNear.Proofs.DeallocateInsertValidation
open Wasm Wasm.Near MeteredLogic WNear.Testing
open DeallocateCore

def native(p:Layout):Bool:=
  decide (p.memory.wf) &&
  decide (p.pointer≠0) &&
  decide (p.length≠0) &&
  decide (p.length.toNat+4<2^32) &&
  decide (p.pointer+4294967288=p.header) &&
  decide (p.pointer+4294967292=p.previousAddress) &&
  decide (p.allocator.toNat+4≤p.memory.byteSize) &&
  decide (p.header.toNat+4≤p.memory.byteSize) &&
  decide (p.pointer.toNat+4≤p.memory.byteSize) &&
  decide (p.header.toNat+8≤(DeallocateListSize.endWord (markedMemory p) p.header).toNat) &&
  decide (p.previousAddress.toNat+4≤(zeroMemory p).byteSize) &&
  decide (Deallocate.previous (zeroMemory p) p.previousAddress=p.previous) &&
  decide (p.previous≠0) &&
  decide (p.previous.toNat+1≤(zeroMemory p).byteSize) &&
  decide (readByteWord (zeroMemory p) p.previous.toNat &&&1≠0) &&
  decide (p.header.toNat+4≤(zeroMemory p).byteSize) &&
  decide (readI32 (zeroMemory p) p.header.toNat &&&4294967292≠0) &&
  decide (readI32 (zeroMemory p) p.header.toNat &&&2≠0)

attribute [local irreducible] readI32 writeI32 readByteWord markedMemory zeroMemory Deallocate.previous DeallocateListSize.endWord

/-- The executable branch filter checks every premise of the proof domain. -/
theorem native_sound(p:Layout)(h:native p=true):DeallocateInsert.Native p:=by
  simp only[native,Bool.and_eq_true,decide_eq_true_eq] at h
  rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0,h1⟩,h2⟩,h3⟩,h4⟩,h5⟩,h6⟩,h7⟩,h8⟩,h9⟩,h10⟩,h11⟩,h12⟩,h13⟩,h14⟩,h15⟩,h16⟩,h17⟩
  exact ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17⟩

private def layout(h:Harness)(m:Memory)(allocator pointer length alignment:UInt32):Layout:=
  let p:=DeallocateValidation.coreLayout h m allocator pointer length alignment
  {p with previous:=Deallocate.previous (zeroMemory p) p.previousAddress}

private def oracle(p:Layout):Memory:=
  let marked:=writeI32 p.memory p.header.toNat (readI32 p.memory p.header.toNat&&&4294967294)
  let zeroed:=writeI32 marked p.pointer.toNat 0
  let linked:=writeI32 zeroed p.pointer.toNat (readI32 p.memory p.allocator.toNat)
  writeI32 linked p.allocator.toNat p.header

private def input(h:Harness)(index:Nat)(entry:Entry):Option Layout:=do
  let m:=h.mem entry.store
  let a:=UInt32.ofNat (u32Arg entry.args 0)
  if index==582 then
    return layout h m a (UInt32.ofNat (u32Arg entry.args 1)) (UInt32.ofNat (u32Arg entry.args 2)) (UInt32.ofNat (u32Arg entry.args 3))
  else if index==68 ||index==747 then
    if a.toNat+8>m.byteSize then none else
      return layout h m 1074896 (readI32 m a.toNat) (readI32 m (a.toNat+4)) 1
  else
    return layout h m 1074896 a (UInt32.ofNat (u32Arg entry.args 1)) (UInt32.ofNat (u32Arg entry.args 2))

private def check(h:Harness)(index units steps:Nat)(entry:Entry):IO Bool:=do
  let some p:=input h index entry | return false
  if !native p then return false
  let result:=h.call entry.store index entry.args
  match result.ending with
  | .returned []=>pure ()
  | _=>throw (IO.userError s!"insert f{index} did not return void")
  let expected:=oracle p
  if (h.mem result.after).pages != expected.pages ||(h.mem result.after).max != expected.max then
    throw (IO.userError s!"insert f{index} whole sequential memory/max mismatch")
  if h.global result.after 0 != h.global entry.store 0 then throw (IO.userError s!"insert f{index} SP mismatch")
  if result.gas != op h units then throw (IO.userError s!"insert f{index} gas got{result.gas/(op h 1)},expected{units}")
  if result.after.host.context.storageUsage != entry.store.host.context.storageUsage ||
      result.after.host.logs != entry.store.host.logs ||result.after.host.returnData != entry.store.host.returnData ||
      result.after.host.returnedPromise != entry.store.host.returnedPromise then
    throw (IO.userError s!"insert f{index} functional host mismatch")
  DeallocateValidation.checkFuel h index steps entry
  return true

def validate:IO Unit:=do
  let protocol←RuntimeConfig.load "../../../near-lean/vm/configs" RuntimeConfig.latestVersion
  let bytes←IO.FS.readBinFile "../contract.wasm"
  let module←orThrow ((Wasm.Binary.decode bytes).mapError Wasm.Binary.DecodeError.message)
  let h←orThrow (Harness.load protocol module internalContext [])
  let seen←captureAll protocol module bytes.size [582,237,311,777,747,68]
  for (index,units,steps) in [(582,141,114),(237,156,120),(311,171,125),(777,188,135),(747,207,148),(68,229,154)] do
    let mut accepted:=0
    let mut getter:=0
    let mut outside:=0
    for (method,entry) in seen.getD index #[] do
      if ←check h index units steps entry then
        accepted:=accepted+1
        if method=="ft_total_supply" then getter:=getter+1
      else outside:=outside+1
    if getter==0 then throw (IO.userError s!"insert f{index} missing219getterdrop")
    let mut generated:=0
    for header in [2000000,h.memSize h.store-512] do
      for length in [1,29,128] do
        for previousFlag in [1,3,255] do
          for oldHead in [0,3000000] do
            let pointer:=header+8
            let previous:=header-32
            let finish:=header+256
            let vector:=header-64
            let m0:=writeI32 (h.mem h.store) 1074896 (UInt32.ofNat oldHead)
            let m1:=writeI32 m0 previous (UInt32.ofNat previousFlag)
            let m2:=writeI32 m1 header ((UInt32.ofNat finish)|||3)
            let m3:=writeI32 m2 (header+4) ((UInt32.ofNat previous)|||1)
            let m4:=writeI32 m3 pointer 0xabcdef
            let m5:=writeI32 (writeI32 m4 vector (UInt32.ofNat pointer)) (vector+4) (UInt32.ofNat length)
            let args:=if index==582 then [.i32 1074896,.i32 (UInt32.ofNat pointer),.i32 (UInt32.ofNat length),.i32 1]
              else if index==68 ||index==747 then [.i32 (UInt32.ofNat vector)]
              else [.i32 (UInt32.ofNat pointer),.i32 (UInt32.ofNat length),.i32 1]
            let entry:Entry:={store:=h.setMem h.store m5,args}
            if !(←check h index units steps entry) then throw (IO.userError s!"generated insert f{index} outsideNative")
            generated:=generated+1
    IO.println s!"PASS insert f{index}: {accepted} captures ({getter} getter219drop,{outside} outsideNative),{generated} generated; exactmemory/max/SP/host/{units}gas/{steps}fuel/one-less"
#eval validate
end WNear.Proofs.DeallocateInsertValidation
