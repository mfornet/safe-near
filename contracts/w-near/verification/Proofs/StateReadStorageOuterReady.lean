import Proofs.StateReadStorageOuterCode
import Proofs.StateReadStorageOuterSetupFrame

/-! Original548 data and code derive every actual459 guest-ready premise. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 StateDispatchLength.lowMemory

theorem Code.storage_ready (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (callers : List CallFrame) (p : Layout) (extra : Nat)
    (hn : Native p) (ha : p.allocator=1074896) (hcode : Code s frame.inst p extra)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global548)
    (h0 : frame.locals[0]?=some (.i32 1055020)) (h1 : frame.locals[1]?=some (.i32 (scratch p+8)))
    (hs : 5≤frame.locals.size) (hd : callers.length+3<limits.maxCallDepth) :
    StateDispatchStorage.Ready (storageArguments s cfg.regularOpCost p) limits frame callers (storageLayout p) extra := by
  have prep := setup_spec p hn
  change (storageLayout p).memory.wf ∧ (storageLayout p).memory.byteSize=p.memory.byteSize ∧ (storageLayout p).memory.max=p.memory.max at prep
  have shapes := borrow_shapes p hn
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have static := hn.staticAbove
  have cell := hn.register.threadBound
  have bs : (StateDispatchLength.scratch (storageLayout p)).toNat=p.sp548.toNat-48 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  have inputNat : (storageLayout p).input.toNat=p.sp548.toNat-24 := by
    change (scratch p+8).toNat=p.sp548.toNat-24
    rw [UInt32.toNat_add,nums.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have upper := p.sp548.toNat_lt
    omega
  have counterZero : readI32 (storageLayout p).memory 1074904=0 :=
    (setup_word p hn 1074904 (by omega)).trans hn.register.counterZero
  have count : Numeric.irelop32 .ge_s (ValueReturnAcquire.nextCount (storageLayout p).memory 1074904) 1=true := by
    simp only [ValueReturnAcquire.nextCount,show (1074904:UInt32).toNat=1074904 by decide,counterZero]
    decide
  have interfaceRead : readI32 (storageLayout p).memory 1055020=p.lookupElement :=
    (setup_word p hn 1055020 hn.staticAbove).trans hn.register.interfaceRead
  have threadRead : readI32 (storageLayout p).memory 1074900=1 :=
    (setup_word p hn 1074900 (by omega)).trans hn.register.threadStatus
  have highBound : (StateDispatchLength.scratch (storageLayout p)).toNat+16≤
      (StateDispatchLength.acquiredMemory (storageLayout p)).byteSize := by
    rw [shapes.2.1,bs];omega
  have lowBound : (StateDispatchLength.scratch (storageLayout p)).toNat+12≤
      (StateDispatchLength.highMemory (storageLayout p)).byteSize := by
    rw [shapes.2.2.2.1,bs];omega
  have selectBound : (StateDispatchLength.borrowed (storageLayout p)).toNat+4≤
      (StateDispatchLength.lowMemory (storageLayout p)).byteSize := by
    rw [borrowed_eq p hn,shapes.2.2.2.2.2]
    change 1074908+4≤p.memory.byteSize
    omega
  have selectedNonzero : StateDispatchLength.selected (storageLayout p)≠0 := by
    rw [selected_eq p hn];decide
  have selectedBound : (StateDispatchLength.selected (storageLayout p)).toNat+8≤
      (StateDispatchLength.lowMemory (storageLayout p)).byteSize := by
    rw [selected_eq p hn,shapes.2.2.2.2.2]
    change 1074908+8≤p.memory.byteSize
    omega
  have inputBound : (storageLayout p).input.toNat+8≤
      (StateDispatchLength.lowMemory (storageLayout p)).byteSize := by
    rw [inputNat,shapes.2.2.2.2.2];omega
  have vtableBound : (StateDispatchLength.vtable (storageLayout p)).toNat+192≤
      (StateDispatchLength.lowMemory (storageLayout p)).byteSize := by
    change (StateDispatchStorage.vtable (storageLayout p)).toNat+192≤_
    rw [storage_vtable_eq p hn,shapes.2.2.2.2.2];exact hn.vtableBound
  have releaseBound : ((StateDispatchLength.scratch (storageLayout p)+8)|||4).toNat+4≤
      (StateDispatchLength.lowMemory (storageLayout p)).byteSize := by
    rw [release_address p hn,bs,shapes.2.2.2.2.2];omega
  have counterBound : (StateDispatchLength.counter (storageLayout p)).toNat+4≤
      (StateDispatchLength.lowMemory (storageLayout p)).byteSize := by
    rw [counter_eq p hn,shapes.2.2.2.2.2]
    change 1074904+4≤p.memory.byteSize
    omega
  have fields := storageArguments_fields s cfg.regularOpCost p
  have code := (hcode.storageCode s frame.inst p extra hn ha).transport s (storageArguments s cfg.regularOpCost p)
    (storageLayout p) frame.inst extra fields.1 fields.2.1 fields.2.2
  have memory := storageArguments_memory s cfg.regularOpCost p hm
  have global := storageArguments_global s cfg.regularOpCost p hg
  have interfaceBound : (storageLayout p).interface.toNat+4≤(storageLayout p).memory.byteSize := by
    change 1055020+4≤(storageLayout p).memory.byteSize
    rw [prep.2.1];exact hn.register.interfaceBound
  have threadBound : 1074900+4≤(storageLayout p).memory.byteSize := by rw [prep.2.1];omega
  have cellBound : 1074904+4≤(storageLayout p).memory.byteSize := by rw [prep.2.1];omega
  have acquireBound : (StateDispatchPrefix.scratch (storageLayout p).toLayout).toNat+8≤(storageLayout p).memory.byteSize := by
    change (StateDispatchLength.scratch (storageLayout p)).toNat+8≤_
    rw [bs,prep.2.1];omega
  have preReady : StateDispatchPrefix.Ready (storageArguments s cfg.regularOpCost p) limits frame callers (storageLayout p).toLayout 2 :=
    ⟨code.prefixCode,h0,by omega,by decide,memory,global,rfl,prep.1,interfaceBound,interfaceRead,
      threadBound,threadRead,cellBound,acquireBound,count,hd⟩
  exact ⟨code,preReady,h1,hs,highBound,lowBound,selectBound,selectedNonzero,selectedBound,inputBound,vtableBound,releaseBound,counterBound⟩
end WNear.Proofs.StateReadStorageOuter
