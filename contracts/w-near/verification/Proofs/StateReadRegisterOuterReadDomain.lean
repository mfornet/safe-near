import Proofs.StateReadRegisterOuterReadPayload
import Proofs.StateReadRegisterOuterReadReady

/-! All435 snapshot conditions are derived from523's original native domain and
actual524/687 writes, including the fresh payload and preserved register ID. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StateReadRegisterOuterReadMemory
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 readInputMemory lengthMemory AllocateVectorOuter.finalMemory AllocateVector.result

theorem read_snapshot (p : Layout) (hn : Native p) (ha : p.allocator=1074896) :
    Snapshot (readLayout p) p.bytes p.register (AllocateVector.result (actualVector p).toVector) p.dispatchVtable := by
  have nums := stack_numbers p hn
  have lower := hn.spLower
  have bound := hn.spBound
  have above := hn.staticAbove
  have align := hn.aligned
  have thread := hn.threadBound
  have vAbove := hn.vtableAbove
  have vBound := hn.vtableBound
  have vBefore := hn.vtableBeforeHeap
  rw [ha] at vBefore
  change p.dispatchVtable.toNat+20≤1074896 at vBefore
  have shape0 := lengthMemory_footprint p hn
  have native := vector_native p hn ha
  have shape := AllocateVectorOuter.final_spec (actualVector p) native
  have vm : (actualVector p).memory=lengthMemory p := rfl
  have total : p.memory.byteSize≤(readInputMemory p).byteSize := by
    unfold readInputMemory
    rw [←shape0.2.1]
    exact shape.2.1
  have wf : (readInputMemory p).wf := by unfold readInputMemory;exact shape.1
  have payload := AllocateVectorOuter.result_payload (actualVector p) native
  have payloadAbove : p.memory.byteSize≤(AllocateVector.result (actualVector p).toVector).toNat := by
    simpa only [vm,shape0.2.1] using payload.1
  have size : p.size.toNat=p.bytes.length := by
    rw [hn.size,UInt32.toNat_ofNat']
    exact Nat.mod_eq_of_lt (lt_trans hn.sizeBound (by decide))
  have payloadBound : (AllocateVector.result (actualVector p).toVector).toNat+p.bytes.length≤(readInputMemory p).byteSize := by
    have avSize : (actualVector p).size=p.size := rfl
    simpa only [readInputMemory,avSize,size] using payload.2
  have nat24 : (scratch p+24).toNat=(scratch p).toNat+24 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    rw [nums.1];have := p.sp523.toNat_lt;omega
  have nat32 := nums.2.2.2.2
  have record := AllocateVectorOuter.final_record (actualVector p) native
  have pointerWord : readI32 (readInputMemory p) (scratch p+32).toNat=AllocateVector.result (actualVector p).toVector := by
    have avOut : (actualVector p).out687=scratch p+32 := hn.vectorOut
    simpa only [readInputMemory,avOut] using record.1
  refine {
    wf := wf
    spLower := ?_, spBound := ?_, aligned := ?_, staticAbove := ?_
    interface := rfl
    interfaceBound := ?_, interfaceRead := ?_, stateBound := ?_, threadStatus := ?_
    counterZero := read_counter_zero p hn ha
    receiverNonzero := ?_, vtableRead := ?_, vtableBound := ?_, vtableAbove := ?_, vtableBeforeCell := ?_
    registerAbove := ?_, registerEnd := ?_, registerRead := read_saved_register p hn ha
    pointerAbove := ?_, pointerEnd := ?_, pointerRead := pointerWord
    payloadAbove := ?_, payloadBound := payloadBound }
  · change 16≤(scratch p).toNat;rw [nums.1];omega
  · change (scratch p).toNat≤(readInputMemory p).byteSize;rw [nums.1];omega
  · change (scratch p).toNat%16=0;rw [nums.1];omega
  · change (scratch p).toNat≤1055020;rw [nums.1];omega
  · change 1055024≤(readInputMemory p).byteSize;have := hn.interfaceBound;omega
  · change readI32 (readInputMemory p) 1055020=p.lookupElement
    rw [read_original_word p hn ha 1055020 hn.interfaceBound above (Or.inl (by omega)) (Or.inl (by omega))]
    exact hn.interfaceRead
  · change 1074916≤(readInputMemory p).byteSize;omega
  · change readI32 (readInputMemory p) 1074900=1
    rw [read_original_word p hn ha 1074900 (by omega) (by omega) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hn.threadStatus
  · change readI32 (readInputMemory p) 1074908≠0
    rw [read_original_word p hn ha 1074908 (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    exact hn.receiverNonzero
  · change readI32 (readInputMemory p) 1074912=p.dispatchVtable
    rw [read_original_word p hn ha 1074912 (by omega) (by omega) (Or.inr (by omega)) (Or.inr (by omega))]
    exact hn.vtableRead
  · change p.dispatchVtable.toNat+16≤(readInputMemory p).byteSize;omega
  · change (scratch p).toNat≤p.dispatchVtable.toNat;rw [nums.1];omega
  · omega
  · change (scratch p).toNat≤(scratch p+24).toNat;rw [nat24];omega
  · change (scratch p+24).toNat+8≤1055020;rw [nat24,nums.1];omega
  · change (scratch p).toNat≤(scratch p+32).toNat;rw [nums.1,nat32];omega
  · change (scratch p+32).toNat+4≤1055020;rw [nat32];omega
  · change (scratch p).toNat≤(AllocateVector.result (actualVector p).toVector).toNat;rw [nums.1];omega
end WNear.Proofs.StateReadRegisterOuter
