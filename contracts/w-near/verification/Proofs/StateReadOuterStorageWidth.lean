import Proofs.StateReadOuterStorageHeader
import Proofs.AllocateVectorResources
import Proofs.AllocateRecordResources

/-! The storage allocation's original page bound controls the complete grown
memory, through all record copies and host payload writes. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

private theorem write32_size(m:Memory)(a:Nat)(v:UInt32):(writeI32 m a v).byteSize=m.byteSize:=by
  simp [writeI32,Memory.writeRun,List.range_succ]
private theorem write64_size(m:Memory)(a:Nat)(v:UInt64):(writeI64 m a v).byteSize=m.byteSize:=by
  simp [writeI64,Memory.writeRun,List.range_succ]

private theorem record_width(p:AllocateRecord.Layout)(hn:AllocateRecord.Native p):
    (AllocateRecord.finalMemory p).byteSize≤2^32:=by
  have final:=AllocateRecord.finalMemory_spec p hn
  have allocated:=AllocateZeroedRetry.finalMemory_spec p.toZeroed hn.allocation
  rw [final.2.1]
  unfold AllocateRecord.allocatedMemory
  rw [allocated.2.1]
  have pages:=hn.allocation.pagesBound
  change p.memory.pages.size+_ <65536 at pages
  simp only [Memory.byteSize,pageSize]
  omega

private theorem vector_width(p:AllocateVector.Layout)(hn:AllocateVector.Native p):
    (AllocateVector.resultMemory p).byteSize≤2^32:=by
  have child:=AllocateVector.copy_native p hn
  have width:=record_width (AllocateVector.layout690 p).inner child.inner
  have shape:=AllocateRecordCopy.resultMemory_spec (AllocateVector.layout690 p) child
  unfold AllocateVector.resultMemory
  rw [shape.2.1]
  exact width

private theorem outer_width(p:AllocateVectorOuter.Layout)(hn:AllocateVectorOuter.Native p):
    (AllocateVectorOuter.finalMemory p).byteSize≤2^32:=by
  have width:=vector_width p.toVector (hn.vector p)
  simpa only [AllocateVectorOuter.finalMemory,AllocateVectorOuter.allocatedMemory,
    AllocateVector.finalMemory,AllocateVector.recordMemory,AllocateVectorOuter.outputMemory,
    StorePair.pairMemory,write32_size,write64_size] using width

private theorem list_size(m:Memory)(a:Nat)(bs:List UInt8):(m.writeList a bs).byteSize=m.byteSize:=by
  induction bs generalizing m a with
  | nil => rw [Memory.writeList_nil]
  | cons b bs ih =>
    rw [Memory.writeList_cons,ih]
    split <;> simp

private theorem readFinal_width(p:StateReadRegisterOuter.Layout)(hn:StateReadRegisterOuter.Native p)
    (ha:p.allocator=1074896): (StateReadRegisterOuter.readFinalMemory p).byteSize≤2^32:=by
  have width:=outer_width (StateReadRegisterOuter.actualVector p) (StateReadRegisterOuter.vector_native p hn ha)
  have snapshot:=StateReadRegisterOuter.read_snapshot p hn ha
  have low:=snapshot.low_shape
  have eq:(StateReadRegisterOuter.readFinalMemory p).byteSize=(StateReadRegisterOuter.readInputMemory p).byteSize:=by
    simp only [StateReadRegisterOuter.readFinalMemory,write32_size,
      StateReadRegisterOuter.readOutputMemory,StateDispatchRead.readMemory,list_size]
    exact low.2.1
  rw [eq]
  exact width

private theorem register_width(p:StateReadRegisterOuter.Layout)(hn:StateReadRegisterOuter.Native p)
    (ha:p.allocator=1074896): (StateReadRegisterOuter.copiedMemory p).byteSize≤2^32:=by
  have width:=readFinal_width p hn ha
  simpa only [StateReadRegisterOuter.copiedMemory,StateReadRegisterOuter.finalMemory,
    StateReadRegisterOuter.firstMemory,write32_size,write64_size] using width

attribute [local irreducible] StateReadStorageOuter.registeredMemory StateReadStorageOuter.actualRegister
  StateReadRegisterOuter.copiedMemory

/-- The original page-count guard bounds the entire actual548 memory. -/
theorem storage_final_width(p:StateReadStorageOuter.Layout)(hn:StateReadStorageOuter.Native p)
    (ha:p.allocator=1074896): (StateReadStorageOuter.finalMemory p).byteSize≤2^32:=by
  rw [(StateReadStorageOuter.finalMemory_shape p hn ha).2.1]
  have root : (StateReadStorageOuter.actualRegister p).allocator=1074896 := by
    simpa only [StateReadStorageOuter.actualRegister,StateReadStorageOuter.registerTemplate] using ha
  have width := register_width (StateReadStorageOuter.actualRegister p)
    (StateReadStorageOuter.register_native p hn ha) root
  simpa only [StateReadStorageOuter.registeredMemory] using width

/-- Original memory bounds remain valid after548. -/
theorem storage_final_grows(p:StateReadStorageOuter.Layout)(hn:StateReadStorageOuter.Native p)
    (ha:p.allocator=1074896):p.memory.byteSize≤(StateReadStorageOuter.finalMemory p).byteSize:=by
  have root:(StateReadStorageOuter.actualRegister p).allocator=1074896:=by
    simpa only [StateReadStorageOuter.actualRegister,StateReadStorageOuter.registerTemplate] using ha
  have shape:=StateReadRegisterOuter.copiedMemory_spec (StateReadStorageOuter.actualRegister p)
    (StateReadStorageOuter.register_native p hn ha) root
  have old:(StateReadStorageOuter.actualRegister p).memory.byteSize=p.memory.byteSize:=by
    simpa only [StateReadStorageOuter.actualRegister,StateReadStorageOuter.registerTemplate] using
      (StateReadStorageOuter.storageMemory_footprint p hn).2.1
  have grow:=shape.2.1
  rw [old] at grow
  rw [(StateReadStorageOuter.finalMemory_shape p hn ha).2.1]
  simpa only [StateReadStorageOuter.registeredMemory] using grow

/-- The full payload span survives every post-allocation write. -/
theorem storage_final_payload_span(p:StateReadStorageOuter.Layout)(hn:StateReadStorageOuter.Native p)
    (ha:p.allocator=1074896):
    (AllocateVector.result (StateReadRegisterOuter.actualVector (StateReadStorageOuter.actualRegister p)).toVector).toNat+
      p.bytes.length≤(StateReadStorageOuter.finalMemory p).byteSize:=by
  let q:=StateReadStorageOuter.actualRegister p
  have native:=StateReadStorageOuter.register_native p hn ha
  have root:q.allocator=1074896:=by
    simpa only [q,StateReadStorageOuter.actualRegister,StateReadStorageOuter.registerTemplate] using ha
  have snapshot:=StateReadRegisterOuter.read_snapshot q native root
  have low:=snapshot.low_shape
  have eq:(StateReadRegisterOuter.readFinalMemory q).byteSize=(StateReadRegisterOuter.readInputMemory q).byteSize:=by
    simp only [StateReadRegisterOuter.readFinalMemory,write32_size,
      StateReadRegisterOuter.readOutputMemory,StateDispatchRead.readMemory,list_size]
    exact low.2.1
  have copy:(StateReadRegisterOuter.copiedMemory q).byteSize=(StateReadRegisterOuter.readInputMemory q).byteSize:=by
    simp only [StateReadRegisterOuter.copiedMemory,StateReadRegisterOuter.finalMemory,
      StateReadRegisterOuter.firstMemory,write32_size,write64_size]
    exact eq
  rw [(StateReadStorageOuter.finalMemory_shape p hn ha).2.1]
  have bound:=snapshot.payloadBound
  have bytes:q.bytes=p.bytes:=by
    simp only [q,StateReadStorageOuter.actualRegister,StateReadStorageOuter.registerTemplate]
  rw [bytes] at bound
  have size:(StateReadStorageOuter.registeredMemory p).byteSize=(StateReadRegisterOuter.readInputMemory q).byteSize:=by
    simpa only [q,StateReadStorageOuter.registeredMemory] using copy
  rw [size]
  exact bound
end WNear.Proofs.StateReadOuter
