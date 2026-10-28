import Proofs.StateDecodeScalarFinalMemory
import Proofs.StorePairReadback

/-! Canonical scalar words require only separation from the later slice update. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI64 writeI64 writeI32 valuesMemory updatedMemory finalMemory

private theorem read64_write64_self (memory : Memory) (address : Nat) (value : UInt64)
    (hw : memory.wf) (hb : address+8≤memory.byteSize) :
    readI64 (writeI64 memory address value) address=value := by
  have spec:=writeI64_spec memory address value hw hb
  apply StorePairReadback.readI64_of_bytes
  intro i hi
  rw [spec.2.2.2,ite_eq_left (by omega),Nat.add_sub_cancel_left]

private theorem read64_write64_frame (memory : Memory) (readAt writeAt : Nat) (value : UInt64)
    (hw : memory.wf) (hb : writeAt+8≤memory.byteSize) (hs : writeAt+8≤readAt ∨ readAt+8≤writeAt) :
    readI64 (writeI64 memory writeAt value) readAt=readI64 memory readAt := by
  have spec:=writeI64_spec memory writeAt value hw hb
  apply readI64_congr_bytes
  intro i hi
  rw [spec.2.2.2,ite_eq_right (by omega)]

private theorem read64_write32_frame (memory : Memory) (readAt writeAt : Nat) (value : UInt32)
    (hw : memory.wf) (hb : writeAt+4≤memory.byteSize) (hs : writeAt+4≤readAt ∨ readAt+8≤writeAt) :
    readI64 (writeI32 memory writeAt value) readAt=readI64 memory readAt := by
  have spec:=writeI32_spec memory writeAt value hw hb
  apply readI64_congr_bytes
  intro i hi
  rw [spec.2.2.2,ite_eq_right (by omega)]

theorem valuesMemory_low (wide : Bool) (p : Layout) (hn : Native wide p) :
    readI64 (valuesMemory wide p) (p.out.toNat+8)=lowValue wide p := by
  have shape:=droppedMemory_spec wide p hn
  have addr:=output_addresses wide p hn
  have hb:=hn.outBound
  cases wide with
  | false=>
    simp only [Bool.false_eq_true,ite_false] at hb
    unfold valuesMemory
    simp only [Bool.false_eq_true,ite_false,addr.1]
    exact read64_write64_self _ _ _ shape.1 (by rw [shape.2.1];omega)
  | true=>
    simp only [ite_true] at hb
    have high:=writeI64_spec (droppedMemory true p) (p.out+16).toNat (highValue p) shape.1
      (by rw [shape.2.1,addr.2 rfl];omega)
    unfold valuesMemory
    simp only [ite_true,addr.1]
    exact read64_write64_self _ _ _ high.1 (by rw [high.2.1,shape.2.1];omega)

theorem valuesMemory_high (p : Layout) (hn : Native true p) :
    readI64 (valuesMemory true p) (p.out.toNat+16)=highValue p := by
  have shape:=droppedMemory_spec true p hn
  have addr:=output_addresses true p hn
  have hb:=hn.outBound
  simp only [ite_true] at hb
  have high:=writeI64_spec (droppedMemory true p) (p.out+16).toNat (highValue p) shape.1
    (by rw [shape.2.1,addr.2 rfl];omega)
  have lowBound : (p.out+8).toNat+8≤(writeI64 (droppedMemory true p) (p.out+16).toNat (highValue p)).byteSize := by
    rw [high.2.1,shape.2.1,addr.1];omega
  unfold valuesMemory
  simp only [ite_true]
  rw [read64_write64_frame _ _ _ _ high.1 lowBound (Or.inl (by rw [addr.1]))]
  rw [←addr.2 rfl]
  exact read64_write64_self _ _ _ shape.1 (by rw [shape.2.1,addr.2 rfl];omega)

theorem finalMemory_low (wide : Bool) (p : Layout) (hn : Native wide p)
    (hs : p.slice.toNat+8≤p.out.toNat+8 ∨ p.out.toNat+16≤p.slice.toNat) :
    readI64 (finalMemory wide p) (p.out.toNat+8)=lowValue wide p := by
  have value:=valuesMemory_spec wide p hn
  have update:=updatedMemory_spec wide p hn
  have hb : p.out.toNat+4≤(updatedMemory wide p).byteSize := by
    rw [update.2.1]
    have h:=hn.outBound
    cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at h <;> omega
  unfold finalMemory
  rw [read64_write32_frame _ _ _ _ update.1 hb (Or.inl (by omega))]
  unfold updatedMemory
  rw [read64_write64_frame _ _ _ _ value.1 (by rw [value.2.1];exact hn.sliceBound) (by omega)]
  exact valuesMemory_low wide p hn

theorem finalMemory_high (p : Layout) (hn : Native true p)
    (hs : p.slice.toNat+8≤p.out.toNat+16 ∨ p.out.toNat+24≤p.slice.toNat) :
    readI64 (finalMemory true p) (p.out.toNat+16)=highValue p := by
  have value:=valuesMemory_spec true p hn
  have update:=updatedMemory_spec true p hn
  have hb : p.out.toNat+4≤(updatedMemory true p).byteSize := by
    rw [update.2.1]
    have h:=hn.outBound
    simp only [ite_true] at h
    omega
  unfold finalMemory
  rw [read64_write32_frame _ _ _ _ update.1 hb (Or.inl (by omega))]
  unfold updatedMemory
  rw [read64_write64_frame _ _ _ _ value.1 (by rw [value.2.1];exact hn.sliceBound) (by omega)]
  exact valuesMemory_high p hn
end WNear.Proofs.StateDecodeScalar
