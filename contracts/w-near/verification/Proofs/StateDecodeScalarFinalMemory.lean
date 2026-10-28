import Proofs.StateDecodeScalarMemory
import Proofs.StateDecodeScalarPhases
import Proofs.PanicAllocateReadback
import NearVM.MemoryListWordRules

/-! Exact scalar result-memory extent and final accepted tag, with arbitrary output aliases. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 valuesMemory updatedMemory finalMemory

theorem output_addresses (wide : Bool) (p : Layout) (hn : Native wide p) :
    (p.out+8).toNat=p.out.toNat+8 ∧
    (wide=true → (p.out+16).toNat=p.out.toNat+16) := by
  have hb:=hn.outBound
  have hw:=hn.memoryWidth
  have out : (p.out+8).toNat=p.out.toNat+8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    apply Nat.mod_eq_of_lt
    cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hb <;> omega
  refine ⟨out,?_⟩
  intro h
  subst wide
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  apply Nat.mod_eq_of_lt
  simp only [ite_true] at hb
  omega

theorem valuesMemory_spec (wide : Bool) (p : Layout) (hn : Native wide p) :
    (valuesMemory wide p).wf ∧ (valuesMemory wide p).byteSize=p.memory.byteSize ∧
    (valuesMemory wide p).max=p.memory.max := by
  have shape:=droppedMemory_spec wide p hn
  have add:=output_addresses wide p hn
  have hb:=hn.outBound
  cases wide with
  | false=>
    simp only [Bool.false_eq_true,ite_false] at hb
    have low:=writeI64_spec (droppedMemory false p) (p.out+8).toNat (lowValue false p) shape.1
      (by rw [shape.2.1,add.1];omega)
    unfold valuesMemory
    simp only [Bool.false_eq_true,ite_false]
    exact ⟨low.1,low.2.1.trans shape.2.1,low.2.2.1.trans shape.2.2.1⟩
  | true=>
    simp only [ite_true] at hb
    have high:=writeI64_spec (droppedMemory true p) (p.out+16).toNat (highValue p) shape.1
      (by rw [shape.2.1,add.2 rfl];omega)
    have low:=writeI64_spec (writeI64 (droppedMemory true p) (p.out+16).toNat (highValue p))
      (p.out+8).toNat (lowValue true p) high.1
      (by rw [high.2.1,shape.2.1,add.1];omega)
    unfold valuesMemory
    simp only [ite_true]
    exact ⟨low.1,low.2.1.trans (high.2.1.trans shape.2.1),low.2.2.1.trans (high.2.2.1.trans shape.2.2.1)⟩

theorem updatedMemory_spec (wide : Bool) (p : Layout) (hn : Native wide p) :
    (updatedMemory wide p).wf ∧ (updatedMemory wide p).byteSize=p.memory.byteSize ∧
    (updatedMemory wide p).max=p.memory.max := by
  have shape:=valuesMemory_spec wide p hn
  have copy:=writeI64_spec (valuesMemory wide p) p.slice.toNat (dropValue wide p) shape.1
    (by rw [shape.2.1];exact hn.sliceBound)
  unfold updatedMemory
  exact ⟨copy.1,copy.2.1.trans shape.2.1,copy.2.2.1.trans shape.2.2⟩

theorem finalMemory_spec (wide : Bool) (p : Layout) (hn : Native wide p) :
    (finalMemory wide p).wf ∧ (finalMemory wide p).byteSize=p.memory.byteSize ∧
    (finalMemory wide p).max=p.memory.max := by
  have shape:=updatedMemory_spec wide p hn
  have bound : p.out.toNat+4≤(updatedMemory wide p).byteSize := by
    rw [shape.2.1]
    have h:=hn.outBound
    cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at h <;> omega
  have tag:=writeI32_spec (updatedMemory wide p) p.out.toNat 0 shape.1 bound
  unfold finalMemory
  exact ⟨tag.1,tag.2.1.trans shape.2.1,tag.2.2.1.trans shape.2.2⟩

theorem finalMemory_tag (wide : Bool) (p : Layout) (hn : Native wide p) :
    readI32 (finalMemory wide p) p.out.toNat=0 := by
  have shape:=updatedMemory_spec wide p hn
  have bound : p.out.toNat+4≤(updatedMemory wide p).byteSize := by
    rw [shape.2.1]
    have h:=hn.outBound
    cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at h <;> omega
  unfold finalMemory
  exact PanicAllocateReadback.read_write_self (updatedMemory wide p) p.out.toNat 0 shape.1 bound
end WNear.Proofs.StateDecodeScalar
