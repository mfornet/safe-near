import Proofs.StateDecodeVectorState
import Proofs.StateDecodeRawMemory

/-! All373 scratch and result bounds follow from its original selected domain. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic

theorem stack_numbers (p:Layout) (hn:Native p) :
    (scratch p).toNat=p.spVector.toNat-16 ∧p.spRaw=scratch p ∧
    p.outRaw.toNat=(scratch p).toNat+8 ∧(scratch p).toNat+16≤p.memory.byteSize ∧scratch p+16=p.spVector := by
  have lo:=hn.spLower
  have lt:=UInt32.toNat_lt p.spVector
  have sp:(scratch p).toNat=p.spVector.toNat-16:=by
    unfold scratch
    rw[UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have child:p.spRaw=scratch p:=hn.childSP
  have out:p.outRaw.toNat=(scratch p).toNat+8:=by
    rw[hn.childOut,child,UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact ⟨sp,child,out,by have h:=hn.spBound;omega,UInt32.sub_add_cancel _ _⟩

theorem allocated_spec (p:Layout) (hn:Native p) :
    (memoryAllocated p).wf ∧(memoryAllocated p).byteSize=p.memory.byteSize ∧(memoryAllocated p).max=p.memory.max ∧
    readI32 (memoryAllocated p) p.outRaw.toNat=StateDecodeRaw.result p.toRaw ∧
    readI32 (memoryAllocated p) (p.outRaw.toNat+4)=p.size := by
  have s:=StateDecodeRaw.finalMemory_spec p.toRaw hn.raw
  exact ⟨s.1,s.2.1,s.2.2.1,s.2.2.2.1,s.2.2.2.2.1⟩
end WNear.Proofs.StateDecodeVector
