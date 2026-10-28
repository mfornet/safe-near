import Proofs.AllocateVectorResources
import Proofs.PanicAllocateReadback

/-! The686 cached record is written pointer first, then size. Both output words
are canonical even when the caller's record overlaps the prior allocation. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] recordMemory finalMemory resultMemory readI32 writeI32

theorem recordMemory_spec (memory : Memory) (out pointer size : UInt32)
    (hw : memory.wf) (hb : out.toNat+8≤memory.byteSize) :
    (recordMemory memory out pointer size).wf ∧
    (recordMemory memory out pointer size).byteSize=memory.byteSize ∧
    (recordMemory memory out pointer size).max=memory.max ∧
    readI32 (recordMemory memory out pointer size) out.toNat=pointer ∧
    readI32 (recordMemory memory out pointer size) (out.toNat+4)=size ∧
    ∀ j, (j<out.toNat ∨ out.toNat+8≤j) → (recordMemory memory out pointer size).read8 j=memory.read8 j := by
  let low := writeI32 memory out.toNat pointer
  have a := writeI32_spec memory out.toNat pointer hw (by omega)
  have bnd : out.toNat+4+4≤low.byteSize := by rw [show low.byteSize=memory.byteSize from a.2.1];omega
  have b := writeI32_spec low (out.toNat+4) size a.1 bnd
  have lo := PanicAllocateReadback.read_write_self memory out.toNat pointer hw (by omega)
  have loFrame := PanicAllocateReadback.read_write_frame low out.toNat (out.toNat+4) size a.1 bnd (by omega)
  have hi := PanicAllocateReadback.read_write_self low (out.toNat+4) size a.1 bnd
  have shape : (recordMemory memory out pointer size).wf ∧
      (recordMemory memory out pointer size).byteSize=low.byteSize ∧
      (recordMemory memory out pointer size).max=low.max := by
    simpa only [recordMemory,low] using And.intro b.1 (And.intro b.2.1 b.2.2.1)
  have lowValue : readI32 (recordMemory memory out pointer size) out.toNat=pointer := by
    rw [recordMemory]
    exact loFrame.trans lo
  have highValue : readI32 (recordMemory memory out pointer size) (out.toNat+4)=size := by
    simpa only [recordMemory,low] using hi
  refine ⟨shape.1,shape.2.1.trans a.2.1,shape.2.2.trans a.2.2.1,lowValue,highValue,?_⟩
  intro j hj
  rw [recordMemory,b.2.2.2,ite_eq_right (show ¬(out.toNat+4≤j ∧ j<out.toNat+4+4) by omega)]
  rw [show low.read8 j=if out.toNat≤j ∧ j<out.toNat+4 then
      UInt8.ofNat (pointer.toNat >>> (8*(j-out.toNat))) else memory.read8 j from a.2.2.2 j]
  rw [ite_eq_right (show ¬(out.toNat≤j ∧ j<out.toNat+4) by omega)]

 theorem finalMemory_spec (p : Layout) (hn : Native p) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=(resultMemory p).byteSize ∧
    (finalMemory p).max=p.memory.max ∧
    readI32 (finalMemory p) p.out686.toNat=result p ∧
    readI32 (finalMemory p) (p.out686.toNat+4)=p.size ∧
    ∀ j, (j<p.out686.toNat ∨ p.out686.toNat+8≤j) → (finalMemory p).read8 j=(resultMemory p).read8 j := by
  have shape := resultMemory_spec p hn
  have outBound := hn.outputBound.trans shape.2.1
  have record := recordMemory_spec (resultMemory p) p.out686 (result p) p.size shape.1 outBound
  unfold finalMemory
  exact ⟨record.1,record.2.1,record.2.2.1.trans shape.2.2,record.2.2.2⟩
 theorem final_words (p : Layout) (hn : Native p) :
    readI32 (finalMemory p) p.out686.toNat=result p ∧
    readI32 (finalMemory p) (p.out686.toNat+4)=p.size := by
  have h := finalMemory_spec p hn
  exact ⟨h.2.2.2.1,h.2.2.2.2.1⟩
end WNear.Proofs.AllocateVector
