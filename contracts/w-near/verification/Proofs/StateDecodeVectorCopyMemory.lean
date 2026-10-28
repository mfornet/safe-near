import Proofs.StateDecodeVectorCopyState

/-! Pure shape and length of374's exact sequential final memory. -/
namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 copiedMemory

theorem copiedMemory_spec (p:Layout)(hn:Native p):
    (copiedMemory p).wf ∧ (copiedMemory p).byteSize=p.memory.byteSize ∧ (copiedMemory p).max=p.memory.max ∧
    ∀j,(j<(pointer p).toNat ∨ (pointer p).toNat+p.size.toNat≤j) →
      (copiedMemory p).read8 j=(StateDecodeVector.finalMemory p.toVector).read8 j:=by
  have b:=copy_bounds p hn
  have h:=ForwardCopyMemory.spec (StateDecodeVector.finalMemory p.toVector) (pointer p).toNat p.source.toNat p.size.toNat b.1 b.2.2.2.2.1
  have s:=StateDecodeVector.finalMemory_shape p.toVector hn.vector
  unfold copiedMemory
  exact ⟨h.1,h.2.1.trans s.2.1,h.2.2.1.trans s.2.2,h.2.2.2⟩

theorem finalMemory_spec (p:Layout)(hn:Native p):
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧ (finalMemory p).max=p.memory.max ∧
    readI32 (finalMemory p) (p.outVector.toNat+8)=p.size ∧
    ∀j,(j<p.outVector.toNat+8 ∨ p.outVector.toNat+12≤j) → (finalMemory p).read8 j=(copiedMemory p).read8 j:=by
  have c:=copiedMemory_spec p hn
  have bound:p.outVector.toNat+8+4≤(copiedMemory p).byteSize:=by rw[c.2.1];exact hn.vector.outBound
  have w:=writeI32_spec (copiedMemory p) (p.outVector.toNat+8) p.size c.1 bound
  have word:=PanicAllocateReadback.read_write_self (copiedMemory p) (p.outVector.toNat+8) p.size c.1 bound
  refine ⟨w.1,w.2.1.trans c.2.1,w.2.2.1.trans c.2.2.1,word,?_⟩
  intro j hj
  unfold finalMemory
  rw[w.2.2.2]
  have no:¬(p.outVector.toNat+8≤j ∧j<p.outVector.toNat+8+4):=by omega
  exact ite_eq_right no
end WNear.Proofs.StateDecodeVectorCopy
