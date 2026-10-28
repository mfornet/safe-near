import Proofs.StateDecodeBorshNarrowNative

/-! Remaining425 sequential memory shapes, derived from its original accepted
inputs. UInt32 added output addresses are justified by the original bounds. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64
private def Shape (original current : Memory) : Prop := current.wf ∧current.byteSize=original.byteSize ∧current.max=original.max
private theorem write32_shape (original current : Memory) (address : Nat) (value : UInt32)
    (h : Shape original current) (hb : address+4≤original.byteSize) : Shape original (writeI32 current address value) := by
  have bound:address+4≤current.byteSize:=by rw[h.2.1];exact hb
  have spec:=writeI32_spec current address value h.1 bound
  exact ⟨spec.1,spec.2.1.trans h.2.1,spec.2.2.1.trans h.2.2⟩
private theorem write64_shape (original current : Memory) (address : Nat) (value : UInt64)
    (h : Shape original current) (hb : address+8≤original.byteSize) : Shape original (writeI64 current address value) := by
  have bound:address+8≤current.byteSize:=by rw[h.2.1];exact hb
  have spec:=writeI64_spec current address value h.1 bound
  exact ⟨spec.1,spec.2.1.trans h.2.1,spec.2.2.1.trans h.2.2⟩

theorem narrowMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (narrowMemory p q).wf ∧(narrowMemory p q).byteSize=p.memory.byteSize ∧(narrowMemory p q).max=p.memory.max := by
  have prev:=savedWideMemory_specs p q hn hd
  have shape:=StateDecodeScalar.finalMemory_spec false (narrowLayout p q) (narrow_native p q hn hd)
  change (narrowMemory p q).wf ∧(narrowMemory p q).byteSize=(savedWideMemory p q).byteSize ∧(narrowMemory p q).max=(savedWideMemory p q).max at shape
  exact ⟨shape.1,shape.2.1.trans prev.2.2.2.2.2.1,shape.2.2.trans prev.2.2.2.2.2.2⟩

theorem narrowHighMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (narrowHighMemory p q).wf ∧(narrowHighMemory p q).byteSize=p.memory.byteSize ∧(narrowHighMemory p q).max=p.memory.max := by
  have prev:=narrowMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a:((scratch p+80)+8).toNat=(scratch p).toNat+88:=by
    have eq:(scratch p+80)+8=scratch p+88:=by rw[UInt32.add_assoc];rfl
    rw[eq];exact scratch_add p hn 88 (by omega)
  unfold narrowHighMemory
  apply write32_shape p.memory _ _ _ prev
  rw[a];omega

theorem savedNarrowMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (savedNarrowMemory p q).wf ∧(savedNarrowMemory p q).byteSize=p.memory.byteSize ∧(savedNarrowMemory p q).max=p.memory.max := by
  have prev:=narrowHighMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  unfold savedNarrowMemory
  exact write64_shape p.memory _ _ _ prev (by omega)

theorem vectorHighMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (vectorHighMemory p q).wf ∧(vectorHighMemory p q).byteSize=p.memory.byteSize ∧(vectorHighMemory p q).max=p.memory.max := by
  have prev:=savedNarrowMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  have a:(scratch p+8).toNat=(scratch p).toNat+8:=scratch_add p hn 8 (by omega)
  unfold vectorHighMemory
  apply write32_shape p.memory _ _ _ prev
  rw[a];omega

theorem cachedMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (cachedMemory p q).wf ∧(cachedMemory p q).byteSize=p.memory.byteSize ∧(cachedMemory p q).max=p.memory.max := by
  have prev:=vectorHighMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  unfold cachedMemory
  exact write64_shape p.memory _ _ _ prev (by omega)

theorem output16Memory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (output16Memory p q).wf ∧(output16Memory p q).byteSize=p.memory.byteSize ∧(output16Memory p q).max=p.memory.max := by
  have prev:=cachedMemory_spec p q hn hd
  have a:(p.out425+16).toNat=p.out425.toNat+16:=output_add p hn 16 (by omega)
  have bound:=hn.outBound
  unfold output16Memory
  apply write64_shape p.memory _ _ _ prev
  rw[a];omega

theorem output8Memory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (output8Memory p q).wf ∧(output8Memory p q).byteSize=p.memory.byteSize ∧(output8Memory p q).max=p.memory.max := by
  have prev:=output16Memory_spec p q hn hd
  have a:(p.out425+8).toNat=p.out425.toNat+8:=output_add p hn 8 (by omega)
  have bound:=hn.outBound
  unfold output8Memory
  apply write64_shape p.memory _ _ _ prev
  rw[a];omega

theorem output24Memory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (output24Memory p q).wf ∧(output24Memory p q).byteSize=p.memory.byteSize ∧(output24Memory p q).max=p.memory.max := by
  have prev:=output8Memory_spec p q hn hd
  have a:(p.out425+24).toNat=p.out425.toNat+24:=output_add p hn 24 (by omega)
  have bound:=hn.outBound
  unfold output24Memory
  apply write64_shape p.memory _ _ _ prev
  rw[a];omega

theorem output32Memory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (output32Memory p q).wf ∧(output32Memory p q).byteSize=p.memory.byteSize ∧(output32Memory p q).max=p.memory.max := by
  have prev:=output24Memory_spec p q hn hd
  have a:(p.out425+32).toNat=p.out425.toNat+32:=output_add p hn 32 (by omega)
  have bound:=hn.outBound
  unfold output32Memory
  apply write64_shape p.memory _ _ _ prev
  rw[a];omega

theorem output40Memory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (output40Memory p q).wf ∧(output40Memory p q).byteSize=p.memory.byteSize ∧(output40Memory p q).max=p.memory.max := by
  have prev:=output32Memory_spec p q hn hd
  have a:(p.out425+40).toNat=p.out425.toNat+40:=output_add p hn 40 (by omega)
  have bound:=hn.outBound
  unfold output40Memory
  apply write32_shape p.memory _ _ _ prev
  rw[a];omega

theorem finalMemory_spec (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p) (hd : AcceptedDomain p q) :
    (finalMemory p q).wf ∧(finalMemory p q).byteSize=p.memory.byteSize ∧(finalMemory p q).max=p.memory.max := by
  have prev:=output40Memory_spec p q hn hd
  have bound:=hn.outBound
  unfold finalMemory
  exact write32_shape p.memory _ _ _ prev (by omega)
end WNear.Proofs.StateDecodeBorsh
