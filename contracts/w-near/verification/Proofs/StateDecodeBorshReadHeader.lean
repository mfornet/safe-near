import Proofs.StateDecodeBorshReadMemoryNative
import Proofs.StateDecodeBorshWrapperSlice

/-! Original29-byte header inputs justify161's real exhausted-input guard.
A header prefix alone does not imply this guard: the input length29 is explicit. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

theorem setup_header(p:Layout)(hn:Native p)(state:WNear.State)
    (h:StateReadHeaderBytes.At p.memory p.pointer.toNat state):
    StateReadHeaderBytes.At (setupMemory p) p.pointer.toNat state:=by
  have n:=scratch_numbers p hn
  have source:=hn.sourceAbove
  intro i hi
  rw[setupMemory_byte_frame p hn (p.pointer.toNat+i) (Or.inr (by omega))]
  exact h i hi

theorem wrappedMemory_exhausted_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)(hl:p.length=29):
    readI32 (wrappedMemory p q) p.slice.toNat=p.pointer+29 ∧
    readI32 (wrappedMemory p q) (p.slice.toNat+4)=0:=by
  have geo:=stack_geometry p hn
  have n:=scratch_numbers p hn
  have input:StateReadHeaderBytes.At (actualWrapper p).memory (actualWrapper p).pointer.toNat state:=setup_header p hn state h
  have hs:(actualWrapper p).sp162.toNat≤(actualWrapper p).slice.toNat:=by
    change p.sp162.toNat≤p.slice.toNat;omega
  have ho:(actualWrapper p).out162.toNat+48≤(actualWrapper p).slice.toNat ∨(actualWrapper p).slice.toNat+8≤(actualWrapper p).out162.toNat:=by
    change p.out162.toNat+48≤p.slice.toNat ∨p.slice.toNat+8≤p.out162.toNat
    right;omega
  exact StateDecodeBorshWrapper.finalMemory_exhausted_header (actualWrapper p) (actualAllocation p q)
    (wrapper_native p hn) (accepted_domain p q hn hd) hs ho state hw input hl

theorem acceptedMemory_exhausted_header(p:Layout)(q:StateDecodeVectorCopy.Layout)(hn:Native p)(hd:AcceptedDomain p q)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)(hl:p.length=29):
    readI32 (acceptedMemory p q) ((scratch p).toNat+12)=0:=by
  have old:=(wrappedMemory_exhausted_header p q hn hd state hw h hl).2
  have slice:p.slice.toNat=(scratch p).toNat+8:=by rw[hn.slice];exact scratch_add p hn 8 (by omega)
  rw[slice,show (scratch p).toNat+8+4=(scratch p).toNat+12 by omega] at old
  have wrapped:=wrappedMemory_spec p q hn hd
  have scratchShape:=scratchMemory_spec p q hn hd
  have upper:=upperMemory_spec p q hn hd
  have first:=ForwardCopyMemory.spec (wrappedMemory p q) (scratch p+60).toNat (scratch p+108).toNat 36 wrapped.1 (first_copy_bounds p q hn hd).1
  have a60:(scratch p+60).toNat=(scratch p).toNat+60:=scratch_add p hn 60 (by omega)
  have n:=scratch_numbers p hn
  have stored:=writeI32_spec (scratchMemory p q) ((scratch p).toNat+16) (UInt32.ofNat ((packedValue p q>>>32).toNat)) scratchShape.1 (by rw[scratchShape.2.1];omega)
  have last:=ForwardCopyMemory.spec (upperMemory p q) ((scratch p+16)|||4).toNat (scratch p+60).toNat 36 upper.1 (accepted_copy_bounds p q hn hd).1
  have frame:readI32 (acceptedMemory p q) ((scratch p).toNat+12)=readI32 (wrappedMemory p q) ((scratch p).toNat+12):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold acceptedMemory
    rw[last.2.2.2 _ (Or.inl (by rw[scratch_or4 p hn];omega))]
    unfold upperMemory
    rw[stored.2.2.2,ite_eq_right (by omega)]
    unfold scratchMemory
    exact first.2.2.2 _ (Or.inl (by rw[a60];omega))
  exact frame.trans old
end WNear.Proofs.StateDecodeBorshRead
