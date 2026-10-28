import Proofs.DeallocateInsertState
import Proofs.PanicAllocateReadback

/-! Original heap words suffice for the insertion domain after the actual
header mark and payload-zero writes. No post-write lookup is an input. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readByteWord writeI32 markedMemory zeroMemory

structure Original(p:DeallocateCore.Layout):Prop where
  wf:p.memory.wf
  pointerNonzero:p.pointer≠0
  lengthNonzero:p.length≠0
  lengthBound:p.length.toNat+4<2^32
  headerEq:p.pointer+4294967288=p.header
  previousAddressEq:p.pointer+4294967292=p.previousAddress
  pointerNat:p.header.toNat+8=p.pointer.toNat
  previousAddressNat:p.previousAddress.toNat=p.header.toNat+4
  allocatorBound:p.allocator.toNat+4≤p.memory.byteSize
  pointerBound:p.pointer.toNat+4≤p.memory.byteSize
  currentSize:p.header.toNat+8≤(DeallocateListSize.endWord p.memory p.header).toNat
  previousRead:Deallocate.previous p.memory p.previousAddress=p.previous
  previousNonzero:p.previous≠0
  previousBound:p.previous.toNat+1≤p.memory.byteSize
  previousBelow:p.previous.toNat+1≤p.header.toNat
  previousAllocated:readByteWord p.memory p.previous.toNat &&&1≠0
  nextAddressNonzero:readI32 p.memory p.header.toNat &&&4294967292≠0
  nextDisabled:readI32 p.memory p.header.toNat &&&2≠0

theorem native_of_original(p:DeallocateCore.Layout)(h:Original p):Native p:=by
  have hb:p.header.toNat+4≤p.memory.byteSize:=by have:=h.pointerBound;have:=h.pointerNat;omega
  have mark:=writeI32_spec p.memory p.header.toNat (readI32 p.memory p.header.toNat&&&4294967294) h.wf hb
  have markSize:(markedMemory p).byteSize=p.memory.byteSize:=by simpa only [markedMemory] using mark.2.1
  have markWf:(markedMemory p).wf:=by simpa only [markedMemory] using mark.1
  have zero:=writeI32_spec (markedMemory p) p.pointer.toNat 0 markWf (by rw [markSize];exact h.pointerBound)
  have zeroSize:(zeroMemory p).byteSize=p.memory.byteSize:=by simpa only [zeroMemory] using zero.2.1.trans markSize
  have self:readI32 (markedMemory p) p.header.toNat=readI32 p.memory p.header.toNat&&&4294967294:=by
    unfold markedMemory
    exact PanicAllocateReadback.read_write_self _ _ _ h.wf hb
  have header:readI32 (zeroMemory p) p.header.toNat=readI32 p.memory p.header.toNat&&&4294967294:=by
    unfold zeroMemory
    exact (PanicAllocateReadback.read_write_frame _ _ _ _ markWf (by rw [markSize];exact h.pointerBound)
      (Or.inl (by have:=h.pointerNat;omega))).trans self
  have previous:readI32 (zeroMemory p) p.previousAddress.toNat=readI32 p.memory p.previousAddress.toNat:=by
    unfold zeroMemory
    rw [PanicAllocateReadback.read_write_frame _ _ _ _ markWf (by rw [markSize];exact h.pointerBound)
      (Or.inl (by have:=h.pointerNat;have:=h.previousAddressNat;omega))]
    unfold markedMemory
    exact PanicAllocateReadback.read_write_frame _ _ _ _ h.wf hb (Or.inr (by have:=h.previousAddressNat;omega))
  have byte:(zeroMemory p).read8 p.previous.toNat=p.memory.read8 p.previous.toNat:=by
    unfold zeroMemory
    rw [zero.2.2.2,ite_eq_right (by have:=h.previousBelow;have:=h.pointerNat;omega)]
    unfold markedMemory
    rw [mark.2.2.2,ite_eq_right (by have:=h.previousBelow;omega)]
  have masked:(readI32 p.memory p.header.toNat&&&4294967294)&&&4294967292=
      readI32 p.memory p.header.toNat&&&4294967292:=by rw [UInt32.and_assoc];rfl
  have disabled:(readI32 p.memory p.header.toNat&&&4294967294)&&&2=
      readI32 p.memory p.header.toNat&&&2:=by rw [UInt32.and_assoc];rfl
  refine ⟨h.wf,h.pointerNonzero,h.lengthNonzero,h.lengthBound,h.headerEq,h.previousAddressEq,
    h.allocatorBound,hb,h.pointerBound,?_,?_,?_,h.previousNonzero,?_,?_,?_,?_,?_⟩
  · unfold DeallocateListSize.endWord
    rw [self,masked]
    exact h.currentSize
  · rw [zeroSize];have:=h.previousAddressNat;have:=h.pointerNat;have:=h.pointerBound;omega
  · unfold Deallocate.previous;rw [previous];exact h.previousRead
  · rw [zeroSize];exact h.previousBound
  · rw [readByteWord_eq,byte]
    simpa only [readByteWord_eq] using h.previousAllocated
  · rw [zeroSize];exact hb
  · rw [header,masked];exact h.nextAddressNonzero
  · rw [header,disabled];exact h.nextDisabled
end WNear.Proofs.DeallocateInsert
