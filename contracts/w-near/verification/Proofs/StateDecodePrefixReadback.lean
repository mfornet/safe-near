import Proofs.StateDecodePrefixMemory
import Proofs.AllocateSplitReadback

/-! Actual descriptor and original payload readbacks along316's accepted prefix. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI64

theorem takenFour_words (p:Layout) (hn:Native p) :
    readI32 (takenFourMemory p) (takeFourOut p).toNat=p.pointer ∧
    readI32 (takenFourMemory p) ((takeFourOut p).toNat+4)=4 := by
  have add:(takeFourOut p).toNat=(scratch p).toNat+40:=scratch_add p hn 40 (by omega)
  have e:=scratch_end p hn
  have bound:(takeFourOut p).toNat+8≤p.memory.byteSize:=by rw[add];have h:=hn.spBound;omega
  exact StateDecodeSlices.finalMemory_words false p.memory (takeFourOut p) p.pointer p.length 4 hn.wf bound

theorem count_after_take (p:Layout) (hn:Native p) :
    readI32 (takenFourMemory p) p.pointer.toNat=count p := by
  have hs:=takenFour_spec p hn
  apply Allocate.readI32_congr_bytes
  intro i hi
  exact hs.2.2.2 _ (by have h:=hn.pointerAbove;omega)

theorem droppedFour_words (p:Layout) (hn:Native p) :
    readI32 (droppedFourMemory p) (dropFourOut p).toNat=payloadPointer p ∧
    readI32 (droppedFourMemory p) ((dropFourOut p).toNat+4)=remaining p := by
  have ht:=takenFour_spec p hn
  have add:(dropFourOut p).toNat=(scratch p).toNat+32:=scratch_add p hn 32 (by omega)
  have e:=scratch_end p hn
  have bound:(dropFourOut p).toNat+8≤(takenFourMemory p).byteSize:=by rw[add,ht.2.1];have h:=hn.spBound;omega
  exact StateDecodeSlices.finalMemory_words true (takenFourMemory p) (dropFourOut p) p.pointer p.length 4 ht.1 bound

private theorem copied_words (m:Memory) (out source:Nat) (a b:UInt32) (hw:m.wf) (hb:out+8≤m.byteSize)
    (h0:readI32 m source=a) (h1:readI32 m (source+4)=b) :
    readI32 (AllocateLayoutWrapperReadback.packedCopy m out source) out=a ∧
    readI32 (AllocateLayoutWrapperReadback.packedCopy m out source) (out+4)=b := by
  have low:=AllocateLayoutWrapperReadback.packedCopy_word m out source 0 hw hb (by omega)
  have high:=AllocateLayoutWrapperReadback.packedCopy_word m out source 4 hw hb (by omega)
  have lo:readI32 (AllocateLayoutWrapperReadback.packedCopy m out source) out=readI32 m source:=by
    simpa only[Nat.add_zero] using low
  exact ⟨lo.trans h0,high.trans h1⟩

private theorem advanced_eq (p:Layout) :
    advancedMemory p=AllocateLayoutWrapperReadback.packedCopy (droppedFourMemory p) p.slice.toNat (dropFourOut p).toNat:=by
  simp only[advancedMemory,advancedPacked,AllocateLayoutWrapperReadback.packedCopy,writeI64]

theorem advanced_low (p:Layout) (hn:Native p) :
    readI32 (advancedMemory p) p.slice.toNat=payloadPointer p := by
  have hd:=droppedFour_spec p hn
  have words:=droppedFour_words p hn
  have bound:p.slice.toNat+8≤(droppedFourMemory p).byteSize:=by rw[hd.2.1];exact hn.sliceBound
  have result:=copied_words (droppedFourMemory p) p.slice.toNat (dropFourOut p).toNat (payloadPointer p) (remaining p) hd.1 bound words.1 words.2
  rw[advanced_eq p]
  exact result.1

theorem advanced_high (p:Layout) (hn:Native p) :
    readI32 (advancedMemory p) (p.slice.toNat+4)=remaining p := by
  have hd:=droppedFour_spec p hn
  have words:=droppedFour_words p hn
  have bound:p.slice.toNat+8≤(droppedFourMemory p).byteSize:=by rw[hd.2.1];exact hn.sliceBound
  have result:=copied_words (droppedFourMemory p) p.slice.toNat (dropFourOut p).toNat (payloadPointer p) (remaining p) hd.1 bound words.1 words.2
  rw[advanced_eq p]
  exact result.2

theorem advanced_words (p:Layout) (hn:Native p) :
    readI32 (advancedMemory p) p.slice.toNat=payloadPointer p ∧
    readI32 (advancedMemory p) (p.slice.toNat+4)=remaining p := ⟨advanced_low p hn,advanced_high p hn⟩

theorem length_words (p:Layout) (hn:Native p) :
    readI32 (lengthMemory p) (lengthOut p).toNat=0 ∧readI32 (lengthMemory p) ((lengthOut p).toNat+4)=count p := by
  have ha:=advancedMemory_spec p hn
  have add:(lengthOut p).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  have e:=scratch_end p hn
  have bound:(lengthOut p).toNat+8≤(advancedMemory p).byteSize:=by rw[add,ha.2.1];have h:=hn.spBound;omega
  exact StateDecodePrefixLeaves.recordMemory_words (advancedMemory p) (lengthOut p) (count p) ha.1 bound

theorem takenPayload_words (p:Layout) (hn:Native p) :
    readI32 (takenPayloadMemory p) (takePayloadOut p).toNat=payloadPointer p ∧
    readI32 (takenPayloadMemory p) ((takePayloadOut p).toNat+4)=count p := by
  have hl:=lengthMemory_spec p hn
  have add:(takePayloadOut p).toNat=(scratch p).toNat+16:=scratch_add p hn 16 (by omega)
  have e:=scratch_end p hn
  have bound:(takePayloadOut p).toNat+8≤(lengthMemory p).byteSize:=by rw[add,hl.2.1];have h:=hn.spBound;omega
  exact StateDecodeSlices.finalMemory_words false (lengthMemory p) (takePayloadOut p) (payloadPointer p) (remaining p) (count p) hl.1 bound
end WNear.Proofs.StateDecodePrefix
