import Proofs.StateDecodeScalarNative
import Proofs.AllocateSplitReadback

/-! Scratch-only child outputs preserve original scalar descriptors and payload. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic

theorem takenMemory_spec (wide : Bool) (p : Layout) (hn : Native wide p) :
    (takenMemory wide p).wf ∧ (takenMemory wide p).byteSize=p.memory.byteSize ∧
    (takenMemory wide p).max=p.memory.max ∧
    ∀j,p.sp.toNat≤j→(takenMemory wide p).read8 j=p.memory.read8 j := by
  have span:=scratch_spans wide p hn
  have hb:(takeOut wide p).toNat+8≤p.memory.byteSize:=Nat.le_trans span.1 hn.spBound
  have hs:=StateDecodeSlices.finalMemory_spec false p.memory (takeOut wide p) p.pointer p.length (width wide) hn.wf hb
  refine ⟨hs.1,hs.2.1,hs.2.2.1,?_⟩
  intro j hj
  unfold takenMemory
  rw [hs.2.2.2 j]
  have no1:¬((takeOut wide p).toNat≤j ∧ j<(takeOut wide p).toNat+4):=by omega
  have no2:¬((takeOut wide p).toNat+4≤j ∧ j<(takeOut wide p).toNat+8):=by omega
  simp only [ite_eq_right no1,ite_eq_right no2]

theorem wordOut_high_nat (wide : Bool) (p : Layout) (hn : Native wide p) :
    wide=true→(wordOut wide p+9).toNat=(wordOut wide p).toNat+9 := by
  intro h
  subst wide
  have he:=scratch_end true p hn
  have hout:=wordOut_nat true p hn
  simp only [ite_true] at hout
  have hlt:=UInt32.toNat_lt p.sp
  rw [UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  omega

theorem wordMemory_spec (wide : Bool) (p : Layout) (hn : Native wide p) :
    (wordMemory wide p).wf ∧ (wordMemory wide p).byteSize=p.memory.byteSize ∧
    (wordMemory wide p).max=p.memory.max ∧
    ∀j,p.sp.toNat≤j→(wordMemory wide p).read8 j=p.memory.read8 j := by
  have ht:=takenMemory_spec wide p hn
  have span:=scratch_spans wide p hn
  have hb:(wordOut wide p).toNat+(StateDecodeWords.widthNat wide+1)≤(takenMemory wide p).byteSize:=by rw[ht.2.1];exact Nat.le_trans span.2.1 hn.spBound
  have ha:=wordOut_high_nat wide p hn
  have hs:=StateDecodeWords.finalMemory_spec wide (takenMemory wide p) (wordOut wide p) p.pointer ht.1 hb ha
  refine ⟨hs.1,hs.2.1.trans ht.2.1,hs.2.2.1.trans ht.2.2.1,?_⟩
  intro j hj
  have he:=scratch_end wide p hn
  have hout:=wordOut_nat wide p hn
  unfold wordMemory
  rw [hs.2.2.2 j]
  have ne:j≠(wordOut wide p).toNat:=by cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hout <;> omega
  have noHigh:¬(wide=true ∧ (wordOut wide p).toNat+9≤j ∧ j<(wordOut wide p).toNat+17):=by
    intro h
    rcases h with ⟨h,_,h⟩
    subst wide
    simp only [ite_true] at hout
    omega
  have noLow:¬((wordOut wide p).toNat+1≤j ∧ j<(wordOut wide p).toNat+9):=by
    cases wide <;> simp only [ite_true,Bool.false_eq_true,ite_false] at hout <;> omega
  simp only [ne,ite_false,ite_eq_right noHigh,ite_eq_right noLow]
  exact ht.2.2.2 j hj

theorem droppedMemory_spec (wide : Bool) (p : Layout) (hn : Native wide p) :
    (droppedMemory wide p).wf ∧ (droppedMemory wide p).byteSize=p.memory.byteSize ∧
    (droppedMemory wide p).max=p.memory.max ∧
    ∀j,p.sp.toNat≤j→(droppedMemory wide p).read8 j=p.memory.read8 j := by
  have hw:=wordMemory_spec wide p hn
  have span:=scratch_spans wide p hn
  have hb:(dropOut wide p).toNat+8≤(wordMemory wide p).byteSize:=by rw[hw.2.1];exact Nat.le_trans span.2.2 hn.spBound
  have hs:=StateDecodeSlices.finalMemory_spec true (wordMemory wide p) (dropOut wide p) p.pointer p.length (width wide) hw.1 hb
  refine ⟨hs.1,hs.2.1.trans hw.2.1,hs.2.2.1.trans hw.2.2.1,?_⟩
  intro j hj
  unfold droppedMemory
  rw [hs.2.2.2 j]
  have no1:¬((dropOut wide p).toNat≤j ∧ j<(dropOut wide p).toNat+4):=by omega
  have no2:¬((dropOut wide p).toNat+4≤j ∧ j<(dropOut wide p).toNat+8):=by omega
  simp only [ite_eq_right no1,ite_eq_right no2]
  exact hw.2.2.2 j hj

theorem taken_descriptor (wide : Bool) (p : Layout) (hn : Native wide p) :
    readI32 (takenMemory wide p) p.slice.toNat=p.pointer ∧
    readI32 (takenMemory wide p) (p.slice.toNat+4)=p.length := by
  have hs:=takenMemory_spec wide p hn
  constructor
  · calc
      _ = readI32 p.memory p.slice.toNat := by
        apply Allocate.readI32_congr_bytes
        intro i hi
        exact hs.2.2.2 _ (by have ha:=hn.sliceAbove;omega)
      _ = _ := hn.pointerRead
  · calc
      _ = readI32 p.memory (p.slice.toNat+4) := by
        apply Allocate.readI32_congr_bytes
        intro i hi
        exact hs.2.2.2 _ (by have ha:=hn.sliceAbove;omega)
      _ = _ := hn.lengthRead

theorem word_descriptor (wide : Bool) (p : Layout) (hn : Native wide p) :
    readI32 (wordMemory wide p) p.slice.toNat=p.pointer ∧
    readI32 (wordMemory wide p) (p.slice.toNat+4)=p.length := by
  have hs:=wordMemory_spec wide p hn
  constructor
  · calc
      _ = readI32 p.memory p.slice.toNat := by
        apply Allocate.readI32_congr_bytes
        intro i hi
        exact hs.2.2.2 _ (by have ha:=hn.sliceAbove;omega)
      _ = _ := hn.pointerRead
  · calc
      _ = readI32 p.memory (p.slice.toNat+4) := by
        apply Allocate.readI32_congr_bytes
        intro i hi
        exact hs.2.2.2 _ (by have ha:=hn.sliceAbove;omega)
      _ = _ := hn.lengthRead

theorem taken_words (wide : Bool) (p : Layout) (hn : Native wide p) :
    readI32 (takenMemory wide p) (takeOut wide p).toNat=p.pointer ∧
    readI32 (takenMemory wide p) ((takeOut wide p).toNat+4)=width wide := by
  have hb:=scratch_spans wide p hn
  exact StateDecodeSlices.finalMemory_words false p.memory (takeOut wide p) p.pointer p.length (width wide) hn.wf (Nat.le_trans hb.1 hn.spBound)

theorem word_status (wide : Bool) (p : Layout) (hn : Native wide p) :
    (wordMemory wide p).read8 (wordOut wide p).toNat=0 := by
  have ht:=takenMemory_spec wide p hn
  have hb:=scratch_spans wide p hn
  have bound:(wordOut wide p).toNat+(StateDecodeWords.widthNat wide+1)≤(takenMemory wide p).byteSize:=by rw[ht.2.1];exact Nat.le_trans hb.2.1 hn.spBound
  exact StateDecodeWords.finalMemory_status wide (takenMemory wide p) (wordOut wide p) p.pointer ht.1 bound (wordOut_high_nat wide p hn)

end WNear.Proofs.StateDecodeScalar
