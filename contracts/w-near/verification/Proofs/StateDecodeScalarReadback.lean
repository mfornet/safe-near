import Proofs.StateDecodeScalarMemory
import NearVM.MemoryListWordRules
import Proofs.AllocateLayoutWrapperReadback

/-! Accepted scalar caches read the original payload, independently of user output aliases. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic

theorem lowValue_eq (wide : Bool) (p : Layout) (hn : Native wide p) :
    lowValue wide p=readI64 p.memory p.pointer.toNat := by
  have ht:=takenMemory_spec wide p hn
  have hb:=scratch_spans wide p hn
  have bound:(wordOut wide p).toNat+(StateDecodeWords.widthNat wide+1)≤(takenMemory wide p).byteSize:=by
    rw[ht.2.1];exact Nat.le_trans hb.2.1 hn.spBound
  have word:=StateDecodeWords.finalMemory_low wide (takenMemory wide p) (wordOut wide p) p.pointer ht.1 bound (wordOut_high_nat wide p hn)
  have addr:(wordOut wide p).toNat+1=(scratch p).toNat+(if wide then 17 else 25):=by
    rw[wordOut_nat wide p hn]
    cases wide <;> simp
  have one:lowValue wide p=readI64 (takenMemory wide p) p.pointer.toNat:=by
    change readI64 (wordMemory wide p) _=_
    rw[←addr]
    exact word
  rw[one]
  apply readI64_congr_bytes
  intro i hi
  exact ht.2.2.2 _ (by have h:=hn.pointerAbove;omega)

theorem highValue_eq (p : Layout) (hn : Native true p) :
    highValue p=readI64 p.memory (p.pointer.toNat+8) := by
  have ht:=takenMemory_spec true p hn
  have hb:=scratch_spans true p hn
  have bound:(wordOut true p).toNat+17≤(takenMemory true p).byteSize:=by
    rw[ht.2.1];exact Nat.le_trans hb.2.1 hn.spBound
  have ha:=wordOut_high_nat true p hn rfl
  have word:=StateDecodeWords.finalMemory_high (takenMemory true p) (wordOut true p) p.pointer ht.1 bound ha
  have addr:(wordOut true p).toNat+9=(scratch p+25).toNat:=by
    have hs:(scratch p+25).toNat=(scratch p).toNat+25:=scratch_add true p hn 25 (by omega)
    rw[wordOut_nat true p hn,hs]
    simp
  have first:highValue p=readI64 (StateDecodeWords.lowMemory (takenMemory true p) (wordOut true p) p.pointer) (p.pointer+8).toNat:=by
    change readI64 (wordMemory true p) _=_
    rw[←addr]
    exact word
  have pointerAdd:(p.pointer+8).toNat=p.pointer.toNat+8:=by
    apply StorePairAddresses.add_eight
    have hp:=hn.payloadBound
    have hw:=hn.memoryWidth
    change p.pointer.toNat+16≤p.memory.byteSize at hp
    omega
  rw[first,pointerAdd]
  have hLow:(wordOut true p).toNat+1+8≤(takenMemory true p).byteSize:=by omega
  have low:=writeI64_spec (takenMemory true p) ((wordOut true p).toNat+1)
    (readI64 (takenMemory true p) p.pointer.toNat) ht.1 hLow
  apply readI64_congr_bytes
  intro i hi
  have he:=scratch_end true p hn
  have ho:=wordOut_nat true p hn
  simp only [ite_true] at ho
  have hp:=hn.pointerAbove
  have no:¬((wordOut true p).toNat+1≤p.pointer.toNat+8+i ∧p.pointer.toNat+8+i<(wordOut true p).toNat+1+8):=by omega
  have bytes:(StateDecodeWords.lowMemory (takenMemory true p) (wordOut true p) p.pointer).read8 (p.pointer.toNat+8+i)=
      (takenMemory true p).read8 (p.pointer.toNat+8+i):=by
    change (writeI64 _ _ _).read8 _=_
    rw[low.2.2.2]
    exact ite_eq_right no
  exact bytes.trans (ht.2.2.2 _ (by omega))

theorem dropped_words (wide : Bool) (p : Layout) (hn : Native wide p) :
    readI32 (droppedMemory wide p) (dropOut wide p).toNat=p.pointer+width wide ∧
    readI32 (droppedMemory wide p) ((dropOut wide p).toNat+4)=p.length-width wide := by
  have hw:=wordMemory_spec wide p hn
  have hb:=scratch_spans wide p hn
  have bound:(dropOut wide p).toNat+8≤(wordMemory wide p).byteSize:=by rw[hw.2.1];exact Nat.le_trans hb.2.2 hn.spBound
  exact StateDecodeSlices.finalMemory_words true (wordMemory wide p) (dropOut wide p) p.pointer p.length (width wide) hw.1 bound

theorem dropValue_bytes (wide : Bool) (p : Layout) (hn : Native wide p) (i : Nat) (hi : i<8) :
    UInt8.ofNat ((dropValue wide p).toNat >>> (8*i))=
      if i<4 then UInt8.ofNat ((p.pointer+width wide).toNat >>> (8*i))
      else UInt8.ofNat ((p.length-width wide).toNat >>> (8*(i-4))) := by
  have hw:=wordMemory_spec wide p hn
  have hb:=scratch_spans wide p hn
  have bound:(dropOut wide p).toNat+8≤(wordMemory wide p).byteSize:=by rw[hw.2.1];exact Nat.le_trans hb.2.2 hn.spBound
  have spec:=StateDecodeSlices.finalMemory_spec true (wordMemory wide p) (dropOut wide p) p.pointer p.length (width wide) hw.1 bound
  have addr:(scratch p).toNat+(if wide then 0 else 8)=(dropOut wide p).toNat:=(dropOut_nat wide p hn).symm
  unfold dropValue
  rw [addr,AllocateLayoutWrapperReadback.readI64_byte _ _ i hi]
  change (StateDecodeSlices.finalMemory true (wordMemory wide p) (dropOut wide p) p.pointer p.length (width wide)).read8 _=_
  rw[spec.2.2.2]
  simp only [StateDecodeSlices.lowWord,StateDecodeSlices.highWord,ite_true]
  by_cases h:i<4
  · have yes:(dropOut wide p).toNat≤(dropOut wide p).toNat+i ∧ (dropOut wide p).toNat+i<(dropOut wide p).toNat+4:=by omega
    simp only [yes,and_self,ite_true,h,Nat.add_sub_cancel_left]
  · have no:¬((dropOut wide p).toNat≤(dropOut wide p).toNat+i ∧ (dropOut wide p).toNat+i<(dropOut wide p).toNat+4):=by omega
    have yes:(dropOut wide p).toNat+4≤(dropOut wide p).toNat+i ∧ (dropOut wide p).toNat+i<(dropOut wide p).toNat+8:=by omega
    simp only [ite_eq_right no,yes,and_self,ite_true,h,ite_false]
    congr 3
    omega

end WNear.Proofs.StateDecodeScalar
