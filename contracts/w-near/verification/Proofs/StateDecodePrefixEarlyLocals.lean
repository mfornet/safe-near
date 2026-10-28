import Proofs.StateDecodePrefixEarlyPhases
import Proofs.StateDecodePrefixReadback

/-! Local slots and descriptor reads along the actual accepted316 prefix. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open AllocateVector (loadedFrame)
attribute [local irreducible] readI32 readI64 writeI64

theorem length_slice_high (p : Layout) (hn : Native p) :
    readI32 (lengthMemory p) (p.slice.toNat+4)=remaining p := by
  have ha:=advancedMemory_spec p hn
  have add:(lengthOut p).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  have hend:=scratch_end p hn
  have hb:(lengthOut p).toNat+8≤(advancedMemory p).byteSize:=by
    rw[add,ha.2.1];have h:=hn.spBound;omega
  have spec:=StateDecodePrefixLeaves.recordMemory_spec (advancedMemory p) (lengthOut p) (count p) ha.1 hb
  have eq:readI32 (lengthMemory p) (p.slice.toNat+4)=readI32 (advancedMemory p) (p.slice.toNat+4):=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    unfold lengthMemory
    rw[spec.2.2.2]
    have hs:=hn.sliceAbove
    have no1:¬((lengthOut p).toNat≤p.slice.toNat+4+i ∧p.slice.toNat+4+i<(lengthOut p).toNat+4):=by rw[add];omega
    have no2:¬((lengthOut p).toNat+4≤p.slice.toNat+4+i ∧p.slice.toNat+4+i<(lengthOut p).toNat+8):=by rw[add];omega
    simp only[ite_eq_right no1,ite_eq_right no2]
  exact eq.trans (advanced_high p hn)

theorem enough_reads (p : Layout) (hn : Native p) :
    readI32 (lengthMemory p) (p.slice.toNat+4)=remaining p ∧
    readI32 (lengthMemory p) ((scratch p).toNat+28)=count p := by
  have add:(lengthOut p).toNat=(scratch p).toNat+24:=scratch_add p hn 24 (by omega)
  exact ⟨length_slice_high p hn, by simpa only[add,Nat.add_assoc] using (length_words p hn).2⟩

theorem guardedPrefixFrame_locals (frame : CallFrame) (p : Layout)
    (hs : 6≤frame.locals.size) :
    (guardedPrefixFrame frame p).locals.size=frame.locals.size ∧
    (guardedPrefixFrame frame p).locals[0]?=frame.locals[0]? ∧
    (guardedPrefixFrame frame p).locals[1]?=frame.locals[1]? ∧
    (guardedPrefixFrame frame p).locals[2]?=some (.i32 (scratch p)) ∧
    (guardedPrefixFrame frame p).locals[3]?=some (.i32 p.length) := by
  simp [guardedPrefixFrame,reservedPrefixFrame,loadedFrame,Array.set!,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega]

theorem statusPrefixFrame_locals (frame : CallFrame) (p : Layout)
    (hs : 6≤frame.locals.size) :
    (statusPrefixFrame frame p).locals.size=frame.locals.size ∧
    (statusPrefixFrame frame p).locals[0]?=frame.locals[0]? ∧
    (statusPrefixFrame frame p).locals[1]?=frame.locals[1]? ∧
    (statusPrefixFrame frame p).locals[2]?=some (.i32 (scratch p)) ∧
    (statusPrefixFrame frame p).locals[3]?=some (.i32 p.length) ∧
    (statusPrefixFrame frame p).locals[4]?=some (.i64 (StateDecodePrefixLeaves.packedWord (count p))) := by
  simp [statusPrefixFrame,statusFrame,guardedPrefixFrame,reservedPrefixFrame,loadedFrame,Array.set!,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

theorem countedPrefixFrame_locals (frame : CallFrame) (p : Layout)
    (hs : 6≤frame.locals.size) :
    (countedPrefixFrame frame p).locals.size=frame.locals.size ∧
    (countedPrefixFrame frame p).locals[0]?=frame.locals[0]? ∧
    (countedPrefixFrame frame p).locals[1]?=frame.locals[1]? ∧
    (countedPrefixFrame frame p).locals[2]?=some (.i32 (scratch p)) ∧
    (countedPrefixFrame frame p).locals[3]?=some (.i32 (count p)) ∧
    (countedPrefixFrame frame p).locals[4]?=some (.i64 (StateDecodePrefixLeaves.packedWord (count p))) := by
  simp [countedPrefixFrame,countFrame,statusPrefixFrame,statusFrame,guardedPrefixFrame,reservedPrefixFrame,loadedFrame,Array.set!,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega]

theorem enoughPrefixFrame_locals (frame : CallFrame) (p : Layout)
    (hs : 6≤frame.locals.size) (hn : Native p) :
    (enoughPrefixFrame frame p).locals.size=frame.locals.size ∧
    (enoughPrefixFrame frame p).locals[0]?=frame.locals[0]? ∧
    (enoughPrefixFrame frame p).locals[1]?=frame.locals[1]? ∧
    (enoughPrefixFrame frame p).locals[2]?=some (.i32 (scratch p)) ∧
    (enoughPrefixFrame frame p).locals[3]?=some (.i32 (count p)) ∧
    (enoughPrefixFrame frame p).locals[4]?=some (.i64 (StateDecodePrefixLeaves.packedWord (count p))) ∧
    (enoughPrefixFrame frame p).locals[5]?=some (.i32 (remaining p)) := by
  have reads:=enough_reads p hn
  simp [enoughPrefixFrame,enoughFrame,countedPrefixFrame,countFrame,statusPrefixFrame,statusFrame,guardedPrefixFrame,reservedPrefixFrame,loadedFrame,Array.set!,reads.1,reads.2,show 2<frame.locals.size by omega,show 3<frame.locals.size by omega,show 4<frame.locals.size by omega,show 5<frame.locals.size by omega]

theorem prefixFrame_shapes (frame : CallFrame) (p : Layout) :
    (reservedPrefixFrame frame p).inst=frame.inst ∧
    (guardedPrefixFrame frame p).arity=frame.arity ∧
    (statusPrefixFrame frame p).height=frame.height ∧
    (countedPrefixFrame frame p).labels=frame.labels ∧
    ((enoughPrefixFrame frame p).inst=frame.inst ∧
     (enoughPrefixFrame frame p).arity=frame.arity ∧
     (enoughPrefixFrame frame p).height=frame.height ∧
     (enoughPrefixFrame frame p).labels=frame.labels) := by
  simp only [reservedPrefixFrame,guardedPrefixFrame,statusPrefixFrame,countedPrefixFrame,enoughPrefixFrame,loadedFrame,statusFrame,countFrame,enoughFrame, and_self]

end WNear.Proofs.StateDecodePrefix
