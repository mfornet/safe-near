import Proofs.StateDispatchLengthOuterResult
import Proofs.StateDispatchLengthMemory

/-! Byte frames for the length query, including its sequential borrow and release
writes. These frames transfer original allocator and register inputs across f524. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 acquiredMemory highMemory lowMemory finalMemory

private theorem word_outside (m : Memory) (a : Nat) (v : UInt32)
    (hw : m.wf) (hb : a+4≤m.byteSize) (j : Nat) (hj : j<a ∨ a+4≤j) :
    (writeI32 m a v).read8 j=m.read8 j := by
  rw [(writeI32_spec m a v hw hb).2.2.2 j]
  exact ite_eq_right (by omega)

theorem lowMemory_footprint (p : Layout) (hw : p.memory.wf)
    (hc : 1074904+4≤p.memory.byteSize) (hs : (scratch p).toNat+16≤p.memory.byteSize) :
    (lowMemory p).wf ∧ (lowMemory p).byteSize=p.memory.byteSize ∧
    (lowMemory p).max=p.memory.max ∧
    ∀ j, (j<(scratch p).toNat ∨ (scratch p).toNat+16≤j) →
      (j<1074904 ∨ 1074904+4≤j) → (lowMemory p).read8 j=p.memory.read8 j := by
  have ac := acquiredMemory_specs p hw hc (by omega)
  have hi := highMemory_specs p ac.1 (by rw [ac.2.1];exact hs)
  have lo := lowMemory_specs p hi.1 (by rw [hi.2.1,ac.2.1];omega)
  refine ⟨lo.1,lo.2.1.trans (hi.2.1.trans ac.2.1),lo.2.2.trans (hi.2.2.trans ac.2.2),?_⟩
  intro j hj hcell
  have a := writeI32_spec p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904) hw hc
  have b := writeI32_spec (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904))
    ((scratch p).toNat+4) 1074904 a.1 (by rw [a.2.1];omega)
  have c := writeI32_spec (writeI32 (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904))
    ((scratch p).toNat+4) 1074904) (scratch p).toNat 1074908 b.1 (by rw [b.2.1,a.2.1];omega)
  unfold lowMemory
  rw [word_outside _ _ _ hi.1 (by rw [hi.2.1,ac.2.1];omega) j (by omega)]
  unfold highMemory
  rw [word_outside _ _ _ ac.1 (by rw [ac.2.1];omega) j (by omega)]
  unfold acquiredMemory ValueReturnAcquire.recordMemory
  change (writeI32 (writeI32 (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904))
    ((scratch p).toNat+4) 1074904) (scratch p).toNat 1074908).read8 j=p.memory.read8 j
  rw [c.2.2.2 j,ite_eq_right (by omega),b.2.2.2 j,ite_eq_right (by omega),a.2.2.2 j,ite_eq_right (by omega)]

theorem finalMemory_footprint (p : Layout) (hw : p.memory.wf)
    (hc : 1074904+4≤p.memory.byteSize) (hs : (scratch p).toNat+16≤p.memory.byteSize)
    (hr : (counter p).toNat+4≤p.memory.byteSize) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧
    (finalMemory p).max=p.memory.max ∧
    ∀ j, (j<(scratch p).toNat ∨ (scratch p).toNat+16≤j) →
      (j<1074904 ∨ 1074904+4≤j) →
      (j<(counter p).toNat ∨ (counter p).toNat+4≤j) →
      (finalMemory p).read8 j=p.memory.read8 j := by
  have lo := lowMemory_footprint p hw hc hs
  have hb : (counter p).toNat+4≤(lowMemory p).byteSize := by rw [lo.2.1];exact hr
  have rel := writeI32_spec (lowMemory p) (counter p).toNat
    (readI32 (lowMemory p) (counter p).toNat+4294967295) lo.1 hb
  unfold finalMemory
  refine ⟨rel.1,rel.2.1.trans lo.2.1,rel.2.2.1.trans lo.2.2.1,?_⟩
  intro j hj hcell hrel
  rw [word_outside _ _ _ lo.1 hb j hrel]
  exact lo.2.2.2 j hj hcell
end WNear.Proofs.StateDispatchLength

namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 inputMemory

theorem outputMemory_footprint (p : Layout) (value : UInt64) (hw : p.memory.wf)
    (hm : p.inner.memory=inputMemory p)
    (hi : (scratch p).toNat+16≤p.memory.byteSize)
    (hs : (StateDispatchLength.scratch p.inner).toNat+16≤p.memory.byteSize)
    (hc : 1074904+4≤p.memory.byteSize)
    (hr : (StateDispatchLength.counter p.inner).toNat+4≤p.memory.byteSize)
    (ho : p.out.toNat+16≤p.memory.byteSize) :
    (StateDispatchLengthOuterTail.finalMemory (StateDispatchLength.finalMemory p.inner) p.out value).wf ∧ (StateDispatchLengthOuterTail.finalMemory (StateDispatchLength.finalMemory p.inner) p.out value).byteSize=p.memory.byteSize ∧
    (StateDispatchLengthOuterTail.finalMemory (StateDispatchLength.finalMemory p.inner) p.out value).max=p.memory.max ∧
    ∀ j, (j<(scratch p).toNat ∨ (scratch p).toNat+16≤j) →
      (j<(StateDispatchLength.scratch p.inner).toNat ∨ (StateDispatchLength.scratch p.inner).toNat+16≤j) →
      (j<1074904 ∨ 1074904+4≤j) →
      (j<(StateDispatchLength.counter p.inner).toNat ∨ (StateDispatchLength.counter p.inner).toNat+4≤j) →
      (j<p.out.toNat ∨ p.out.toNat+16≤j) →
      (StateDispatchLengthOuterTail.finalMemory (StateDispatchLength.finalMemory p.inner) p.out value).read8 j=p.memory.read8 j := by
  have inp := writeI64_spec p.memory ((scratch p).toNat+8) p.register hw (by omega)
  have iw : p.inner.memory.wf := by rw [hm];unfold inputMemory;exact inp.1
  have ib : p.inner.memory.byteSize=p.memory.byteSize := by rw [hm];unfold inputMemory;exact inp.2.1
  have im : p.inner.memory.max=p.memory.max := by rw [hm];unfold inputMemory;exact inp.2.2.1
  have fin := StateDispatchLength.finalMemory_footprint p.inner iw
    (by rw [ib];exact hc) (by rw [ib];exact hs) (by rw [ib];exact hr)
  have out := StateDispatchLengthOuterTail.finalMemory_spec (StateDispatchLength.finalMemory p.inner)
    p.out value fin.1 (by rw [fin.2.1,ib];exact ho)
  refine ⟨out.1,out.2.1.trans (fin.2.1.trans ib),out.2.2.1.trans (fin.2.2.1.trans im),?_⟩
  intro j hj hs hc hr ho
  rw [out.2.2.2.2.2 j ho,fin.2.2.2 j hs hc hr,hm]
  unfold inputMemory
  rw [inp.2.2.2 j,ite_eq_right (by omega)]

theorem resultMemory_footprint (s : Store NearState) (p : Layout) (hw : p.memory.wf)
    (hm : p.inner.memory=inputMemory p)
    (hi : (scratch p).toNat+16≤p.memory.byteSize)
    (hs : (StateDispatchLength.scratch p.inner).toNat+16≤p.memory.byteSize)
    (hc : 1074904+4≤p.memory.byteSize)
    (hr : (StateDispatchLength.counter p.inner).toNat+4≤p.memory.byteSize)
    (ho : p.out.toNat+16≤p.memory.byteSize) :
    (resultMemory s p).wf ∧ (resultMemory s p).byteSize=p.memory.byteSize ∧
    (resultMemory s p).max=p.memory.max ∧
    ∀ j, (j<(scratch p).toNat ∨ (scratch p).toNat+16≤j) →
      (j<(StateDispatchLength.scratch p.inner).toNat ∨ (StateDispatchLength.scratch p.inner).toNat+16≤j) →
      (j<1074904 ∨ 1074904+4≤j) →
      (j<(StateDispatchLength.counter p.inner).toNat ∨ (StateDispatchLength.counter p.inner).toNat+4≤j) →
      (j<p.out.toNat ∨ p.out.toNat+16≤j) →
      (resultMemory s p).read8 j=p.memory.read8 j :=
  outputMemory_footprint p (resultValue s p) hw hm hi hs hc hr ho

end WNear.Proofs.StateDispatchLengthOuter
