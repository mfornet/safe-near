import Proofs.AllocateLayoutWrapperReadback

/-! Exact byte footprint of685: its sixteen-byte scratch record and the
snapshot eight-byte output copy. These frames derive later allocator inputs. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
open AllocateLayoutWrapperReadback
set_option maxRecDepth 16384
set_option maxHeartbeats 600000
attribute [local irreducible] readI32 writeI32 setupMemory laidOutMemory finalMemory

theorem setup_outside (p : Layout) (hw : p.memory.wf)
    (hs : (scratch p).toNat+16≤p.memory.byteSize) (j : Nat)
    (hj : j<(scratch p).toNat ∨ (scratch p).toNat+16≤j) :
    (setupMemory p).read8 j=p.memory.read8 j := by
  have a := writeI32_spec p.memory ((scratch p).toNat+12) 1 hw (by omega)
  have bnd : (scratch p).toNat+8+4≤(alignmentMemory p).byteSize := by
    rw [show (alignmentMemory p).byteSize=p.memory.byteSize from a.2.1];omega
  have b := writeI32_spec (alignmentMemory p) ((scratch p).toNat+8) p.size a.1 bnd
  rw [setupMemory,b.2.2.2]
  rw [ite_eq_right (show ¬((scratch p).toNat+8≤j ∧ j<(scratch p).toNat+8+4) by omega)]
  rw [alignmentMemory,a.2.2.2]
  rw [ite_eq_right (show ¬((scratch p).toNat+12≤j ∧ j<(scratch p).toNat+12+4) by omega)]

theorem laidOut_footprint (p : Layout) (hw : p.memory.wf)
    (hs : (scratch p).toNat+16≤p.memory.byteSize) :
    (laidOutMemory p).wf ∧ (laidOutMemory p).byteSize=p.memory.byteSize ∧
    (laidOutMemory p).max=p.memory.max ∧
    ∀ j, (j<(scratch p).toNat ∨ (scratch p).toNat+16≤j) →
      (laidOutMemory p).read8 j=p.memory.read8 j := by
  have setup := setup_spec p hw hs
  have bound : (leafLayout p).out.toNat+8≤(leafLayout p).memory.byteSize := by
    change (scratch p).toNat+8≤(setupMemory p).byteSize
    rw [setup.2.1];omega
  have leaf := AllocateLayout.final_spec (leafLayout p) setup.1 bound
  unfold laidOutMemory
  refine ⟨leaf.1,leaf.2.1.trans setup.2.1,leaf.2.2.1.trans setup.2.2.1,?_⟩
  intro j hj
  have outside : j<(leafLayout p).out.toNat ∨ (leafLayout p).out.toNat+8≤j := by
    change j<(scratch p).toNat ∨ (scratch p).toNat+8≤j
    omega
  exact (leaf.2.2.2.2.2 j outside).trans (setup_outside p hw hs j hj)

theorem final_footprint (p : Layout) (hw : p.memory.wf)
    (hs : (scratch p).toNat+16≤p.memory.byteSize) (ho : p.out.toNat+8≤p.memory.byteSize) :
    (finalMemory p).wf ∧ (finalMemory p).byteSize=p.memory.byteSize ∧
    (finalMemory p).max=p.memory.max ∧
    ∀ j, (j<(scratch p).toNat ∨ (scratch p).toNat+16≤j) →
      (j<p.out.toNat ∨ p.out.toNat+8≤j) → (finalMemory p).read8 j=p.memory.read8 j := by
  have leaf := laidOut_footprint p hw hs
  have bound : p.out.toNat+8≤(laidOutMemory p).byteSize := by rw [leaf.2.1];exact ho
  have cp := packedCopy_spec (laidOutMemory p) p.out.toNat (scratch p).toNat leaf.1 bound
  have shape : (finalMemory p).wf ∧ (finalMemory p).byteSize=(laidOutMemory p).byteSize ∧ (finalMemory p).max=(laidOutMemory p).max := by
    simpa only [finalMemory,packedCopy] using And.intro cp.1 (And.intro cp.2.1 cp.2.2.1)
  refine ⟨shape.1,shape.2.1.trans leaf.2.1,shape.2.2.trans leaf.2.2.1,?_⟩
  intro j hj ho
  have read : (finalMemory p).read8 j=if p.out.toNat≤j ∧ j<p.out.toNat+8 then
      (laidOutMemory p).read8 ((scratch p).toNat+(j-p.out.toNat)) else (laidOutMemory p).read8 j := by
    simpa only [finalMemory,packedCopy] using cp.2.2.2 j
  rw [read,ite_eq_right (show ¬(p.out.toNat≤j ∧ j<p.out.toNat+8) by omega)]
  exact leaf.2.2.2 j hj

theorem final_size (p : Layout) (hw : p.memory.wf)
    (hs : (scratch p).toNat+16≤p.memory.byteSize) (ho : p.out.toNat+8≤p.memory.byteSize) :
    (finalMemory p).size=p.memory.size := by
  have h := (final_footprint p hw hs ho).2.1
  change (finalMemory p).size*65536=p.memory.size*65536 at h
  omega

theorem final_word_frame (p : Layout) (hw : p.memory.wf)
    (hs : (scratch p).toNat+16≤p.memory.byteSize) (ho : p.out.toNat+8≤p.memory.byteSize)
    (address : Nat)
    (hScratch : address+4≤(scratch p).toNat ∨ (scratch p).toNat+16≤address)
    (hOutput : address+4≤p.out.toNat ∨ p.out.toNat+8≤address) :
    readI32 (finalMemory p) address=readI32 p.memory address := by
  have frame := (final_footprint p hw hs ho).2.2.2
  apply LoadedValueReturnData.readI32_frame
  intro i hi
  exact frame (address+i) (by omega) (by omega)
end WNear.Proofs.AllocateLayoutWrapper
