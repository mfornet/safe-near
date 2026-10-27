import Proofs.AllocateGrowthResources
import Proofs.AllocateFlaggedMemory
import Proofs.AllocateSplitReadback

/-! Native fresh-block readbacks, before f581 invokes its second search. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 writeI64

/-- All three freshly initialized words, including the actual flags-two header. -/
theorem fresh_reads (memory : Memory) (header bytes : UInt32)
    (hw : memory.wf) (hb : header.toNat+12≤memory.byteSize) :
    readI32 (AllocateGrowth.freshMemory memory header bytes) header.toNat=((header+bytes)|||2) ∧
    readI32 (AllocateGrowth.freshMemory memory header bytes) (header.toNat+4)=0 ∧
    readI32 (AllocateGrowth.freshMemory memory header bytes) (header.toNat+8)=0 := by
  let m1 := writeI64 memory header.toNat 0
  let m2 := writeI32 m1 (header.toNat+8) 0
  have a := writeI64_spec memory header.toNat 0 hw (by omega)
  have b := writeI32_spec m1 (header.toNat+8) 0 a.1 (by rw [a.2.1];omega)
  have c := writeI32_spec m2 header.toNat ((header+bytes)|||2) b.1 (by rw [b.2.1,a.2.1];omega)
  refine ⟨PanicAllocateReadback.read_write_self m2 _ _ b.1 (by rw [b.2.1,a.2.1];omega),?_,?_⟩
  · have frame := PanicAllocateReadback.read_write_frame m2 (header.toNat+4) header.toNat ((header+bytes)|||2) b.1 (by rw [b.2.1,a.2.1];omega) (by omega)
    have frame2 := PanicAllocateReadback.read_write_frame m1 (header.toNat+4) (header.toNat+8) 0 a.1 (by rw [a.2.1];omega) (by omega)
    change readI32 (writeI32 m2 header.toNat _) (header.toNat+4)=0
    rw [frame,frame2]
    apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    rw [show m1.read8 (header.toNat+4+i)=_ from a.2.2.2 (header.toNat+4+i)]
    have inside : header.toNat≤header.toNat+4+i ∧ header.toNat+4+i<header.toNat+8 := by omega
    rw [ite_eq_left inside]
    simp
  · have frame := PanicAllocateReadback.read_write_frame m2 (header.toNat+8) header.toNat ((header+bytes)|||2) b.1 (by rw [b.2.1,a.2.1];omega) (by omega)
    change readI32 (writeI32 m2 header.toNat _) (header.toNat+8)=0
    rw [frame]
    exact PanicAllocateReadback.read_write_self m1 _ 0 a.1 (by rw [a.2.1];omega)

/-- Writing the result record below the new page preserves its fresh header. -/
theorem record_read_above (memory : Memory) (record header : UInt32) (address : Nat)
    (hw : memory.wf) (hb : record.toNat+8≤memory.byteSize)
    (ha : record.toNat+8≤address) :
    readI32 (AllocateGrowth.recordMemory memory record header) address=readI32 memory address := by
  have a := writeI32_spec memory (record.toNat+4) header hw (by omega)
  have b := PanicAllocateReadback.read_write_frame (writeI32 memory (record.toNat+4) header)
    address record.toNat 0 a.1 (by rw [a.2.1];omega) (by omega)
  have c := PanicAllocateReadback.read_write_frame memory address (record.toNat+4) header hw (by omega) (by omega)
  exact b.trans c

/-- The growth result record is below the appended page in every nonempty
original memory; the condition is on original byte bounds. -/
theorem growth_record_below (p : AllocateGrowth.Layout) (hn : AllocateGrowth.Native p) :
    p.record.toNat+8≤(AllocateGrowth.header p).toNat := by
  have bound := hn.recordBound
  have old : (AllocateGrowth.oldPages p).toNat=p.memory.size := by
    simp only [AllocateGrowth.oldPages]
    apply Nat.mod_eq_of_lt
    have h := hn.oldPagesBound
    omega
  have pages : (AllocateGrowth.oldPages p).toNat<65536 := by rw [old];exact hn.oldPagesBound
  rw [AllocateGrowth.header,AllocateGrowth.pageBytes_toNat _ pages,old]
  exact bound

/-- Fresh flags and empty links survive the actual successful growth record. -/
theorem growth_reads (p : AllocateGrowth.Layout) (hn : AllocateGrowth.Native p) :
    readI32 (AllocateGrowth.finalMemory p) (AllocateGrowth.header p).toNat=
      ((AllocateGrowth.header p+AllocateGrowth.blockBytes p)|||2) ∧
    readI32 (AllocateGrowth.finalMemory p) ((AllocateGrowth.header p).toNat+4)=0 ∧
    readI32 (AllocateGrowth.finalMemory p) ((AllocateGrowth.header p).toNat+8)=0 := by
  have grow := hn.grown_spec p
  have fresh := fresh_reads p.grown (AllocateGrowth.header p) (AllocateGrowth.blockBytes p) grow.1 grow.2.2.1
  have shape := AllocateGrowth.freshMemory_spec p.grown (AllocateGrowth.header p) (AllocateGrowth.blockBytes p) grow.1 grow.2.2.1
  have below := growth_record_below p hn
  have bound : p.record.toNat+8≤(AllocateGrowth.committedMemory p).byteSize := by
    change p.record.toNat+8≤(AllocateGrowth.freshMemory p.grown _ _).byteSize
    rw [shape.2.1]
    exact grow.2.2.2
  have frame := fun address ha => record_read_above (AllocateGrowth.committedMemory p) p.record (AllocateGrowth.header p) address shape.1 bound ha
  exact ⟨(frame _ below).trans fresh.1,(frame _ (by omega)).trans fresh.2.1,(frame _ (by omega)).trans fresh.2.2⟩

/-- The actual two f581 link writes use the saved old root, then the fresh
head obtained before either write. No simultaneous-copy interpretation is used. -/
def relinkMemory (memory : Memory) (record head : UInt32) :=
  writeI32 (writeI32 memory (record.toNat+8) (readI32 memory (record.toNat+12)))
    (record.toNat+12) head

theorem relink_spec (memory : Memory) (record head : UInt32)
    (hw : memory.wf) (hb : record.toNat+16≤memory.byteSize) :
    (relinkMemory memory record head).wf ∧
    (relinkMemory memory record head).byteSize=memory.byteSize ∧
    (relinkMemory memory record head).max=memory.max ∧
    readI32 (relinkMemory memory record head) (record.toNat+12)=head := by
  have first := writeI32_spec memory (record.toNat+8) (readI32 memory (record.toNat+12)) hw (by omega)
  have second := writeI32_spec (writeI32 memory (record.toNat+8) (readI32 memory (record.toNat+12))) (record.toNat+12) head first.1 (by rw [first.2.1];omega)
  exact ⟨second.1,second.2.1.trans first.2.1,second.2.2.1.trans first.2.2.1,
    PanicAllocateReadback.read_write_self _ _ _ first.1 (by rw [first.2.1];omega)⟩

theorem relink_read_above (memory : Memory) (record head : UInt32) (address : Nat)
    (hw : memory.wf) (hb : record.toNat+16≤memory.byteSize)
    (ha : record.toNat+16≤address) :
    readI32 (relinkMemory memory record head) address=readI32 memory address := by
  have first := writeI32_spec memory (record.toNat+8) (readI32 memory (record.toNat+12)) hw (by omega)
  have a := PanicAllocateReadback.read_write_frame (writeI32 memory (record.toNat+8) (readI32 memory (record.toNat+12)))
    address (record.toNat+12) head first.1 (by rw [first.2.1];omega) (by omega)
  have b := PanicAllocateReadback.read_write_frame memory address (record.toNat+8) (readI32 memory (record.toNat+12)) hw (by omega) (by omega)
  exact a.trans b

/-- Memory presented to the retry search, computed solely from the original
successful growth layout and the two actual f581 writes. -/
def retryMemory (p : AllocateGrowth.Layout) :=
  relinkMemory (AllocateGrowth.finalMemory p) p.record (AllocateGrowth.header p)

theorem retry_reads (p : AllocateGrowth.Layout) (hn : AllocateGrowth.Native p)
    (hb : p.record.toNat+16≤p.memory.byteSize) :
    readI32 (retryMemory p) (p.record.toNat+12)=AllocateGrowth.header p ∧
    readI32 (retryMemory p) (AllocateGrowth.header p).toNat=
      ((AllocateGrowth.header p+AllocateGrowth.blockBytes p)|||2) ∧
    readI32 (retryMemory p) ((AllocateGrowth.header p).toNat+8)=0 := by
  have shape := AllocateGrowth.finalMemory_spec p hn
  have bound : p.record.toNat+16≤(AllocateGrowth.finalMemory p).byteSize := by rw [shape.2.1];omega
  have below : p.record.toNat+16≤(AllocateGrowth.header p).toNat := by
    have h := growth_record_below p hn
    have old : (AllocateGrowth.header p).toNat=p.memory.byteSize := by
      have oldNat : (AllocateGrowth.oldPages p).toNat=p.memory.size := by
        simp only [AllocateGrowth.oldPages]
        apply Nat.mod_eq_of_lt
        have hp := hn.oldPagesBound
        omega
      rw [AllocateGrowth.header,AllocateGrowth.pageBytes_toNat _ (by rw [oldNat];exact hn.oldPagesBound),oldNat]
      rfl
    rw [old];exact hb
  have reads := growth_reads p hn
  have frame := fun address ha => relink_read_above (AllocateGrowth.finalMemory p) p.record (AllocateGrowth.header p) address shape.1 bound ha
  exact ⟨(relink_spec _ _ _ shape.1 bound).2.2.2,(frame _ below).trans reads.1,(frame _ (by omega)).trans reads.2.2⟩

end WNear.Proofs.AllocateRetry
