import Proofs.StateReadStorageOuterFootprint

/-! Actual459 increments the shared zero counter and releases it back to zero. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 StateDispatchLength.acquiredMemory StateDispatchLength.highMemory StateDispatchLength.lowMemory
theorem low_counter_value (p : Layout) (hn : Native p) :
    readI32 (StateDispatchLength.lowMemory (storageLayout p)) 1074904=1 := by
  let q := storageLayout p
  let b := (StateDispatchLength.scratch q).toNat
  let m1 := writeI32 q.memory 1074904 (ValueReturnAcquire.nextCount q.memory 1074904)
  let m2 := writeI32 m1 (b+4) 1074904
  have prep := setup_spec p hn
  have bounds := setup_native_bounds p hn
  change (StateDispatchLength.scratch (storageLayout p)).toNat+16≤(storageLayout p).memory.byteSize ∧ 1074908≤(storageLayout p).memory.byteSize at bounds
  have shapes := borrow_shapes p hn
  have zero : readI32 q.memory 1074904=0 :=
    (setup_word p hn 1074904 (by have := hn.staticAbove;omega)).trans hn.register.counterZero
  have next : ValueReturnAcquire.nextCount q.memory 1074904=1 := by
    simp only [ValueReturnAcquire.nextCount,show (1074904:UInt32).toNat=1074904 by decide,zero]
    rfl
  have nums := stack_numbers p hn
  have bs : b=p.sp548.toNat-48 := by simpa only [b,q,StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  have bb : b+16≤q.memory.byteSize := by simpa only [b,q] using bounds.1
  have sep : b+16≤1074904 := by rw [bs];have := hn.spLower;have := hn.staticAbove;omega
  have a := writeI32_spec q.memory 1074904 (ValueReturnAcquire.nextCount q.memory 1074904) prep.1 bounds.2
  have bnd : b+4+4≤m1.byteSize := by rw [show m1.byteSize=q.memory.byteSize from a.2.1];omega
  have c := writeI32_spec m1 (b+4) 1074904 a.1 bnd
  have lowBound : b+4≤m2.byteSize := by rw [show m2.byteSize=m1.byteSize from c.2.1,show m1.byteSize=q.memory.byteSize from a.2.1];omega
  have initial := PanicAllocateReadback.read_write_self q.memory 1074904 (ValueReturnAcquire.nextCount q.memory 1074904) prep.1 bounds.2
  have second := PanicAllocateReadback.read_write_frame m1 1074904 (b+4) 1074904 a.1 bnd (Or.inr (by omega))
  have third := PanicAllocateReadback.read_write_frame m2 1074904 b 1074908 c.1 lowBound (Or.inr (by omega))
  have acRead : readI32 (StateDispatchLength.acquiredMemory q) 1074904=1 := by
    have all := third.trans (second.trans (initial.trans next))
    simpa only [StateDispatchLength.acquiredMemory,ValueReturnAcquire.recordMemory,q,m2,m1,b,
      show (1074904:UInt32)+4=1074908 by decide] using all
  have highBound : b+12+4≤(StateDispatchLength.acquiredMemory q).byteSize := by
    rw [show (StateDispatchLength.acquiredMemory q).byteSize=p.memory.byteSize from shapes.2.1,bs]
    have := hn.spLower;have := hn.spBound;omega
  have fourth := PanicAllocateReadback.read_write_frame (StateDispatchLength.acquiredMemory q) 1074904 (b+12)
    (readI32 (StateDispatchLength.acquiredMemory q) (b+4)) shapes.1 highBound (Or.inr (by omega))
  have hiRead : readI32 (StateDispatchLength.highMemory q) 1074904=1 := by
    simpa only [StateDispatchLength.highMemory] using fourth.trans acRead
  have lastBound : b+8+4≤(StateDispatchLength.highMemory q).byteSize := by
    rw [show (StateDispatchLength.highMemory q).byteSize=p.memory.byteSize from shapes.2.2.2.1,bs]
    have := hn.spLower;have := hn.spBound;omega
  have fifth := PanicAllocateReadback.read_write_frame (StateDispatchLength.highMemory q) 1074904 (b+8)
    (StateDispatchLength.borrowed q) shapes.2.2.1 lastBound (Or.inr (by omega))
  unfold StateDispatchLength.lowMemory
  exact fifth.trans hiRead

theorem storage_counter_restored (p : Layout) (hn : Native p) :
    readI32 (StateDispatchLength.finalMemory (storageLayout p)) 1074904=0 := by
  have shapes := borrow_shapes p hn
  have bound : 1074904+4≤(StateDispatchLength.lowMemory (storageLayout p)).byteSize := by
    rw [shapes.2.2.2.2.2];have := hn.register.threadBound;omega
  have read := PanicAllocateReadback.read_write_self (StateDispatchLength.lowMemory (storageLayout p)) 1074904
    (readI32 (StateDispatchLength.lowMemory (storageLayout p)) 1074904+4294967295) shapes.2.2.2.2.1 bound
  unfold StateDispatchLength.finalMemory
  rw [counter_eq p hn]
  change readI32 (writeI32 (StateDispatchLength.lowMemory (storageLayout p)) 1074904
    (readI32 (StateDispatchLength.lowMemory (storageLayout p)) 1074904+4294967295)) 1074904=0
  rw [read,low_counter_value p hn]
  decide


end WNear.Proofs.StateReadStorageOuter
