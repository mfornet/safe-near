import Proofs.StateReadStorageOuterSetup
import Proofs.StateDispatchLengthOuterFootprint

/-! Concrete borrow record readbacks from original bounds. Neither the selected
pointer nor the release counter is assumed as a future memory observation. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 StateDispatchLength.acquiredMemory StateDispatchLength.highMemory StateDispatchLength.lowMemory StateDispatchLength.borrowed

theorem borrow_shapes (p : Layout) (hn : Native p) :
    (StateDispatchLength.acquiredMemory (storageLayout p)).wf ∧
    (StateDispatchLength.acquiredMemory (storageLayout p)).byteSize=p.memory.byteSize ∧
    (StateDispatchLength.highMemory (storageLayout p)).wf ∧
    (StateDispatchLength.highMemory (storageLayout p)).byteSize=p.memory.byteSize ∧
    (StateDispatchLength.lowMemory (storageLayout p)).wf ∧
    (StateDispatchLength.lowMemory (storageLayout p)).byteSize=p.memory.byteSize := by
  have prep := setup_spec p hn
  have bounds := setup_native_bounds p hn
  change (StateDispatchLength.scratch (storageLayout p)).toNat+16≤(storageLayout p).memory.byteSize ∧
    1074904+4≤(storageLayout p).memory.byteSize at bounds
  have ac := StateDispatchLength.acquiredMemory_specs (storageLayout p) prep.1 bounds.2 (by omega)
  have hs : (StateDispatchLength.scratch (storageLayout p)).toNat+16≤
      (StateDispatchLength.acquiredMemory (storageLayout p)).byteSize := by rw [ac.2.1];exact bounds.1
  have hi := StateDispatchLength.highMemory_specs (storageLayout p) ac.1 hs
  have ls : (StateDispatchLength.scratch (storageLayout p)).toNat+12≤
      (StateDispatchLength.highMemory (storageLayout p)).byteSize := by rw [hi.2.1,ac.2.1];omega
  have lo := StateDispatchLength.lowMemory_specs (storageLayout p) hi.1 ls
  exact ⟨ac.1,ac.2.1.trans prep.2.1,hi.1,hi.2.1.trans (ac.2.1.trans prep.2.1),lo.1,
    lo.2.1.trans (hi.2.1.trans (ac.2.1.trans prep.2.1))⟩

theorem borrowed_eq (p : Layout) (hn : Native p) : StateDispatchLength.borrowed (storageLayout p)=1074908 := by
  let q := (storageLayout p)
  let b := (StateDispatchLength.scratch q).toNat
  let m1 := writeI32 q.memory 1074904 (ValueReturnAcquire.nextCount q.memory 1074904)
  let m2 := writeI32 m1 (b+4) 1074904
  have prep := setup_spec p hn
  have bounds := setup_native_bounds p hn
  change (StateDispatchLength.scratch (storageLayout p)).toNat+16≤(storageLayout p).memory.byteSize ∧
    1074904+4≤(storageLayout p).memory.byteSize at bounds
  have b0 : b+16≤q.memory.byteSize := by simpa only [b,q] using bounds.1
  have a := writeI32_spec q.memory 1074904 (ValueReturnAcquire.nextCount q.memory 1074904) prep.1 bounds.2
  have hb : b+4+4≤m1.byteSize := by rw [show m1.byteSize=q.memory.byteSize from a.2.1];omega
  have c := writeI32_spec m1 (b+4) 1074904 a.1 hb
  have lowBound : b+4≤m2.byteSize := by rw [show m2.byteSize=m1.byteSize from c.2.1,show m1.byteSize=q.memory.byteSize from a.2.1];omega
  have low := PanicAllocateReadback.read_write_self m2 b 1074908 c.1 lowBound
  have shapes := borrow_shapes p hn
  have highBound : b+12+4≤(StateDispatchLength.acquiredMemory q).byteSize := by
    rw [show (StateDispatchLength.acquiredMemory q).byteSize=p.memory.byteSize from shapes.2.1]
    have nums := stack_numbers p hn
    have bs : b=p.sp548.toNat-48 := by simpa only [b,q,StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
    rw [bs];have := hn.spLower;have := hn.spBound;omega
  have high := PanicAllocateReadback.read_write_frame (StateDispatchLength.acquiredMemory q) b (b+12)
    (readI32 (StateDispatchLength.acquiredMemory q) (b+4)) shapes.1 highBound (Or.inl (by omega))
  unfold StateDispatchLength.borrowed StateDispatchLength.highMemory
  change readI32 (writeI32 (StateDispatchLength.acquiredMemory q) (b+12) _) b=1074908
  rw [high]
  simpa only [StateDispatchLength.acquiredMemory,ValueReturnAcquire.recordMemory,q,m2,m1,b,
    show (1074904:UInt32)+4=1074908 by decide] using low

theorem low_counter_record (p : Layout) (hn : Native p) :
    readI32 (StateDispatchLength.lowMemory (storageLayout p))
      ((StateDispatchLength.scratch (storageLayout p)).toNat+12)=1074904 := by
  let q := (storageLayout p)
  let b := (StateDispatchLength.scratch q).toNat
  let m1 := writeI32 q.memory 1074904 (ValueReturnAcquire.nextCount q.memory 1074904)
  let m2 := writeI32 m1 (b+4) 1074904
  have prep := setup_spec p hn
  have bounds := setup_native_bounds p hn
  change (StateDispatchLength.scratch (storageLayout p)).toNat+16≤(storageLayout p).memory.byteSize ∧
    1074904+4≤(storageLayout p).memory.byteSize at bounds
  have b0 : b+16≤q.memory.byteSize := by simpa only [b,q] using bounds.1
  have shapes := borrow_shapes p hn
  have a := writeI32_spec q.memory 1074904 (ValueReturnAcquire.nextCount q.memory 1074904) prep.1 bounds.2
  have bnd : b+4+4≤m1.byteSize := by rw [show m1.byteSize=q.memory.byteSize from a.2.1];omega
  have c := writeI32_spec m1 (b+4) 1074904 a.1 bnd
  have lowBound : b+4≤m2.byteSize := by rw [show m2.byteSize=m1.byteSize from c.2.1,show m1.byteSize=q.memory.byteSize from a.2.1];omega
  have saved := PanicAllocateReadback.read_write_self m1 (b+4) 1074904 a.1 bnd
  have frame := PanicAllocateReadback.read_write_frame m2 (b+4) b 1074908 c.1 lowBound (Or.inr (by omega))
  have acRead : readI32 (StateDispatchLength.acquiredMemory q) (b+4)=1074904 := by
    have eq := frame.trans saved
    simpa only [StateDispatchLength.acquiredMemory,ValueReturnAcquire.recordMemory,q,m2,m1,b,
      show (1074904:UInt32)+4=1074908 by decide] using eq
  have nums := stack_numbers p hn
  have bs : b=p.sp548.toNat-48 := by simpa only [b,q,StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  have highBound : b+12+4≤(StateDispatchLength.acquiredMemory q).byteSize := by
    rw [show (StateDispatchLength.acquiredMemory q).byteSize=p.memory.byteSize from shapes.2.1,bs]
    have := hn.spLower;have := hn.spBound;omega
  have high := PanicAllocateReadback.read_write_self (StateDispatchLength.acquiredMemory q) (b+12)
    (readI32 (StateDispatchLength.acquiredMemory q) (b+4)) shapes.1 highBound
  have finalBound : b+8+4≤(StateDispatchLength.highMemory q).byteSize := by
    rw [show (StateDispatchLength.highMemory q).byteSize=p.memory.byteSize from shapes.2.2.2.1,bs]
    have := hn.spLower;have := hn.spBound;omega
  have last := PanicAllocateReadback.read_write_frame (StateDispatchLength.highMemory q) (b+12) (b+8)
    (StateDispatchLength.borrowed q) shapes.2.2.1 finalBound (Or.inr (by omega))
  unfold StateDispatchLength.lowMemory
  have highRead : readI32 (StateDispatchLength.highMemory q) (b+12)=1074904 := by
    simpa only [StateDispatchLength.highMemory] using high.trans acRead
  exact last.trans highRead

theorem release_address (p : Layout) (hn : Native p) :
    (((StateDispatchLength.scratch (storageLayout p))+8)|||4).toNat=
      (StateDispatchLength.scratch (storageLayout p)).toNat+12 := by
  let b := StateDispatchLength.scratch (storageLayout p)
  have nums := stack_numbers p hn
  have bs : b.toNat=p.sp548.toNat-48 := by
    simpa only [b,StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  have low := hn.spLower
  have upper := p.sp548.toNat_lt
  have aligned := hn.aligned
  have bm : b.toNat%16=0 := by rw [bs];omega
  have hn8 : (b+8).toNat=b.toNat+8 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    rw [bs]
    omega
  rw [UInt32.toNat_or,hn8]
  change (b.toNat+8)|||4=b.toNat+12
  have quotient : b.toNat=16*(b.toNat/16) := by omega
  rw [quotient]
  have h8 := Nat.two_pow_add_eq_or_of_lt (i:=4) (b:=8) (by decide) (b.toNat/16)
  have h12 := Nat.two_pow_add_eq_or_of_lt (i:=4) (b:=12) (by decide) (b.toNat/16)
  change (16*(b.toNat/16)+8)|||4=16*(b.toNat/16)+12
  rw [h8,Nat.or_assoc,show (8:Nat)|||4=12 by decide,←h12]

theorem counter_eq (p : Layout) (hn : Native p) : StateDispatchLength.counter (storageLayout p)=1074904 := by
  unfold StateDispatchLength.counter
  rw [release_address p hn]
  exact low_counter_record p hn

theorem low_static_word (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.sp548.toNat≤address) (hc : address+4≤1074904 ∨ 1074908≤address) :
    readI32 (StateDispatchLength.lowMemory (storageLayout p)) address=readI32 p.memory address := by
  have prep := setup_spec p hn
  have bounds := setup_native_bounds p hn
  change (StateDispatchLength.scratch (storageLayout p)).toNat+16≤(storageLayout p).memory.byteSize ∧
    1074904+4≤(storageLayout p).memory.byteSize at bounds
  have footprint := StateDispatchLength.lowMemory_footprint (storageLayout p) prep.1 bounds.2 bounds.1
  have nums := stack_numbers p hn
  have low := hn.spLower
  have b : (StateDispatchLength.scratch (storageLayout p)).toNat=p.sp548.toNat-48 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  have first : readI32 (StateDispatchLength.lowMemory (storageLayout p)) address=
      readI32 (storageLayout p).memory address := by
    apply readI32_congr_bytes
    intro i hi
    apply footprint.2.2.2
    · right;rw [b];omega
    · omega
  exact first.trans (setup_word p hn address ha)

theorem selected_eq (p : Layout) (hn : Native p) : StateDispatchLength.selected (storageLayout p)=1074908 := by
  have above : p.sp548.toNat≤1074908 := by have := hn.staticAbove;omega
  have word := (low_static_word p hn 1074908 above (Or.inr (by decide))).trans (Eq.refl _)
  have nonzero : readI32 (StateDispatchLength.lowMemory (storageLayout p)) 1074908≠0 := by
    rw [word];exact hn.register.receiverNonzero
  unfold StateDispatchLength.selected
  rw [borrowed_eq p hn]
  simp only [show (1074908:UInt32).toNat=1074908 by decide,ite_eq_left nonzero]
end WNear.Proofs.StateReadStorageOuter
