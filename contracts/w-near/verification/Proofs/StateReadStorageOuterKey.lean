import Proofs.StateReadStorageOuterBorrow
import Proofs.ValueReturnSlice

/-! Original key bytes survive the actual548 setup and459 borrow. -/
namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic MeteredHosts
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

private theorem low_byte (p : Layout) (hn : Native p) (address : Nat)
    (ha : p.sp548.toNat≤address) (hc : address<1074904 ∨1074908≤address) :
    (StateDispatchStorage.lowMemory (storageLayout p)).read8 address=p.memory.read8 address := by
  have prep := setup_spec p hn
  have bounds := setup_native_bounds p hn
  have foot := StateDispatchLength.lowMemory_footprint (storageLayout p) prep.1 bounds.2 bounds.1
  have nums := stack_numbers p hn
  have bs : (StateDispatchLength.scratch (storageLayout p)).toNat=p.sp548.toNat-48 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  have left : address<(StateDispatchLength.scratch (storageLayout p)).toNat ∨
      (StateDispatchLength.scratch (storageLayout p)).toNat+16≤address := by
    right;rw [bs];have := hn.spLower;omega
  exact (foot.2.2.2 address left hc).trans (setup_byte p hn address ha)

private theorem packed_congr (before after : Memory) (address : Nat)
    (h : ∀ i<4,after.read8 (address+i)=before.read8 (address+i)) :
    ValueReturnDispatch.packed32 after address=ValueReturnDispatch.packed32 before address := by
  have hm : (List.range 4).map (fun i=>after.read8 (address+i))=
      (List.range 4).map (fun i=>before.read8 (address+i)) := by
    apply List.map_congr_left
    intro i hi
    exact h i (List.mem_range.mp hi)
  have hd := congrArg (fun bytes : List UInt8 => UInt64.ofNat (Memory.decodeLE bytes)) hm
  simpa only [ValueReturnDispatch.packed32,Memory.decodeLE,List.foldr_map] using hd

theorem low_input_byte (p : Layout) (hn : Native p) (i : Nat) (hi : i<8) :
    (StateDispatchStorage.lowMemory (storageLayout p)).read8 ((scratch p).toNat+8+i)=
      (setupMemory p).read8 ((scratch p).toNat+8+i) := by
  have prep := setup_spec p hn
  have bounds := setup_native_bounds p hn
  have foot := StateDispatchLength.lowMemory_footprint (storageLayout p) prep.1 bounds.2 bounds.1
  have nums := stack_numbers p hn
  have bs : (StateDispatchLength.scratch (storageLayout p)).toNat=p.sp548.toNat-48 := by
    simpa only [StateDispatchLength.scratch,StateDispatchPrefix.scratch,storageLayout] using nums.2.1
  apply foot.2.2.2
  · right;rw [bs,nums.1];have := hn.spLower;omega
  · left
    rw [nums.1]
    have := hn.spLower
    have := hn.staticAbove
    omega

theorem keyPtr_eq (p : Layout) (hn : Native p) :
    StateDispatchStorage.keyPtr (storageLayout p)=UInt64.ofNat p.keyPtr.toNat := by
  have nums := stack_numbers p hn
  have span : (scratch p).toNat+16≤p.memory.byteSize := by rw [nums.1];have := hn.spLower;have := hn.spBound;omega
  have spec := ValueReturnSlice.sliceMemory_spec p.memory (scratch p) p.keyPtr p.keyLen hn.register.allocation.wf span
  have frame := packed_congr (setupMemory p) (StateDispatchStorage.lowMemory (storageLayout p)) ((scratch p).toNat+8)
    (fun i hi=>low_input_byte p hn i (by omega))
  have addr : (storageLayout p).input.toNat=(scratch p).toNat+8 := by
    change (scratch p+8).toNat=_
    rw [UInt32.toNat_add,nums.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have := hn.spLower;have := p.sp548.toNat_lt;omega
  unfold StateDispatchStorage.keyPtr
  rw [addr,frame]
  exact spec.2.2.2.1

theorem keyLen_eq (p : Layout) (hn : Native p) :
    StateDispatchStorage.keyLen (storageLayout p)=UInt64.ofNat p.keyLen.toNat := by
  have nums := stack_numbers p hn
  have span : (scratch p).toNat+16≤p.memory.byteSize := by rw [nums.1];have := hn.spLower;have := hn.spBound;omega
  have spec := ValueReturnSlice.sliceMemory_spec p.memory (scratch p) p.keyPtr p.keyLen hn.register.allocation.wf span
  have frame := packed_congr (setupMemory p) (StateDispatchStorage.lowMemory (storageLayout p)) ((scratch p).toNat+12)
    (fun i hi=>by simpa only [←Nat.add_assoc,show (8:Nat)+4=12 by decide] using low_input_byte p hn (4+i) (by omega))
  have addr : (storageLayout p).input.toNat+4=(scratch p).toNat+12 := by
    change (scratch p+8).toNat+4=_
    rw [UInt32.toNat_add,nums.1]
    simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    have := hn.spLower;have := p.sp548.toNat_lt;omega
  unfold StateDispatchStorage.keyLen
  rw [addr,frame]
  exact spec.2.2.2.2.1

theorem key_read (p : Layout) (hn : Native p) (host : NearState) (key : List UInt8)
    (hk : getMemOrReg ⟨p.memory,host⟩ (UInt64.ofNat p.keyPtr.toNat) (UInt64.ofNat p.keyLen.toNat)=some key) :
    getMemOrReg ⟨StateDispatchStorage.lowMemory (storageLayout p),host⟩
      (StateDispatchStorage.keyPtr (storageLayout p)) (StateDispatchStorage.keyLen (storageLayout p))=some key := by
  rw [keyPtr_eq p hn,keyLen_eq p hn]
  have shapes := borrow_shapes p hn
  have ptr : (UInt64.ofNat p.keyPtr.toNat).toNat=p.keyPtr.toNat := by simp
  have len : (UInt64.ofNat p.keyLen.toNat).toNat=p.keyLen.toNat := by simp
  have ns : UInt64.ofNat p.keyLen.toNat≠u64Max := by
    intro eq
    have he := congrArg UInt64.toNat eq
    rw [len] at he
    change p.keyLen.toNat=18446744073709551615 at he
    have := p.keyLen.toNat_lt;omega
  have bound := hn.keyBound
  have currentBound : p.keyPtr.toNat+p.keyLen.toNat≤(StateDispatchStorage.lowMemory (storageLayout p)).size*65536 := by
    change _≤(StateDispatchLength.lowMemory (storageLayout p)).byteSize
    rw [shapes.2.2.2.2.2];exact bound
  have originalBound : p.keyPtr.toNat+p.keyLen.toNat≤p.memory.size*65536 := bound
  have lists : (StateDispatchStorage.lowMemory (storageLayout p)).readList p.keyPtr.toNat p.keyLen.toNat=
      p.memory.readList p.keyPtr.toNat p.keyLen.toNat := by
    unfold Memory.readList
    apply List.map_congr_left
    intro i hi
    have hi := List.mem_range.mp hi
    apply low_byte p hn
    · have := hn.keyAbove;omega
    · rcases hn.keyCounterSep with hc|hc <;> omega
  simp only [getMemOrReg,ns,ptr,len,show ¬(p.keyPtr.toNat+p.keyLen.toNat>p.memory.size*65536) by omega] at hk
  simp only [getMemOrReg,ns,ptr,len,show ¬(p.keyPtr.toNat+p.keyLen.toNat>(StateDispatchStorage.lowMemory (storageLayout p)).size*65536) by omega]
  rw [lists]
  exact hk
end WNear.Proofs.StateReadStorageOuter
