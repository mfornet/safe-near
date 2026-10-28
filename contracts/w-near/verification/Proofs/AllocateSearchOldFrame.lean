import Proofs.AllocateSearchMemory

/-! Every actual direct-split write lies inside the original free-block header
through its terminal backlink. This frames original source bytes beyond it. -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

private theorem write_byte (p : Layout) (memory : Memory) (shape : Shape p memory)
    (address : Nat) (value : UInt32) (j : Nat)
    (hb : address+4≤p.memory.byteSize) (hd : j<address ∨ address+4≤j) :
    (writeI32 memory address value).read8 j=memory.read8 j := by
  have s:=writeI32_spec memory address value shape.wf (by rw[shape.size];exact hb)
  rw [s.2.2.2 j]
  exact ite_eq_right (by omega)

attribute [local irreducible] clearedMemory initializedMemory backlinkedMemory previousMemory
  unflaggedMemory linkedMemory finalMemory

/-- The complete split preserves each original byte outside the original
`[head, finish+8)` interval, including its final terminal-backlink write. -/
theorem finalMemory_byte_frame (p : Layout) (hn : Native p) (j : Nat)
    (hj : j<(head p).toNat ∨ (finish p).toNat+8≤j) :
    (finalMemory p).read8 j=p.memory.read8 j := by
  have b:=intervals p hn
  have cl:=Allocate.clearedMemory_spec p.memory (header p) hn.memoryWf (by omega)
  have cleared : (clearedMemory p).read8 j=p.memory.read8 j := by
    simpa only [clearedMemory] using cl.2.2.2 j (by omega)
  have init := write_byte p (clearedMemory p) (cleared_shape p hn) (header p).toNat
    (readI32 (clearedMemory p) (head p).toNat &&& 4294967292) j (by omega) (by omega)
  have back := write_byte p (initializedMemory p) (initialized_shape p hn) ((finish p).toNat+4)
    (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p)) j (by omega) (by omega)
  have prev := write_byte p (backlinkedMemory p) (backlinked_shape p hn) ((header p).toNat+4)
    (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) j (by omega) (by omega)
  have unflag := write_byte p (previousMemory p) (previous_shape p hn) ((head p).toNat+8)
    (readI32 (previousMemory p) ((head p).toNat+8) &&& 4294967294) j (by omega) (by omega)
  have link := write_byte p (unflaggedMemory p) (unflagged_shape p hn) (head p).toNat
    (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)) j (by omega) (by omega)
  have mark := write_byte p (linkedMemory p) (linked_shape p hn) (header p).toNat
    (readI32 (linkedMemory p) (header p).toNat ||| 1) j (by omega) (by omega)
  unfold finalMemory Allocate.markedMemory
  rw [mark]
  unfold linkedMemory
  rw [link]
  unfold unflaggedMemory
  rw [unflag]
  unfold previousMemory
  rw [prev]
  unfold backlinkedMemory
  rw [back]
  unfold initializedMemory
  rw [init]
  exact cleared
end WNear.Proofs.AllocateSearch
