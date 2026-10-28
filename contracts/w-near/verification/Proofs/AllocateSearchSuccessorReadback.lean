import Proofs.AllocateSearchMemory

/-! A direct split changes its successor's backlink, while preserving the
successor's low header word (including its allocated/next-disabled flags). -/
namespace WNear.Proofs.AllocateSearch
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32
private theorem frame(p:Layout)(m:Memory)(shape:Shape p m)(address target:Nat)(value:UInt32)
    (hb:address+4≤p.memory.byteSize)(hs:target+4≤address ∨address+4≤target):
    readI32 (writeI32 m address value) target=readI32 m target:=
  PanicAllocateReadback.read_write_frame m target address value shape.wf (by rw[shape.size];exact hb) hs

 theorem final_successor_header(p:Layout)(hn:Native p):
    readI32 (finalMemory p) (finish p).toNat=readI32 p.memory (finish p).toNat:=by
  have b:=intervals p hn
  have initialized:=Allocate.initializedMemory_spec p.memory (head p) (header p) hn.memoryWf (by omega) (by omega)
  have first:readI32 (initializedMemory p) (finish p).toNat=readI32 p.memory (finish p).toNat:=by
    apply Allocate.readI32_congr_bytes
    intro i hi
    exact initialized.2.2.2.2.2 _ (Or.inr (by omega))
  have backlink:=frame p (initializedMemory p) (initialized_shape p hn) ((finish p).toNat+4) (finish p).toNat
    (Allocate.taggedValue (initializedMemory p) (finish p) 4 (header p)) (by omega) (Or.inl (by omega))
  have previous:=frame p (backlinkedMemory p) (backlinked_shape p hn) ((header p).toNat+4) (finish p).toNat
    (Allocate.taggedValue (backlinkedMemory p) (header p) 4 (head p)) (by omega) (Or.inr (by omega))
  have unflagged:=frame p (previousMemory p) (previous_shape p hn) ((head p).toNat+8) (finish p).toNat
    (readI32 (previousMemory p) ((head p).toNat+8)&&&4294967294) (by omega) (Or.inr (by omega))
  have linked:=frame p (unflaggedMemory p) (unflagged_shape p hn) (head p).toNat (finish p).toNat
    (Allocate.taggedValue (unflaggedMemory p) (head p) 0 (header p)) (by omega) (Or.inr (by omega))
  have marked:=frame p (linkedMemory p) (linked_shape p hn) (header p).toNat (finish p).toNat
    (readI32 (linkedMemory p) (header p).toNat|||1) (by omega) (Or.inr (by omega))
  exact marked.trans (linked.trans (unflagged.trans (previous.trans (backlink.trans first))))
end WNear.Proofs.AllocateSearch
