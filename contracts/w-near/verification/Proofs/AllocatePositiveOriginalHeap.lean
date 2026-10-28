import Proofs.AllocatePositiveState
import Proofs.PanicAllocateReadback

/-! The positive allocator's real root snapshot derives its search domain
from original heap words. No saved-memory Native or lookup is a premise. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 savedMemory

private theorem stack_numbers(p:Layout)(hl:16≤p.sp.toNat)(hb:p.sp.toNat≤p.memory.byteSize):
    (scratch p).toNat+16=p.sp.toNat ∧(scratch p+12).toNat=(scratch p).toNat+12 ∧
    (scratch p).toNat+12+4≤p.memory.byteSize:=by
  have lt:=p.sp.toNat_lt
  have sub:(scratch p).toNat=p.sp.toNat-16:=by
    unfold scratch
    rw[UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  have add:(scratch p+12).toNat=(scratch p).toNat+12:=by
    rw[UInt32.toNat_add]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    exact Nat.mod_eq_of_lt (by omega)
  exact ⟨by omega,add,by omega⟩

theorem saved_head_original(p:Layout)(hw:p.memory.wf)(hl:16≤p.sp.toNat)(hb:p.sp.toNat≤p.memory.byteSize):
    AllocateSearch.head (searchLayout p)=readI32 p.memory p.allocator.toNat:=by
  have n:=stack_numbers p hl hb
  change readI32 (savedMemory p) (scratch p+12).toNat=readI32 p.memory p.allocator.toNat
  rw[n.2.1]
  unfold savedMemory
  exact PanicAllocateReadback.read_write_self p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hw n.2.2

theorem saved_word_above(p:Layout)(hw:p.memory.wf)(hl:16≤p.sp.toNat)(hb:p.sp.toNat≤p.memory.byteSize)
    (address:Nat)(above:p.sp.toNat≤address):
    readI32 (savedMemory p) address=readI32 p.memory address:=by
  have n:=stack_numbers p hl hb
  unfold savedMemory
  exact PanicAllocateReadback.read_write_frame p.memory address ((scratch p).toNat+12)
    (readI32 p.memory p.allocator.toNat) hw n.2.2 (Or.inr (by omega))

theorem search_native_original(p:Layout)(hw:p.memory.wf)(hl:16≤p.sp.toNat)(hb:p.sp.toNat≤p.memory.byteSize)
    (hnz:readI32 p.memory p.allocator.toNat≠0)
    (split:Allocate.SplitNative p.memory (readI32 p.memory p.allocator.toNat) (words p))
    (he:(Allocate.endWord p.memory (readI32 p.memory p.allocator.toNat)).toNat+8≤p.memory.byteSize)
    (flags:readI32 p.memory (readI32 p.memory p.allocator.toNat).toNat&&&3=0)
    (candidate:readI32 p.memory ((readI32 p.memory p.allocator.toNat).toNat+8)&&&1=0)
    (vtable:1057464+20≤p.memory.byteSize)
    (above:p.sp.toNat≤(readI32 p.memory p.allocator.toNat).toNat):
    AllocateSearch.Native (searchLayout p):=by
  have n:=stack_numbers p hl hb
  have shape:=writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hw n.2.2
  have savedSize:(savedMemory p).byteSize=p.memory.byteSize:=by unfold savedMemory;exact shape.2.1
  have savedWf:(savedMemory p).wf:=by unfold savedMemory;exact shape.1
  have head:=saved_head_original p hw hl hb
  have word:=saved_word_above p hw hl hb (readI32 p.memory p.allocator.toNat).toNat above
  have flag:=saved_word_above p hw hl hb ((readI32 p.memory p.allocator.toNat).toNat+8) (by omega)
  have finish:Allocate.endWord (savedMemory p) (readI32 p.memory p.allocator.toNat)=
      Allocate.endWord p.memory (readI32 p.memory p.allocator.toNat):=by
    unfold Allocate.endWord
    rw[word]
  refine ⟨savedWf,?_,?_,?_,?_,?_,?_,?_⟩
  · change (scratch p+12).toNat+4≤(savedMemory p).byteSize
    rw[n.2.1,savedSize];exact n.2.2
  · rw[head];exact hnz
  · change Allocate.SplitNative (savedMemory p) (AllocateSearch.head (searchLayout p)) (words p)
    rw[head]
    refine ⟨split.wordsPositive,?_,?_⟩
    · rw[finish];exact split.room
    · rw[finish,savedSize];exact split.endBound
  · change (Allocate.endWord (savedMemory p) (AllocateSearch.head (searchLayout p))).toNat+8≤(savedMemory p).byteSize
    rw[head,finish,savedSize];exact he
  · change readI32 (savedMemory p) (AllocateSearch.head (searchLayout p)).toNat&&&3=0
    rw[head,word];exact flags
  · change readI32 (savedMemory p) ((AllocateSearch.head (searchLayout p)).toNat+8)&&&1=0
    rw[head,flag];exact candidate
  · change (1057464:UInt32).toNat+20≤(savedMemory p).byteSize
    rw[savedSize];exact vtable
end WNear.Proofs.AllocatePositive
