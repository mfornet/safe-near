import Proofs.StateDecodeRawSearchFrame
import Proofs.StateDecodeVectorCopyMemory

/-! Direct comparison with the actual allocator-search post-memory. Result
records and forward-copy destination are excluded using original address spans. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

 theorem finalMemory_search_frame(p:Layout)(hn:Native p)(j:Nat)(above:p.spVector.toNat≤j)
    (root:j<p.allocator.toNat ∨p.allocator.toNat+4≤j)
    (output:j<p.outVector.toNat ∨p.outVector.toNat+12≤j):
    (finalMemory p).read8 j=
      (AllocatePositive.searchedMemory (StateDecodeRaw.actualPositive p.toRaw)).read8 j:=by
  have a:=allocated_spec p hn
  have nums:=stack_numbers p hn
  have lo:=hn.spLower
  have rawBelow:p.spRaw.toNat≤j:=by rw[nums.2.1];omega
  have rawOut:j<p.outRaw.toNat ∨p.outRaw.toNat+8≤j:=by rw[nums.2.2.1];omega
  have raw:=StateDecodeRaw.finalMemory_search_frame p.toRaw hn.raw j rawBelow root rawOut
  have zb:p.outVector.toNat+8+4≤(memoryAllocated p).byteSize:=by rw[a.2.1];exact hn.outBound
  have z:=writeI32_spec (memoryAllocated p) (p.outVector.toNat+8) 0 a.1 zb
  have fb:p.outVector.toNat+8≤(zeroMemory p).byteSize:=by
    change _≤(writeI32 _ _ _).byteSize
    rw[z.2.1,a.2.1];have b:=hn.outBound;omega
  have f:=writeI64_spec (zeroMemory p) p.outVector.toNat (packed p) z.1 fb
  have nf:¬(p.outVector.toNat≤j ∧j<p.outVector.toNat+8):=by rcases output with h|h <;> omega
  have nz:¬(p.outVector.toNat+8≤j ∧j<p.outVector.toNat+8+4):=by rcases output with h|h <;> omega
  have first:(finalMemory p).read8 j=(zeroMemory p).read8 j:=by
    unfold finalMemory;rw[f.2.2.2];exact ite_eq_right nf
  have second:(zeroMemory p).read8 j=(memoryAllocated p).read8 j:=by
    unfold zeroMemory;rw[z.2.2.2];exact ite_eq_right nz
  exact first.trans (second.trans raw)
end WNear.Proofs.StateDecodeVector

namespace WNear.Proofs.StateDecodeVectorCopy
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

 theorem finalMemory_search_frame(p:Layout)(hn:Native p)(j:Nat)(above:p.spVector.toNat≤j)
    (root:j<p.allocator.toNat ∨p.allocator.toNat+4≤j)
    (output:j<p.outVector.toNat ∨p.outVector.toNat+12≤j)
    (copy:j<(pointer p).toNat ∨(pointer p).toNat+p.size.toNat≤j):
    (finalMemory p).read8 j=
      (AllocatePositive.searchedMemory (StateDecodeRaw.actualPositive p.toRaw)).read8 j:=by
  have first:=(finalMemory_spec p hn).2.2.2.2 j
    (by rcases output with h|h <;> omega)
  have second:=(copiedMemory_spec p hn).2.2.2 j copy
  have third:=StateDecodeVector.finalMemory_search_frame p.toVector hn.vector j above root output
  exact first.trans (second.trans third)

 theorem finalMemory_search_word(p:Layout)(hn:Native p)(address:Nat)(above:p.spVector.toNat≤address)
    (root:address+4≤p.allocator.toNat ∨p.allocator.toNat+4≤address)
    (output:address+4≤p.outVector.toNat ∨p.outVector.toNat+12≤address)
    (copy:address+4≤(pointer p).toNat ∨(pointer p).toNat+p.size.toNat≤address):
    readI32 (finalMemory p) address=
      readI32 (AllocatePositive.searchedMemory (StateDecodeRaw.actualPositive p.toRaw)) address:=by
  apply readI32_congr_bytes
  intro i hi
  apply finalMemory_search_frame p hn (address+i) (by omega)
  · rcases root with h|h <;> omega
  · rcases output with h|h <;> omega
  · rcases copy with h|h <;> omega
end WNear.Proofs.StateDecodeVectorCopy
