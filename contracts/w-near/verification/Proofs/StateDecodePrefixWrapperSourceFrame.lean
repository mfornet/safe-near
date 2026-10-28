import Proofs.StateDecodePrefixSourceFrame
import Proofs.StateDecodePrefixWrapperRecord

/-! Original remaining source bytes survive the complete315 wrapper. Its
child output occupies [childSP, childSP+16), so that span is excluded as well. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic

theorem finalMemory_source_frame (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p)
    (hd : StateDecodePrefix.AcceptedDomain p.toPrefix q) (j : Nat)
    (hstack : p.sp.toNat+16≤j)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤j)
    (hroot : j<q.allocator.toNat ∨q.allocator.toNat+4≤j)
    (hout : j<p.wrapperOut.toNat ∨p.wrapperOut.toNat+16≤j)
    (hslice : j<p.slice.toNat ∨p.slice.toNat+8≤j) :
    (finalMemory p q).read8 j=p.memory.read8 j := by
  have childOut:p.out=p.sp:=hn.childOut.trans hn.childSP.symm
  have child:=StateDecodePrefix.finalMemory_source_frame p.toPrefix q hn.child hd.toAllocationDomain j
    (by omega) hheap hroot (Or.inr (by rw[childOut];exact hstack)) hslice
  have wrapper:=Tail.finalMemory_byte_frame (tailLayout p q) (tail_native p q hn hd) j hout
  exact wrapper.trans child

/-- With a nonwrapping wrapper stack reservation, the child output ends at
original wrapperSP, yielding the familiar original-SP source bound. -/
theorem finalMemory_source_frame_above_sp (p : Layout) (q : StateDecodeVectorCopy.Layout) (hn : Native p)
    (hd : StateDecodePrefix.AcceptedDomain p.toPrefix q) (j : Nat)
    (hsp : 16≤p.wrapperSP.toNat) (hstack : p.wrapperSP.toNat≤j)
    (hheap : (StateDecodeRaw.originalFinish q.toRaw).toNat+8≤j)
    (hroot : j<q.allocator.toNat ∨q.allocator.toNat+4≤j)
    (hout : j<p.wrapperOut.toNat ∨p.wrapperOut.toNat+16≤j)
    (hslice : j<p.slice.toNat ∨p.slice.toNat+8≤j) :
    (finalMemory p q).read8 j=p.memory.read8 j := by
  have width:=p.wrapperSP.toNat_lt
  have child:p.sp.toNat=p.wrapperSP.toNat-16:=by
    rw[hn.childSP,scratch,UInt32.toNat_sub]
    simp only[UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
    omega
  exact finalMemory_source_frame p q hn hd j (by rw[child];omega) hheap hroot hout hslice
end WNear.Proofs.StateDecodePrefixWrapper
