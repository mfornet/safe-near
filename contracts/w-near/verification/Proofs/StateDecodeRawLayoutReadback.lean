import Proofs.StateDecodeRawNative

/-! Actual f767 reads size then alignment from752's two output words. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 laidOutMemory

theorem layout_words (p : Layout) (hn : Native p) :
    readI32 (laidOutMemory p) ((scratch p).toNat+24)=p.size ∧
    readI32 (laidOutMemory p) ((scratch p).toNat+28)=1 := by
  have b:=layout_bounds p hn
  have s:=AllocateLayoutWrapper.final_spec (layout752 p) hn.allocation.wf hn.allocation.width b.1 b.2
  have n:=stack_numbers p hn
  have lo:=hn.spLower
  have hi:=p.spRaw.toNat_lt
  have out : (layout752 p).out.toNat=(scratch p).toNat+24 := by rw[n.2.2.2.1,n.1];omega
  constructor
  · have low:=s.2.2.2.1
    rw [out] at low
    simpa only [laidOutMemory,show (layout752 p).size=p.size from rfl] using low
  · simpa only [laidOutMemory,out,Nat.add_assoc] using s.2.2.2.2
end WNear.Proofs.StateDecodeRaw
