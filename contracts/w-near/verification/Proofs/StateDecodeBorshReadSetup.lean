import Proofs.StateDecodeBorshReadState
import Proofs.PanicAllocateReadback

/-! The actual161 length-then-pointer setup constructs the descriptor on a
well-formed memory and preserves every original source/heap byte above SP. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 writeI32 writeI64

private theorem sub_nat(x:UInt32)(n:Nat)(h:n≤x.toNat)(hn:n<2^32):
    (x-UInt32.ofNat n).toNat=x.toNat-n:=by
  rw[UInt32.toNat_sub,UInt32.toNat_ofNat',Nat.mod_eq_of_lt hn]
  have lt:=x.toNat_lt
  omega

theorem scratch_numbers(p:Layout)(hn:Native p):
    (scratch p).toNat=p.sp161.toNat-144 ∧(scratch p).toNat+144=p.sp161.toNat ∧
    (scratch p).toNat+144≤p.memory.byteSize ∧scratch p+144=p.sp161:=by
  have lo:=hn.spLower
  have eq:(scratch p).toNat=p.sp161.toNat-144:=sub_nat p.sp161 144 (by omega) (by omega)
  exact ⟨eq,by omega,by have b:=hn.spBound;omega,UInt32.sub_add_cancel _ _⟩

theorem scratch_add(p:Layout)(hn:Native p)(offset:Nat)(ho:offset<144):
    (scratch p+UInt32.ofNat offset).toNat=(scratch p).toNat+offset:=by
  have n:=scratch_numbers p hn
  have lt:=p.sp161.toNat_lt
  have off:offset<2^32:=by omega
  rw[UInt32.toNat_add,UInt32.toNat_ofNat',Nat.mod_eq_of_lt off]
  exact Nat.mod_eq_of_lt (by omega)

theorem setupMemory_spec(p:Layout)(hn:Native p):
    (setupMemory p).wf ∧(setupMemory p).byteSize=p.memory.byteSize ∧(setupMemory p).max=p.memory.max:=by
  have n:=scratch_numbers p hn
  have high:=writeI32_spec p.memory ((scratch p).toNat+12) p.length hn.wf (by omega)
  have low:=writeI32_spec (highSetupMemory p) ((scratch p).toNat+8) p.pointer high.1 (by unfold highSetupMemory;rw[high.2.1];omega)
  exact ⟨low.1,low.2.1.trans high.2.1,low.2.2.1.trans high.2.2.1⟩

theorem setupMemory_byte_frame(p:Layout)(hn:Native p)(j:Nat)
    (hj:j<(scratch p).toNat+8 ∨(scratch p).toNat+16≤j):
    (setupMemory p).read8 j=p.memory.read8 j:=by
  have n:=scratch_numbers p hn
  have high:=writeI32_spec p.memory ((scratch p).toNat+12) p.length hn.wf (by omega)
  have low:=writeI32_spec (highSetupMemory p) ((scratch p).toNat+8) p.pointer high.1 (by unfold highSetupMemory;rw[high.2.1];omega)
  unfold setupMemory
  rw[low.2.2.2,ite_eq_right (by rcases hj with h|h <;> omega)]
  unfold highSetupMemory
  rw[high.2.2.2]
  exact ite_eq_right (by rcases hj with h|h <;> omega)

theorem setupMemory_word_above(p:Layout)(hn:Native p)(address:Nat)(ha:p.sp161.toNat≤address):
    readI32 (setupMemory p) address=readI32 p.memory address:=by
  have n:=scratch_numbers p hn
  apply Allocate.readI32_congr_bytes
  intro i hi
  apply setupMemory_byte_frame p hn
  exact Or.inr (by omega)

theorem setup_descriptor(p:Layout)(hn:Native p):
    readI32 (setupMemory p) p.slice.toNat=p.pointer ∧
    readI32 (setupMemory p) (p.slice.toNat+4)=p.length:=by
  have n:=scratch_numbers p hn
  have slice:p.slice.toNat=(scratch p).toNat+8:=by rw[hn.slice];exact scratch_add p hn 8 (by omega)
  have high:=writeI32_spec p.memory ((scratch p).toNat+12) p.length hn.wf (by omega)
  have low:=PanicAllocateReadback.read_write_self (highSetupMemory p) ((scratch p).toNat+8) p.pointer high.1 (by unfold highSetupMemory;rw[high.2.1];omega)
  have higher:=PanicAllocateReadback.read_write_self p.memory ((scratch p).toNat+12) p.length hn.wf (by omega)
  have frame:=PanicAllocateReadback.read_write_frame (highSetupMemory p) ((scratch p).toNat+12) ((scratch p).toNat+8) p.pointer high.1 (by unfold highSetupMemory;rw[high.2.1];omega) (Or.inr (by omega))
  constructor
  · rw[slice];exact low
  · rw[slice,show (scratch p).toNat+8+4=(scratch p).toNat+12 by omega]
    exact frame.trans higher

theorem actual_count(p:Layout)(hn:Native p):
    StateDecodeBorshWrapper.count (actualWrapper p)=count p:=by
  exact setupMemory_word_above p hn p.pointer.toNat hn.sourceAbove
end WNear.Proofs.StateDecodeBorshRead
