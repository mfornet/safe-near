import Proofs.AllocationGrowthRemainderReadRoot
import Proofs.AllocationGrowthRemainderStorageRoot

/-! Original static words survive548 under explicit original output separation;
in particular this protects the allocator callback selector used by219. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 copiedMemory readFinalMemory readInputMemory actualVector

 theorem copiedMemory_static_word(p:Layout)(hn:Native p)(ha:p.allocator=1074896)(address:Nat)
    (bound:address+4≤p.memory.byteSize)(above:p.sp523.toNat≤address)
    (root:address+4≤1074896 ∨1074900≤address)
    (counter:address+4≤1074904 ∨1074908≤address)
    (output:address+4≤p.out523.toNat ∨p.out523.toNat+12≤address):
    readI32 (copiedMemory p) address=readI32 p.memory address:=by
  have pointer:=allocated_pointer_above p hn ha
  have original:=read_original_word p hn ha address bound above root counter
  have same:readI32 (copiedMemory p) address=readI32 (readInputMemory p) address:=by
    apply readI32_congr_bytes
    intro i hi
    have copy:=(copiedMemory_spec p hn ha).2.2.2.2.2 (address+i)
      (by rcases output with h|h <;> omega)
    have read:=read_final_protected_byte p hn ha (address+i) (by omega)
      (by rcases counter with h|h <;> omega) (by omega)
    exact copy.trans read
  exact same.trans original
end WNear.Proofs.StateReadRegisterOuter

namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 readI64 finalMemory registeredMemory actualRegister StateReadRegisterOuter.copiedMemory

 theorem finalMemory_static_word(p:Layout)(hn:Native p)(ha:p.allocator=1074896)(address:Nat)
    (bound:address+4≤p.memory.byteSize)(above:p.sp548.toNat≤address)
    (root:address+4≤1074896 ∨1074900≤address)
    (counter:address+4≤1074904 ∨1074908≤address)
    (output:address+4≤p.out548.toNat ∨p.out548.toNat+12≤address):
    readI32 (finalMemory p) address=readI32 p.memory address:=by
  have rn:=register_native p hn ha
  have nums:=stack_numbers p hn
  have lower:=hn.spLower
  have old:(actualRegister p).memory.byteSize=p.memory.byteSize:=by
    simp only[actualRegister,registerTemplate];exact (storageMemory_footprint p hn).2.1
  have cbound:address+4≤(actualRegister p).memory.byteSize:=by rw[old];exact bound
  have csp:(actualRegister p).sp523.toNat≤address:=by
    have eq:(actualRegister p).sp523=scratch p:=by simp only[actualRegister,registerTemplate];exact hn.registerSP
    rw[eq,nums.1];omega
  have cout:(actualRegister p).out523.toNat+12≤address:=by
    have eq:(actualRegister p).out523=scratch p+16:=by simp only[actualRegister,registerTemplate];exact hn.registerOut
    rw[eq,nums.2.2.2];omega
  have ca:(actualRegister p).allocator=1074896:=by simp only[actualRegister,registerTemplate];exact ha
  have child:=StateReadRegisterOuter.copiedMemory_static_word (actualRegister p) rn ca address cbound csp root counter (Or.inr cout)
  have b:=result_bounds p hn ha
  have copy:readI32 (finalMemory p) address=readI32 (registeredMemory p) address:=by
    apply readI32_congr_bytes
    intro i hi
    unfold finalMemory
    exact StateReadResult.finalMemory_outside (registeredMemory p) p.out548 (scratch p+16)
      b.1 b.2.1 b.2.2.2.1 b.2.2.2.2.2.1 _ (by rcases output with h|h <;> omega)
  have same:readI32 (registeredMemory p) address=readI32 (storageMemory p) address:=by
    unfold registeredMemory
    simpa only[actualRegister,registerTemplate] using child
  exact copy.trans (same.trans (storageMemory_word p hn address above counter))
end WNear.Proofs.StateReadStorageOuter
