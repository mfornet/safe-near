import Proofs.AllocateVectorOuterOutput
import Proofs.StorePairReadback
import Proofs.PanicAllocateReadback
import Proofs.AllocateSearchGasCost
import NearVM.MemoryListWordRules

/-! Cached687 output retains arbitrary aliases with the source record. Only
the destination twelve-byte bound is needed for shape and exact readback. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
set_option maxRecDepth 16384
attribute [local irreducible] outputMemory outputAfter highStore readI32 readI64 writeI32 writeI64

theorem outputMemory_spec (memory : Memory) (out count : UInt32) (cached : UInt64)
    (hw : memory.wf) (hb : out.toNat+12≤memory.byteSize) :
    (outputMemory memory out count cached).wf ∧
    (outputMemory memory out count cached).byteSize=memory.byteSize ∧
    (outputMemory memory out count cached).max=memory.max ∧
    readI64 (outputMemory memory out count cached) out.toNat=cached ∧
    readI32 (outputMemory memory out count cached) (out.toNat+8)=count ∧
    ∀ j, (j<out.toNat ∨ out.toNat+12≤j) →
      (outputMemory memory out count cached).read8 j=memory.read8 j := by
  let high := writeI32 memory (out.toNat+8) count
  have a := writeI32_spec memory (out.toNat+8) count hw (by omega)
  have bnd : out.toNat+8≤high.byteSize := by rw [show high.byteSize=memory.byteSize from a.2.1];omega
  have b := writeI64_spec high out.toNat cached a.1 bnd
  have low : readI64 (outputMemory memory out count cached) out.toNat=cached := by
    apply StorePairReadback.readI64_of_bytes
    intro i hi
    rw [outputMemory]
    change (writeI64 high out.toNat cached).read8 (out.toNat+i)=_
    rw [b.2.2.2,ite_eq_left (show out.toNat≤out.toNat+i ∧ out.toNat+i<out.toNat+8 by omega)]
    simp only [Nat.add_sub_cancel_left]
  have highFrame : readI32 (outputMemory memory out count cached) (out.toNat+8)=readI32 high (out.toNat+8) := by
    apply readI32_congr_bytes
    intro i hi
    rw [outputMemory]
    change (writeI64 high out.toNat cached).read8 (out.toNat+8+i)=_
    rw [b.2.2.2,ite_eq_right (show ¬(out.toNat≤out.toNat+8+i ∧ out.toNat+8+i<out.toNat+8) by omega)]
  have highValue := PanicAllocateReadback.read_write_self memory (out.toNat+8) count hw (by omega)
  have shape : (outputMemory memory out count cached).wf ∧
      (outputMemory memory out count cached).byteSize=high.byteSize ∧
      (outputMemory memory out count cached).max=high.max := by
    simpa only [outputMemory,high] using And.intro b.1 (And.intro b.2.1 b.2.2.1)
  refine ⟨shape.1,shape.2.1.trans a.2.1,shape.2.2.trans a.2.2.1,low,highFrame.trans highValue,?_⟩
  intro j hj
  rw [outputMemory]
  change (writeI64 high out.toNat cached).read8 j=memory.read8 j
  rw [b.2.2.2,ite_eq_right (show ¬(out.toNat≤j ∧ j<out.toNat+8) by omega)]
  change (writeI32 memory (out.toNat+8) count).read8 j=memory.read8 j
  rw [a.2.2.2,ite_eq_right (show ¬(out.toNat+8≤j ∧ j<out.toNat+8+4) by omega)]

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero=>rfl | succ n ih=>exact ih
 theorem outputAfter_memory (s : Store NearState) (op index : Nat) (memory : Memory)
    (out count : UInt32) (cached : UInt64) (hm : s.mems[index]?=some memory) :
    (outputAfter s op index memory out count cached).mems[index]?=some (outputMemory memory out count cached) := by
  have first := storeI32_memory (paid s op 3) index (out.toNat+8) memory count (by rw [mems_paid];exact hm)
  unfold outputAfter outputMemory
  apply storeI64_memory
  rw [mems_paid]
  simpa only [highStore] using first

private theorem units32 (s : Store NearState) (op index address : Nat) (memory : Memory) (v : UInt32) :
    GasUnits s (storeI32 (paid s op 3) index address memory v) op 3 := (gasUnits_paid s op 3).host_eq rfl
private theorem units64 (s : Store NearState) (op index address : Nat) (memory : Memory) (v : UInt64) :
    GasUnits s (storeI64 (paid s op 3) index address memory v) op 3 := (gasUnits_paid s op 3).host_eq rfl
 theorem outputAfter_gas (s : Store NearState) (op index : Nat) (memory : Memory)
    (out count : UInt32) (cached : UInt64) : GasUnits s (outputAfter s op index memory out count cached) op 6 := by
  have all := (units32 s op index (out.toNat+8) memory count).trans
    (units64 _ op index out.toNat (writeI32 memory (out.toNat+8) count) cached)
  simpa only [outputAfter,highStore,Nat.reduceAdd] using all

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem fields32 (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s := rfl
private theorem fields64 (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : fields (storeI64 s i a m v)=fields s := rfl
 theorem outputAfter_fields (s : Store NearState) (op index : Nat) (memory : Memory)
    (out count : UInt32) (cached : UInt64) :
    (outputAfter s op index memory out count cached).funcs=s.funcs ∧
    (outputAfter s op index memory out count cached).modules=s.modules ∧
    (outputAfter s op index memory out count cached).tables=s.tables ∧
    (outputAfter s op index memory out count cached).globals=s.globals := by
  have eq : fields (outputAfter s op index memory out count cached)=fields s := by
    rw [outputAfter,fields64,fields_paid,highStore,fields32,fields_paid]
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,
    congrArg (fun x=>x.2.2.1) eq,congrArg (fun x=>x.2.2.2) eq⟩

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with | zero=>rfl | succ n ih=>exact ih
private theorem view32 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) :
    view seed (storeI32 s i a m v).host=view seed s.host := rfl
private theorem view64 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) :
    view seed (storeI64 s i a m v).host=view seed s.host := rfl
 theorem outputAfter_functional_host (s : Store NearState) (op index : Nat) (memory : Memory)
    (out count : UInt32) (cached : UInt64) :
    {(outputAfter s op index memory out count cached).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (outputAfter s op index memory out count cached).host=s.host
  rw [outputAfter,view64,view_paid,highStore,view32,view_paid]
  rfl
end WNear.Proofs.AllocateVectorOuter
