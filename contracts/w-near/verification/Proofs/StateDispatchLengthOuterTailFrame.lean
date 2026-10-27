import Proofs.StateDispatchLengthOuterTail
import Proofs.StorePairReadback

/-! Exact option-pair memory and scalar resource effects of the f524 tail. -/
namespace WNear.Proofs.StateDispatchLengthOuterTail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] readI64 writeI64

/-- The actual stores have exactly the established high-then-low pair order. -/
theorem finalMemory_eq_pair (memory : Memory) (out : UInt32) (value : UInt64) :
    finalMemory memory out value = StorePair.pairMemory memory out.toNat (present value) value := rfl

theorem finalMemory_spec (memory : Memory) (out : UInt32) (value : UInt64)
    (hw : memory.wf) (hb : out.toNat+16 ≤ memory.byteSize) :
    (finalMemory memory out value).wf ∧ (finalMemory memory out value).byteSize=memory.byteSize ∧
    (finalMemory memory out value).max=memory.max ∧
    readI64 (finalMemory memory out value) out.toNat=present value ∧
    readI64 (finalMemory memory out value) (out.toNat+8)=value ∧
    ∀ j, j<out.toNat ∨ out.toNat+16≤j → (finalMemory memory out value).read8 j=memory.read8 j := by
  rw [finalMemory_eq_pair]
  have h := StorePair.pairMemory_spec memory out.toNat (present value) value hw hb
  refine ⟨h.1,h.2.1,h.2.2.1,StorePairReadback.pairMemory_read_low memory out.toNat (present value) value hw hb,
    StorePairReadback.pairMemory_read_high memory out.toNat (present value) value hw hb,?_⟩
  intro j hj
  rw [h.2.2.2 j]
  rw [ite_eq_right (show ¬(out.toNat≤j ∧ j<out.toNat+8) by omega)]
  rw [ite_eq_right (show ¬(out.toNat+8≤j ∧ j<out.toNat+16) by omega)]

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem mems_global (s : Store NearState) (index : Nat) (v : Value) : (setGlobal s index v).mems=s.mems := rfl

theorem after_memory (s : Store NearState) (op index globalIndex : Nat) (memory : Memory)
    (out scratch : UInt32) (value : UInt64) (hm : s.mems[index]?=some memory) :
    (after s op index globalIndex memory out scratch value).mems[index]?=some (finalMemory memory out value) := by
  have high : (highStore s op index memory out value).mems[index]?=some (highMemory memory out value) := by
    unfold highStore highMemory
    apply storeI64_memory
    rw [mems_paid]
    exact hm
  have low : (lowStore s op index memory out value).mems[index]?=some (finalMemory memory out value) := by
    unfold lowStore finalMemory
    apply storeI64_memory
    rw [mems_paid]
    exact high
  unfold after
  rw [mems_global,mems_paid]
  exact low

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with | zero => rfl | succ n ih => exact ih
private theorem fields_global (s : Store NearState) (index : Nat) (v : Value) : fields (setGlobal s index v)=fields s := rfl
private theorem fields_store (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt64) : fields (storeI64 s index address memory v)=fields s := rfl
private theorem fields_project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩

theorem after_fields (s : Store NearState) (op index globalIndex : Nat) (memory : Memory)
    (out scratch : UInt32) (value : UInt64) :
    (after s op index globalIndex memory out scratch value).funcs=s.funcs ∧
    (after s op index globalIndex memory out scratch value).modules=s.modules ∧
    (after s op index globalIndex memory out scratch value).tables=s.tables := by
  have h : fields (after s op index globalIndex memory out scratch value)=fields s := by
    simp only [after,lowStore,highStore,fields_global,fields_paid,fields_store]
  exact fields_project s _ h

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with | zero => rfl | succ n ih => exact ih

theorem after_globals (s : Store NearState) (op index globalIndex : Nat) (memory : Memory)
    (out scratch : UInt32) (value : UInt64) :
    (after s op index globalIndex memory out scratch value).globals=
      (setGlobal s globalIndex (.i32 (scratch+16))).globals := by
  simp only [after,setGlobal,globals_paid,lowStore,highStore,storeI64_globals]

theorem after_host (s : Store NearState) (op index globalIndex : Nat) (memory : Memory)
    (out scratch : UInt32) (value : UInt64) :
    {(after s op index globalIndex memory out scratch value).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  simp only [after,lowStore,highStore,setGlobal,storeI64_host,paid,chargedStore,chargeHost]

end WNear.Proofs.StateDispatchLengthOuterTail
