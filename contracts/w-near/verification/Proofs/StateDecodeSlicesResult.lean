import Proofs.StateDecodeSlicesCall
import Proofs.ValueReturnOuterLayout

/-! Accepted slice outputs and full memory, code, global and host frames. -/
namespace WNear.Proofs.StateDecodeSlices
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_gas)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

theorem finalMemory_spec (drop : Bool) (memory : Memory) (out pointer len split : UInt32)
    (hwf : memory.wf) (hb : out.toNat+8≤memory.byteSize) :
    (finalMemory drop memory out pointer len split).wf ∧
    (finalMemory drop memory out pointer len split).byteSize=memory.byteSize ∧
    (finalMemory drop memory out pointer len split).max=memory.max ∧
    ∀ j, (finalMemory drop memory out pointer len split).read8 j=
      if out.toNat≤j ∧ j<out.toNat+4 then UInt8.ofNat ((lowWord drop pointer split).toNat >>> (8*(j-out.toNat)))
      else if out.toNat+4≤j ∧ j<out.toNat+8 then UInt8.ofNat ((highWord drop len split).toNat >>> (8*(j-(out.toNat+4))))
      else memory.read8 j := by
  have high := writeI32_spec memory (out.toNat+4) (highWord drop len split) hwf (by omega)
  have low := writeI32_spec (firstMemory drop memory out len split) out.toNat (lowWord drop pointer split) high.1
    (by change _≤(writeI32 memory _ _).byteSize;rw [high.2.1];omega)
  refine ⟨low.1,low.2.1.trans high.2.1,low.2.2.1.trans high.2.2.1,?_⟩
  intro j
  unfold finalMemory
  rw [low.2.2.2 j]
  have bytes : (firstMemory drop memory out len split).read8 j=_ := high.2.2.2 j
  rw [bytes]

theorem finalMemory_words (drop : Bool) (memory : Memory) (out pointer len split : UInt32)
    (hwf : memory.wf) (hb : out.toNat+8≤memory.byteSize) :
    readI32 (finalMemory drop memory out pointer len split) out.toNat=lowWord drop pointer split ∧
    readI32 (finalMemory drop memory out pointer len split) (out.toNat+4)=highWord drop len split := by
  have spec := finalMemory_spec drop memory out pointer len split hwf hb
  constructor
  · apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    rw [spec.2.2.2 (out.toNat+i)]
    simp only [show out.toNat≤out.toNat+i ∧ out.toNat+i<out.toNat+4 by omega,and_self,ite_true,Nat.add_sub_cancel_left]
  · apply ValueReturnOuterLayout.readI32_of_bytes
    intro i hi
    rw [spec.2.2.2 (out.toNat+4+i)]
    simp only [show ¬(out.toNat≤out.toNat+4+i ∧ out.toNat+4+i<out.toNat+4) by omega,ite_false,
      show out.toNat+4≤out.toNat+4+i ∧ out.toNat+4+i<out.toNat+8 by omega,and_self,ite_true,Nat.add_sub_cancel_left]

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_paid (s : Store NearState) (op n : Nat) :
    (paid s op n).funcs=s.funcs ∧ (paid s op n).modules=s.modules ∧ (paid s op n).tables=s.tables ∧ (paid s op n).globals=s.globals := by
  induction n with |zero=>exact ⟨rfl,rfl,rfl,rfl⟩ |succ n ih=>exact ih

theorem after_memory (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32)
    (hm : s.mems[index]?=some memory) :
    (after drop s op index memory out pointer len split).mems[index]?=some (finalMemory drop memory out pointer len split) := by
  have he : (paid (paid s op 4) op (wordCount drop)).mems[index]?=some memory := by rw [mems_paid,mems_paid];exact hm
  have one : (highStore drop (paid s op 4) op index memory out len split).mems[index]?=some (firstMemory drop memory out len split) :=
    storeI32_memory (paid (paid s op 4) op (wordCount drop)) index (out.toNat+4) memory (highWord drop len split) he
  have two : (paid (highStore drop (paid s op 4) op index memory out len split) op (wordCount drop)).mems[index]?=some (firstMemory drop memory out len split) := by
    rw [mems_paid];exact one
  exact storeI32_memory _ index out.toNat _ (lowWord drop pointer split) two

theorem after_fields (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32) :
    (after drop s op index memory out pointer len split).funcs=s.funcs ∧
    (after drop s op index memory out pointer len split).modules=s.modules ∧
    (after drop s op index memory out pointer len split).tables=s.tables ∧
    (after drop s op index memory out pointer len split).globals=s.globals := by
  simp only [after,writesAfter,highStore,storeI32_funcs,storeI32_modules,storeI32_tables,storeI32_globals,
    (fields_paid _ _ _).1,(fields_paid _ _ _).2.1,(fields_paid _ _ _).2.2.1,(fields_paid _ _ _).2.2.2,and_self]

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (v : UInt32) :
    view seed (storeI32 s index address memory v).host=view seed s.host := rfl

theorem after_host (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32) :
    {(after drop s op index memory out pointer len split).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after drop s op index memory out pointer len split).host=s.host
  simp only [after,writesAfter,highStore,view_store,view_paid]
  rfl

theorem after_gas (drop : Bool) (s : Store NearState) (op index rest : Nat) (memory : Memory) (out pointer len split : UInt32)
    (hc : s.host.gas.Credits (WNear.Binary.StateDecodeSlices.bodyCost drop*op+rest)) :
    (after drop s op index memory out pointer len split).host.gas.burnt=s.host.gas.burnt+WNear.Binary.StateDecodeSlices.bodyCost drop*op ∧
    (after drop s op index memory out pointer len split).host.gas.promises=s.host.gas.promises := by
  cases drop with
  | false => simpa only [after,writesAfter,highStore,wordCount,Bool.false_eq_true,ite_false,storeI32_host,paid,chargedStore,WNear.Binary.StateDecodeSlices.bodyCost]
      using paid_gas s op 10 rest hc
  | true => simpa only [after,writesAfter,highStore,wordCount,ite_true,storeI32_host,paid,chargedStore,WNear.Binary.StateDecodeSlices.bodyCost]
      using paid_gas s op 14 rest hc

theorem callAfter_memory (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32)
    (hm : s.mems[index]?=some memory) :
    (callAfter drop s op index memory out pointer len split).mems[index]?=some (finalMemory drop memory out pointer len split) :=
  after_memory drop (entered s op) op index memory out pointer len split hm

theorem callAfter_fields (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32) :
    (callAfter drop s op index memory out pointer len split).funcs=s.funcs ∧
    (callAfter drop s op index memory out pointer len split).modules=s.modules ∧
    (callAfter drop s op index memory out pointer len split).tables=s.tables ∧
    (callAfter drop s op index memory out pointer len split).globals=s.globals :=
  after_fields drop (entered s op) op index memory out pointer len split

theorem callAfter_host (drop : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer len split : UInt32) :
    {(callAfter drop s op index memory out pointer len split).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h := congrArg (view s.host) (after_host drop (entered s op) op index memory out pointer len split)
  simpa only [view,callAfter,entered,chargedStore,chargeHost] using h
end WNear.Proofs.StateDecodeSlices
