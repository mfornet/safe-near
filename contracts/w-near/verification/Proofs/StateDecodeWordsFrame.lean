import Proofs.StateDecodeWordsCall
import Proofs.StateDecodeWordsMemory

/-! Complete memory, code/global and functional-host frames of the word decoders. -/
namespace WNear.Proofs.StateDecodeWords
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits paid_gas)
set_option maxRecDepth 16384

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_word (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt64) :
    fields (storeI64 s index address memory value)=fields s := rfl
private theorem fields_byte (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    fields (storeByte s index address memory value)=fields s := rfl
private theorem fields_copy (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    fields (copyAfter wide s op index memory out source)=fields s := by
  cases wide <;> simp only [copyAfter,ite_true,ite_false,Bool.false_eq_true,highStore,lowStore,fields_word,fields_paid]
private theorem fields_after (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    fields (after wide s op index memory out source)=fields s := by
  simp only [after,statusStore,fields_byte,fields_paid,fields_copy]

private theorem fields_project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables ∧t.globals=s.globals :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2.1) h,congrArg (fun x=>x.2.2.2) h⟩

theorem after_fields (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    (after wide s op index memory out source).funcs=s.funcs ∧
    (after wide s op index memory out source).modules=s.modules ∧
    (after wide s op index memory out source).tables=s.tables ∧
    (after wide s op index memory out source).globals=s.globals := by
  exact fields_project s _ (fields_after wide s op index memory out source)

theorem after_memory (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]?=some memory) :
    (after wide s op index memory out source).mems[index]?=some (finalMemory wide memory out source) := by
  have mp : (paid s op 6).mems[index]?=some memory := by rw[mems_paid];exact hm
  have mc := copyAfter_memory wide (paid s op 6) op index memory out source mp
  have mr : (paid (paid (copyAfter wide (paid s op 6) op index memory out source) op 2) op 3).mems[index]?=
      some (copiedMemory wide memory out source) := by rw[mems_paid,mems_paid];exact mc
  exact storeByte_memory _ index out.toNat (copiedMemory wide memory out source) 0 mr

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem view_word (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt64) :
    view seed (storeI64 s index address memory value).host=view seed s.host := rfl
private theorem view_byte (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    view seed (storeByte s index address memory value).host=view seed s.host := rfl
private theorem view_copy (seed : NearState) (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    view seed (copyAfter wide s op index memory out source).host=view seed s.host := by
  cases wide <;> simp only [copyAfter,ite_true,ite_false,Bool.false_eq_true,highStore,lowStore,view_word,view_paid]

theorem after_functional_host (wide : Bool) (s : Store NearState) (op index : Nat) (memory : Memory) (out source : UInt32) :
    {(after wide s op index memory out source).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after wide s op index memory out source).host=s.host
  simp only [after,statusStore,view_byte,view_paid,view_copy]
  rfl

theorem callAfter_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (index : Nat) (memory : Memory) (out source : UInt32)
    (hm : s.mems[index]?=some memory) :
    (callAfter wide cfg s index memory out source).mems[index]?=some (finalMemory wide memory out source) :=
  after_memory wide (entered s cfg.regularOpCost) cfg.regularOpCost index memory out source hm

theorem callAfter_fields (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (index : Nat) (memory : Memory) (out source : UInt32) :
    (callAfter wide cfg s index memory out source).funcs=s.funcs ∧
    (callAfter wide cfg s index memory out source).modules=s.modules ∧
    (callAfter wide cfg s index memory out source).tables=s.tables ∧
    (callAfter wide cfg s index memory out source).globals=s.globals :=
  after_fields wide (entered s cfg.regularOpCost) cfg.regularOpCost index memory out source

theorem callAfter_functional_host (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (index : Nat) (memory : Memory) (out source : UInt32) :
    {(callAfter wide cfg s index memory out source).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h:=after_functional_host wide (entered s cfg.regularOpCost) cfg.regularOpCost index memory out source
  have q:=congrArg (view s.host) h
  exact q
end WNear.Proofs.StateDecodeWords
