import Proofs.StateDecodeRawFinish
import Proofs.AllocateVectorFrame

/-! Generic f767 output-tail resources, independent of allocation internals. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_globals (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem record_globals (s : Store NearState) (op i : Nat) (m : Memory) (out ptr len : UInt32) :
    (AllocateVector.recordStore s op i m out ptr len).globals=s.globals := by
  simp only [AllocateVector.recordStore,storeI32_globals,paid_globals]
attribute [local irreducible] AllocateVector.finished AllocateVector.recordStore

theorem finished_memory (s : Store NearState) (op i g : Nat) (m : Memory) (out ptr len scratch : UInt32)
    (hm : s.mems[i]?=some m) :
    (finished s op i g m out ptr len scratch).mems[i]?=some (AllocateVector.recordMemory m out ptr len) := by
  unfold finished AllocateVector.finished
  simp only [chargedStore,setGlobal,paid_mems]
  apply AllocateVector.recordStore_memory
  rw [paid_mems];exact hm

theorem finished_globals (s : Store NearState) (op i g : Nat) (m : Memory) (out ptr len scratch : UInt32) :
    (finished s op i g m out ptr len scratch).globals=(setGlobal s g (.i32 (scratch+32))).globals := by
  unfold finished AllocateVector.finished
  simp only [chargedStore,setGlobal,paid_globals,record_globals]
private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem fields_global (s : Store NearState) (i : Nat) (v : Value) : fields (setGlobal s i v)=fields s:=rfl
private theorem fields_charge (s : Store NearState) (op : Nat) : fields (chargedStore s op)=fields s:=rfl
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s:=rfl
private theorem fields_record (s : Store NearState) (op i : Nat) (m : Memory) (out ptr len : UInt32) :
    fields (AllocateVector.recordStore s op i m out ptr len)=fields s := by
  simp only [AllocateVector.recordStore,fields_store,fields_paid]
attribute [local irreducible] fields

theorem finished_fields (s : Store NearState) (op i g : Nat) (m : Memory) (out ptr len scratch : UInt32) :
    (finished s op i g m out ptr len scratch).funcs=s.funcs ∧
    (finished s op i g m out ptr len scratch).modules=s.modules ∧
    (finished s op i g m out ptr len scratch).tables=s.tables := by
  have h : fields (finished s op i g m out ptr len scratch)=fields s := by
    simp only [finished,AllocateVector.finished,fields_charge,fields_global,fields_paid,fields_record]
  refine ⟨?_,?_,?_⟩
  · simpa only [fields] using congrArg (fun x=>x.1) h
  · simpa only [fields] using congrArg (fun x=>x.2.1) h
  · simpa only [fields] using congrArg (fun x=>x.2.2) h
end WNear.Proofs.StateDecodeRaw
