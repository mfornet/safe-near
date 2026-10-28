import Proofs.StateDecodePrefixEarlyPhases
import Proofs.StateDecodePrefixLeavesRecordResult

/-! Installed arrays and the reserved global through316's actual early calls. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem fields_store64 (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : fields (storeI64 s i a m v)=fields s:=rfl
private theorem fields_pack (s t : Store NearState)
    (h : t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables ∧t.globals=s.globals) : fields t=fields s :=
  Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))
private theorem fields_slice (drop : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out ptr len split : UInt32) :
    fields (StateDecodeSlices.callAfter drop s op i m out ptr len split)=fields s :=
  fields_pack s _ (StateDecodeSlices.callAfter_fields drop s op i m out ptr len split)
private theorem fields_word (cfg : WasmConfig) (s : Store NearState) :
    fields (StateDecodePrefixLeaves.wordCallAfter cfg s)=fields s := fields_pack s _ (StateDecodePrefixLeaves.wordCallAfter_fields cfg s)
private theorem fields_record (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out len : UInt32) :
    fields (StateDecodePrefixLeaves.recordCallAfter cfg s i m out len)=fields s :=
  fields_pack s _ (StateDecodePrefixLeaves.recordCallAfter_fields cfg s i m out len)
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem project_fields (s t r : Store NearState) (h : fields t=fields r)
    (hf : r.funcs=s.funcs) (hm : r.modules=s.modules) (ht : r.tables=s.tables) :
    t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables ∧t.globals=r.globals := by
  have a : t.funcs=r.funcs:=congrArg (fun x=>x.1) h
  have b : t.modules=r.modules:=congrArg (fun x=>x.2.1) h
  have c : t.tables=r.tables:=congrArg (fun x=>x.2.2.1) h
  have d : t.globals=r.globals:=congrArg (fun x=>x.2.2.2) h
  exact ⟨a.trans hf,b.trans hm,c.trans ht,d⟩
attribute [local irreducible] fields reservedPrefix guardedPrefix takenPrefix wordPrefix statusPrefix droppedPrefix advancedPrefix
  countedPrefix lengthPrefix lengthCheckedPrefix enoughPrefix payloadPrefix
private theorem reserved_arrays (s : Store NearState) (op : Nat) (p : Layout) :
    (reservedPrefix s op p).funcs=s.funcs ∧(reservedPrefix s op p).modules=s.modules ∧(reservedPrefix s op p).tables=s.tables := by
  simp only [reservedPrefix,setGlobal,paid_funcs,paid_modules,paid_tables,and_self]
theorem guardedPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (guardedPrefix s cfg.regularOpCost p).funcs=s.funcs ∧(guardedPrefix s cfg.regularOpCost p).modules=s.modules ∧(guardedPrefix s cfg.regularOpCost p).tables=s.tables ∧
    (guardedPrefix s cfg.regularOpCost p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (guardedPrefix s cfg.regularOpCost p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,fields_paid,]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (guardedPrefix s cfg.regularOpCost p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem takenPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (takenPrefix cfg s p).funcs=s.funcs ∧(takenPrefix cfg s p).modules=s.modules ∧(takenPrefix cfg s p).tables=s.tables ∧
    (takenPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (takenPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,fields_paid,fields_slice,]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (takenPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem wordPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (wordPrefix cfg s p).funcs=s.funcs ∧(wordPrefix cfg s p).modules=s.modules ∧(wordPrefix cfg s p).tables=s.tables ∧
    (wordPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (wordPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,fields_paid,fields_slice,fields_word,]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (wordPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem statusPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (statusPrefix cfg s p).funcs=s.funcs ∧(statusPrefix cfg s p).modules=s.modules ∧(statusPrefix cfg s p).tables=s.tables ∧
    (statusPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (statusPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,fields_paid,fields_slice,fields_word,]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (statusPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem droppedPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (droppedPrefix cfg s p).funcs=s.funcs ∧(droppedPrefix cfg s p).modules=s.modules ∧(droppedPrefix cfg s p).tables=s.tables ∧
    (droppedPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (droppedPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,droppedPrefix,dropFourAfter,fields_paid,fields_slice,fields_word,]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (droppedPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem advancedPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (advancedPrefix cfg s p).funcs=s.funcs ∧(advancedPrefix cfg s p).modules=s.modules ∧(advancedPrefix cfg s p).tables=s.tables ∧
    (advancedPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (advancedPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,droppedPrefix,dropFourAfter,advancedPrefix,advanceAfter,fields_paid,fields_slice,fields_word,fields_store64]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (advancedPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem countedPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (countedPrefix cfg s p).funcs=s.funcs ∧(countedPrefix cfg s p).modules=s.modules ∧(countedPrefix cfg s p).tables=s.tables ∧
    (countedPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (countedPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,droppedPrefix,dropFourAfter,advancedPrefix,advanceAfter,countedPrefix,fields_paid,fields_slice,fields_word,fields_store64]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (countedPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem lengthPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (lengthPrefix cfg s p).funcs=s.funcs ∧(lengthPrefix cfg s p).modules=s.modules ∧(lengthPrefix cfg s p).tables=s.tables ∧
    (lengthPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (lengthPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,droppedPrefix,dropFourAfter,advancedPrefix,advanceAfter,countedPrefix,lengthPrefix,lengthAfter,fields_paid,fields_slice,fields_word,fields_record,fields_store64]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (lengthPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem lengthCheckedPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (lengthCheckedPrefix cfg s p).funcs=s.funcs ∧(lengthCheckedPrefix cfg s p).modules=s.modules ∧(lengthCheckedPrefix cfg s p).tables=s.tables ∧
    (lengthCheckedPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (lengthCheckedPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,droppedPrefix,dropFourAfter,advancedPrefix,advanceAfter,countedPrefix,lengthPrefix,lengthAfter,lengthCheckedPrefix,fields_paid,fields_slice,fields_word,fields_record,fields_store64]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (lengthCheckedPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem enoughPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (enoughPrefix cfg s p).funcs=s.funcs ∧(enoughPrefix cfg s p).modules=s.modules ∧(enoughPrefix cfg s p).tables=s.tables ∧
    (enoughPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (enoughPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,droppedPrefix,dropFourAfter,advancedPrefix,advanceAfter,countedPrefix,lengthPrefix,lengthAfter,lengthCheckedPrefix,enoughPrefix,fields_paid,fields_slice,fields_word,fields_record,fields_store64]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (enoughPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
theorem payloadPrefix_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (payloadPrefix cfg s p).funcs=s.funcs ∧(payloadPrefix cfg s p).modules=s.modules ∧(payloadPrefix cfg s p).tables=s.tables ∧
    (payloadPrefix cfg s p).globals=(reservedPrefix s cfg.regularOpCost p).globals := by
  have h : fields (payloadPrefix cfg s p)=fields (reservedPrefix s cfg.regularOpCost p) := by
    simp only [guardedPrefix,takenPrefix,takeAfter,wordPrefix,wordAfter,statusPrefix,droppedPrefix,dropFourAfter,advancedPrefix,advanceAfter,countedPrefix,lengthPrefix,lengthAfter,lengthCheckedPrefix,enoughPrefix,payloadPrefix,fields_paid,fields_slice,fields_word,fields_record,fields_store64]
  have r:=reserved_arrays s cfg.regularOpCost p
  exact project_fields s (payloadPrefix cfg s p) (reservedPrefix s cfg.regularOpCost p) h r.1 r.2.1 r.2.2
end WNear.Proofs.StateDecodePrefix
