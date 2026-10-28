import Proofs.StateDecodeScalarMemory

/-! Actual phase memory and unchanged code/global arrays before the final restore. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems := rfl

private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem fields_mk (s t : Store NearState)
    (h : t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables ∧t.globals=s.globals) : fields t=fields s :=
  Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2))
private theorem fields_slices (drop : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out ptr len split : UInt32) :
    fields (StateDecodeSlices.callAfter drop s op i m out ptr len split)=fields s := by
  have h:=StateDecodeSlices.callAfter_fields drop s op i m out ptr len split
  exact fields_mk s _ h
private theorem fields_words (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out ptr : UInt32) :
    fields (StateDecodeWords.callAfter wide cfg s i m out ptr)=fields s := by
  have h:=StateDecodeWords.callAfter_fields wide cfg s i m out ptr
  exact fields_mk s _ h

private theorem project (s t : Store NearState) (h : fields t=fields s) :
    t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables ∧ t.globals=s.globals :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2.1) h,congrArg (fun x=>x.2.2.2) h⟩

theorem taken_fields (wide : Bool) (s : Store NearState) (op : Nat) (p : Layout) :
    (taken wide s op p).funcs=(reserved s op p).funcs ∧
    (taken wide s op p).modules=(reserved s op p).modules ∧
    (taken wide s op p).tables=(reserved s op p).tables ∧
    (taken wide s op p).globals=(reserved s op p).globals := by
  apply project
  simp only [taken,takeArguments,guarded,fields_slices,fields_paid]

theorem readWords_fields (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (readWords wide cfg s p).funcs=(reserved s cfg.regularOpCost p).funcs ∧
    (readWords wide cfg s p).modules=(reserved s cfg.regularOpCost p).modules ∧
    (readWords wide cfg s p).tables=(reserved s cfg.regularOpCost p).tables ∧
    (readWords wide cfg s p).globals=(reserved s cfg.regularOpCost p).globals := by
  apply project
  simp only [readWords,wordArguments,taken,takeArguments,guarded,fields_words,fields_slices,fields_paid]

theorem dropped_fields (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (dropped wide cfg s p).funcs=(reserved s cfg.regularOpCost p).funcs ∧
    (dropped wide cfg s p).modules=(reserved s cfg.regularOpCost p).modules ∧
    (dropped wide cfg s p).tables=(reserved s cfg.regularOpCost p).tables ∧
    (dropped wide cfg s p).globals=(reserved s cfg.regularOpCost p).globals := by
  apply project
  simp only [dropped,dropArguments,cached,accepted,readWords,wordArguments,taken,takeArguments,guarded,
    fields_words,fields_slices,fields_paid]

theorem takeArguments_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (takeArguments s op p).mems[p.memoryIndex]?=some p.memory := by
  simp only [takeArguments,guarded,reserved,mems_paid,mems_global]
  exact hm

theorem taken_memory (wide : Bool) (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (taken wide s op p).mems[p.memoryIndex]?=some (takenMemory wide p) :=
  StateDecodeSlices.callAfter_memory false (takeArguments s op p) op p.memoryIndex p.memory (takeOut wide p) p.pointer p.length (width wide)
    (takeArguments_memory s op p hm)

theorem wordArguments_memory (wide : Bool) (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (wordArguments wide s op p).mems[p.memoryIndex]?=some (takenMemory wide p) := by
  rw [wordArguments,mems_paid]
  exact taken_memory wide s op p hm

theorem readWords_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (readWords wide cfg s p).mems[p.memoryIndex]?=some (wordMemory wide p) :=
  StateDecodeWords.callAfter_memory wide cfg (wordArguments wide s cfg.regularOpCost p) p.memoryIndex (takenMemory wide p)
    (wordOut wide p) p.pointer (wordArguments_memory wide s cfg.regularOpCost p hm)

theorem dropArguments_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (dropArguments wide cfg s p).mems[p.memoryIndex]?=some (wordMemory wide p) := by
  simp only [dropArguments,cached,accepted,mems_paid]
  exact readWords_memory wide cfg s p hm

theorem dropped_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (dropped wide cfg s p).mems[p.memoryIndex]?=some (droppedMemory wide p) :=
  StateDecodeSlices.callAfter_memory true (dropArguments wide cfg s p) cfg.regularOpCost p.memoryIndex (wordMemory wide p)
    (dropOut wide p) p.pointer p.length (width wide) (dropArguments_memory wide cfg s p hm)

end WNear.Proofs.StateDecodeScalar
