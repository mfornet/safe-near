import Proofs.StateDecodeScalarGlobals
import Proofs.StateDecodeScalarPhases

/-! Complete code, shadow-stack and functional host frames of the accepted scalar path. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private def codeFields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem code_paid (s : Store NearState) (op n : Nat) : codeFields (paid s op n)=codeFields s := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem code_charge (s : Store NearState) (op : Nat) : codeFields (chargedStore s op)=codeFields s:=rfl
private theorem code_global (s : Store NearState) (i : Nat) (v : Value) : codeFields (setGlobal s i v)=codeFields s:=rfl
private theorem code_word (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : codeFields (storeI64 s i a m v)=codeFields s:=rfl
private theorem code_tag (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : codeFields (storeI32 s i a m v)=codeFields s:=rfl
private theorem code_values (wide : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out : UInt32) (a b : UInt64) :
    codeFields (valuesStore wide s op i m out a b)=codeFields s := by
  cases wide <;> simp only [valuesStore,ite_true,Bool.false_eq_true,ite_false,store64Added,code_word,code_paid]
private theorem code_project (s t : Store NearState) (h : codeFields t=codeFields s) :
    t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables :=
  ⟨congrArg (fun x=>x.1) h,congrArg (fun x=>x.2.1) h,congrArg (fun x=>x.2.2) h⟩
private theorem code_from_fields (s t : Store NearState)
    (h:t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables ∧t.globals=s.globals) : codeFields t=codeFields s:=
  Prod.ext h.1 (Prod.ext h.2.1 h.2.2.1)

theorem after_fields (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after wide cfg s p).funcs=s.funcs ∧(after wide cfg s p).modules=s.modules ∧(after wide cfg s p).tables=s.tables := by
  have droppedEq:=code_from_fields (reserved s cfg.regularOpCost p) (dropped wide cfg s p) (dropped_fields wide cfg s p)
  apply code_project
  simp only [after,restored,finishStore,tagStore,updated,updateStore,store64Local,values,dropCached,
    code_charge,code_global,code_tag,code_word,code_values,code_paid,droppedEq,reserved]

private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem globals_charge (s : Store NearState) (op : Nat) : (chargedStore s op).globals=s.globals:=rfl
private theorem globals_word (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : (storeI64 s i a m v).globals=s.globals:=rfl
private theorem globals_tag (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : (storeI32 s i a m v).globals=s.globals:=rfl
private theorem globals_values (wide : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out : UInt32) (a b : UInt64) :
    (valuesStore wide s op i m out a b).globals=s.globals:=by
  cases wide <;> simp only [valuesStore,ite_true,Bool.false_eq_true,ite_false,store64Added,globals_word,globals_paid]

theorem after_globals (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (after wide cfg s p).globals=s.globals := by
  have dg: (dropped wide cfg s p).globals=(reserved s cfg.regularOpCost p).globals:=(dropped_fields wide cfg s p).2.2.2
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.global hg
  have endSP:scratch p+48=p.sp:=UInt32.sub_add_cancel _ _
  simp only [after,globals_charge,restored,finishStore,setGlobal,globals_paid,tagStore,globals_tag,
    updated,updateStore,store64Local,globals_word,values,globals_values,dropCached,dg,reserved]
  simpa only [setGlobal,hv,endSP] using restore

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (op : Nat) : view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) : view seed (setGlobal s i v).host=view seed s.host:=rfl
private theorem view_word (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : view seed (storeI64 s i a m v).host=view seed s.host:=rfl
private theorem view_tag (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_slices (seed : NearState) (drop : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out ptr len split : UInt32) :
    view seed (StateDecodeSlices.callAfter drop s op i m out ptr len split).host=view seed s.host:=by
  have h:=congrArg (view seed) (StateDecodeSlices.callAfter_host drop s op i m out ptr len split)
  exact h
private theorem view_words (seed : NearState) (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out ptr : UInt32) :
    view seed (StateDecodeWords.callAfter wide cfg s i m out ptr).host=view seed s.host:=by
  have h:=congrArg (view seed) (StateDecodeWords.callAfter_functional_host wide cfg s i m out ptr)
  exact h
private theorem view_values (seed : NearState) (wide : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out : UInt32) (a b : UInt64) :
    view seed (valuesStore wide s op i m out a b).host=view seed s.host:=by
  cases wide <;> simp only [valuesStore,ite_true,Bool.false_eq_true,ite_false,store64Added,view_word,view_paid]

theorem after_functional_host (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after wide cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after wide cfg s p).host=s.host
  simp only [after,restored,finishStore,tagStore,updated,updateStore,store64Local,values,dropCached,dropped,
    dropArguments,cached,accepted,readWords,wordArguments,taken,takeArguments,guarded,reserved,
    view_charge,view_global,view_tag,view_word,view_values,view_paid,view_slices,view_words]
  rfl

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_charge (s : Store NearState) (op : Nat) : (chargedStore s op).mems=s.mems:=rfl
private theorem mems_global (s : Store NearState) (i : Nat) (v : Value) : (setGlobal s i v).mems=s.mems:=rfl

private theorem added_memory (s : Store NearState) (op i : Nat) (m : Memory) (out delta : UInt32) (v : UInt64)
    (hm:s.mems[i]?=some m) :
    (store64Added s op i m out delta v).mems[i]?=some (writeI64 m (out+delta).toNat v) := by
  unfold store64Added
  apply storeI64_memory
  rw[mems_paid]
  exact hm

private theorem values_memory_generic (wide : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out : UInt32) (a b : UInt64)
    (hm:s.mems[i]?=some m) :
    (valuesStore wide s op i m out a b).mems[i]?=some
      (if wide then writeI64 (writeI64 m (out+16).toNat a) (out+8).toNat b else writeI64 m (out+8).toNat a) := by
  cases wide
  · exact added_memory s op i m out 8 a hm
  · have h:=added_memory s op i m out 16 a hm
    exact added_memory _ op i (firstValueMemory m out a) out 8 b h

theorem values_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm:s.mems[p.memoryIndex]?=some p.memory) :
    (values wide cfg s p).mems[p.memoryIndex]?=some (valuesMemory wide p) := by
  have hd:(dropCached wide cfg s p).mems[p.memoryIndex]?=some (droppedMemory wide p):=by
    rw[dropCached,mems_paid]
    exact dropped_memory wide cfg s p hm
  have h:=values_memory_generic wide (dropCached wide cfg s p) cfg.regularOpCost p.memoryIndex (droppedMemory wide p) p.out
    (if wide then highValue p else lowValue wide p) (lowValue wide p) hd
  cases wide <;> simpa only [values,valuesMemory,ite_true,Bool.false_eq_true,ite_false] using h

theorem updated_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm:s.mems[p.memoryIndex]?=some p.memory) :
    (updated wide cfg s p).mems[p.memoryIndex]?=some (updatedMemory wide p) := by
  have h:=values_memory wide cfg s p hm
  unfold updated updateStore
  rw[mems_paid]
  unfold store64Local
  apply storeI64_memory
  rw[mems_paid]
  exact h

theorem after_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm:s.mems[p.memoryIndex]?=some p.memory) :
    (after wide cfg s p).mems[p.memoryIndex]?=some (finalMemory wide p) := by
  have h:=updated_memory wide cfg s p hm
  simp only [after,mems_charge,restored,finishStore,mems_global,mems_paid,tagStore]
  apply storeI32_memory
  rw[mems_paid]
  exact h

end WNear.Proofs.StateDecodeScalar
