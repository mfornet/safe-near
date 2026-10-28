import Proofs.StateDecodeScalarPhases
import Proofs.StateDecodeSlicesGas
import Proofs.StateDecodeWordsGas

/-! Exact ordinary gas for every accepted scalar-reader phase. These equations
need no memory, branch, code-installation, or whole-execution assumptions. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384

private theorem units_set (s : Store NearState) (op n index : Nat) (v : Value) :
    GasUnits s (setGlobal (paid s op n) index v) op n :=
  (gasUnits_paid s op n).host_eq rfl
private theorem units_added (s : Store NearState) (op index : Nat) (memory : Memory)
    (out offset : UInt32) (v : UInt64) :
    GasUnits s (store64Added s op index memory out offset v) op 5 :=
  (gasUnits_paid s op 5).host_eq rfl
private theorem units_values (wide : Bool) (s : Store NearState) (op index : Nat)
    (memory : Memory) (out : UInt32) (a b : UInt64) :
    GasUnits s (valuesStore wide s op index memory out a b) op (if wide then 10 else 5) := by
  cases wide
  · exact units_added s op index memory out 8 a
  · exact (units_added s op index memory out 16 a).trans
      (units_added (store64Added s op index memory out 16 a) op index (firstValueMemory memory out a) out 8 b)
private theorem units_update (s : Store NearState) (op index : Nat) (memory : Memory) (slice : UInt32) (v : UInt64) :
    GasUnits s (updateStore s op index memory slice v) op 5 := by
  have a : GasUnits s (store64Local s op index memory slice v) op 3 := (gasUnits_paid s op 3).host_eq rfl
  exact a.trans (gasUnits_paid (store64Local s op index memory slice v) op 2)
private theorem units_finish (s : Store NearState) (op index gi : Nat) (memory : Memory) (out scratch : UInt32) :
    GasUnits s (finishStore s op index gi memory out scratch) op 7 := by
  have a : GasUnits s (tagStore s op index memory out) op 3 := (gasUnits_paid s op 3).host_eq rfl
  exact a.trans (units_set (tagStore s op index memory out) op 4 gi (.i32 (scratch+48)))

attribute [local irreducible] reserved guarded takeArguments taken wordArguments readWords accepted cached
  dropArguments dropped dropCached values updated restored after

theorem reserved_gas (_wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (reserved s cfg.regularOpCost p) cfg.regularOpCost 5 := by
  unfold reserved
  exact units_set s cfg.regularOpCost 5 p.globalIndex (.i32 (scratch p))

theorem guarded_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (guarded s cfg.regularOpCost p) cfg.regularOpCost 11 := by
  have step := gasUnits_paid (reserved s cfg.regularOpCost p) cfg.regularOpCost 6
  have h := (reserved_gas wide cfg s p).trans step
  simpa only [guarded,Nat.reduceAdd] using h

theorem takeArguments_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (takeArguments s cfg.regularOpCost p) cfg.regularOpCost 19 := by
  have step := gasUnits_paid (guarded s cfg.regularOpCost p) cfg.regularOpCost 8
  have h := (guarded_gas wide cfg s p).trans step
  simpa only [takeArguments,Nat.reduceAdd] using h

theorem taken_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (taken wide s cfg.regularOpCost p) cfg.regularOpCost 41 := by
  have step := StateDecodeSlices.callAfter_units false (takeArguments s cfg.regularOpCost p) cfg.regularOpCost p.memoryIndex p.memory (takeOut wide p) p.pointer p.length (width wide)
  have h := (takeArguments_gas wide cfg s p).trans step
  simpa only [taken,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost, Bool.false_eq_true, ite_false] using h

theorem wordArguments_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (wordArguments wide s cfg.regularOpCost p) cfg.regularOpCost 48 := by
  have step := gasUnits_paid (taken wide s cfg.regularOpCost p) cfg.regularOpCost 7
  have h := (taken_gas wide cfg s p).trans step
  simpa only [wordArguments,Nat.reduceAdd] using h

theorem readWords_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (readWords wide cfg s p) cfg.regularOpCost (if wide then 82 else 74) := by
  have step : GasUnits (wordArguments wide s cfg.regularOpCost p) (StateDecodeWords.callAfter wide cfg (wordArguments wide s cfg.regularOpCost p) p.memoryIndex (takenMemory wide p) (wordOut wide p) p.pointer) cfg.regularOpCost (StateDecodeWords.bodyCost wide+11) := (fun rest hc => StateDecodeWords.callAfter_gas wide cfg (wordArguments wide s cfg.regularOpCost p) p.memoryIndex rest (takenMemory wide p) (wordOut wide p) p.pointer hc)
  have h := (wordArguments_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,readWords,Nat.reduceAdd,StateDecodeWords.bodyCost,StateDecodeWords.copyCost] using h

theorem accepted_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (accepted wide cfg s p) cfg.regularOpCost (if wide then 87 else 79) := by
  have step := gasUnits_paid (readWords wide cfg s p) cfg.regularOpCost 5
  have h := (readWords_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,accepted,Nat.reduceAdd] using h

theorem cached_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (cached wide cfg s p) cfg.regularOpCost (if wide then 95 else 82) := by
  have step := gasUnits_paid (accepted wide cfg s p) cfg.regularOpCost (if wide then 8 else 3)
  have h := (accepted_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,cached,Nat.reduceAdd] using h

theorem dropArguments_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (dropArguments wide cfg s p) cfg.regularOpCost (if wide then 102 else 91) := by
  have step := gasUnits_paid (cached wide cfg s p) cfg.regularOpCost (if wide then 7 else 9)
  have h := (cached_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,dropArguments,Nat.reduceAdd] using h

theorem dropped_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (dropped wide cfg s p) cfg.regularOpCost (if wide then 128 else 117) := by
  have step := StateDecodeSlices.callAfter_units true (dropArguments wide cfg s p) cfg.regularOpCost p.memoryIndex (wordMemory wide p) (dropOut wide p) p.pointer p.length (width wide)
  have h := (dropArguments_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,dropped,Nat.reduceAdd,WNear.Binary.StateDecodeSlices.bodyCost, ite_true] using h

theorem dropCached_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (dropCached wide cfg s p) cfg.regularOpCost (if wide then 131 else 120) := by
  have step := gasUnits_paid (dropped wide cfg s p) cfg.regularOpCost 3
  have h := (dropped_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,dropCached,Nat.reduceAdd] using h

theorem values_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (values wide cfg s p) cfg.regularOpCost (if wide then 141 else 125) := by
  have step := units_values wide (dropCached wide cfg s p) cfg.regularOpCost p.memoryIndex (droppedMemory wide p) p.out (if wide then highValue p else lowValue wide p) (lowValue wide p)
  have h := (dropCached_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,values,Nat.reduceAdd] using h

theorem updated_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (updated wide cfg s p) cfg.regularOpCost (if wide then 146 else 130) := by
  have step := units_update (values wide cfg s p) cfg.regularOpCost p.memoryIndex (valuesMemory wide p) p.slice (dropValue wide p)
  have h := (values_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,updated,Nat.reduceAdd] using h

theorem restored_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (restored wide cfg s p) cfg.regularOpCost (if wide then 153 else 137) := by
  have step := units_finish (updated wide cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (updatedMemory wide p) p.out (scratch p)
  have h := (updated_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,restored,Nat.reduceAdd] using h

theorem after_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (after wide cfg s p) cfg.regularOpCost (if wide then 154 else 138) := by
  have step := gasUnits_charge (restored wide cfg s p) cfg.regularOpCost 1
  have h := (restored_gas wide cfg s p).trans step
  cases wide <;> simpa only [Bool.false_eq_true,ite_false,ite_true,after,Nat.reduceAdd,Nat.one_mul] using h

end WNear.Proofs.StateDecodeScalar
