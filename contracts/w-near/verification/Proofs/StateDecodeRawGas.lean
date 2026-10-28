import Proofs.StateDecodeRawPhases
import Proofs.StateDecodeRawCopyGas
import Proofs.AllocateVectorGas

/-! Exact ordinary ledgers for f767's selected direct nonzeroing path. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
private theorem global_units (s : Store NearState) (op n i : Nat) (v : Value) :
    GasUnits s (setGlobal (paid s op n) i v) op n := (gasUnits_paid s op n).host_eq rfl
attribute [local irreducible] reservedRaw layoutArgumentsRaw laidOutRaw alignedRaw checkedRaw flagCheckedRaw argumentsRaw
  allocatedRaw cachedRaw afterRaw callAfterRaw AllocateVector.finished

theorem laidOutRaw_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (laidOutRaw s op p) op 87 := by
  have reserve : GasUnits s (reservedRaw s op p) op 5 := by
    unfold reservedRaw
    exact global_units s op 5 p.globalIndex (.i32 (scratch p))
  have arguments : GasUnits s (layoutArgumentsRaw s op p) op 9 := by
    simpa only [layoutArgumentsRaw,Nat.reduceAdd] using reserve.trans (gasUnits_paid (reservedRaw s op p) op 4)
  have callee : GasUnits (layoutArgumentsRaw s op p) (AllocateLayoutWrapper.called (layoutArgumentsRaw s op p) op (layout752 p)) op 78 := by
    intro rest hc;exact AllocateLayoutWrapper.called_gas _ op rest _ hc
  simpa only [laidOutRaw,Nat.reduceAdd] using arguments.trans callee
theorem alignedRaw_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (alignedRaw s op p) op 92 := by
  simpa only [alignedRaw,Nat.reduceAdd] using (laidOutRaw_gas s op p).trans (gasUnits_paid (laidOutRaw s op p) op 5)
theorem checkedRaw_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (checkedRaw s op p) op 98 := by
  simpa only [checkedRaw,Nat.reduceAdd] using (alignedRaw_gas s op p).trans (gasUnits_paid (alignedRaw s op p) op 6)
theorem flagCheckedRaw_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (flagCheckedRaw s op p) op 101 := by
  simpa only [flagCheckedRaw,Nat.reduceAdd] using (checkedRaw_gas s op p).trans (gasUnits_paid (checkedRaw s op p) op 3)
theorem argumentsRaw_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (argumentsRaw s op p) op 106 := by
  simpa only [argumentsRaw,Nat.reduceAdd] using (flagCheckedRaw_gas s op p).trans (gasUnits_paid (flagCheckedRaw s op p) op 5)
theorem allocatedRaw_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (allocatedRaw cfg s p) cfg.regularOpCost 553 := by
  simpa only [allocatedRaw,Nat.reduceAdd] using (argumentsRaw_gas s cfg.regularOpCost p).trans
    (callAfter769_gas cfg (argumentsRaw s cfg.regularOpCost p) p)
theorem cachedRaw_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (cachedRaw cfg s p) cfg.regularOpCost 559 := by
  simpa only [cachedRaw,Nat.reduceAdd] using (allocatedRaw_gas cfg s p).trans
    (gasUnits_paid (allocatedRaw cfg s p) cfg.regularOpCost 6)
private theorem finished_gas (s : Store NearState) (op i g : Nat) (m : Memory) (out ptr len scratch : UInt32) :
    GasUnits s (finished s op i g m out ptr len scratch) op 14 := by
  have guard:=gasUnits_paid s op 3
  have record:=AllocateVector.recordStore_gas (paid s op 3) op i m out ptr len
  have restore:=global_units (AllocateVector.recordStore (paid s op 3) op i m out ptr len) op 4 g (.i32 (scratch+32))
  have ret:=gasUnits_charge (setGlobal (paid (AllocateVector.recordStore (paid s op 3) op i m out ptr len) op 4) g (.i32 (scratch+32))) op 1
  simpa only [finished,AllocateVector.finished,Nat.reduceAdd,Nat.one_mul] using ((guard.trans record).trans restore).trans ret
theorem afterRaw_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (afterRaw cfg s p) cfg.regularOpCost 573 := by
  simpa only [afterRaw,Nat.reduceAdd] using (cachedRaw_gas cfg s p).trans
    (finished_gas (cachedRaw cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memory769 p)
      p.outRaw (cachedPointer p) (cachedLength p) (scratch p))
theorem callAfterRaw_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (callAfterRaw cfg s p) cfg.regularOpCost 585 := by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only [Nat.one_mul] at one
  have enter : GasUnits s (enteredRaw s cfg.regularOpCost) cfg.regularOpCost 12 :=
    one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 11)
  simpa only [callAfterRaw,Nat.reduceAdd] using enter.trans (afterRaw_gas cfg (enteredRaw s cfg.regularOpCost) p)
end WNear.Proofs.StateDecodeRaw
