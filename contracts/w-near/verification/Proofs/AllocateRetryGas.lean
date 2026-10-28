import Proofs.AllocateRetryState
import Proofs.AllocatePositiveGas

/-! Exact ordinary and linear growth gas through the actual581 retry stages. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] reserved prefixed firstAttempt firstMiss beforeGrow grown checked oldLinked relinked retried found updated after
  AllocateGrowth.callAfter AllocateGrowth.delta memoryGrowCost growthLayout AllocateFlagged.callAfter AllocateEmpty.callAfter

theorem gasUnits_reserved (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (reserved s op p) op 5 := by
  simpa only [reserved] using AllocatePositive.gasUnits_reserved s op p.toLayout

theorem gasUnits_prefixed (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (prefixed s op p) op 54 := by
  simpa only [prefixed] using AllocatePositive.gasUnits_prefixed s op p.toLayout

private theorem empty_units (s : Store NearState) (op : Nat) : GasUnits s (AllocateEmpty.callAfter s op) op 37 := by
  intro rest hc
  exact AllocateEmpty.callAfter_gas s op rest hc

theorem gasUnits_firstAttempt (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (firstAttempt s op p) op 98 := by
  have a := (gasUnits_prefixed s op p).trans (gasUnits_paid (prefixed s op p) op 7)
  simpa only [firstAttempt,Nat.reduceAdd] using a.trans (empty_units (paid (prefixed s op p) op 7) op)

theorem gasUnits_beforeGrow (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (beforeGrow s op p) op 104 := by
  have a : GasUnits s (firstMiss s op p) op 100 := by
    simpa only [firstMiss,Nat.reduceAdd] using (gasUnits_firstAttempt s op p).trans (gasUnits_paid (firstAttempt s op p) op 2)
  simpa only [beforeGrow,firstMiss,Nat.reduceAdd] using a.trans (gasUnits_paid (firstMiss s op p) op 4)

theorem grown_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (grown cfg s p) (282*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  have b : GasCost (beforeGrow s cfg.regularOpCost p) (grown cfg s p)
      (178*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
    intro rest hc
    have h := AllocateGrowth.callAfter_gas cfg (beforeGrow s cfg.regularOpCost p) (growthLayout p) rest hc
    simpa only [grown,Nat.add_assoc] using h
  have all := (GasCost.of_units (gasUnits_beforeGrow s cfg.regularOpCost p)).trans b
  have cost : 104*cfg.regularOpCost+(178*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p)))=
      282*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p)) := by omega
  simpa only [cost] using all

private theorem plus_units {s t u : Store NearState} {op fee n m : Nat}
    (first : GasCost s t (n*op+fee)) (second : GasUnits t u op m) : GasCost s u ((n+m)*op+fee) := by
  have h := first.trans (GasCost.of_units second)
  have cost : n*op+fee+m*op=(n+m)*op+fee := by rw [Nat.add_mul];omega
  simpa only [cost] using h

theorem checked_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (checked cfg s p) (287*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  simpa only [checked,Nat.reduceAdd] using plus_units (grown_gas cfg s p) (gasUnits_paid (grown cfg s p) cfg.regularOpCost 5)

private theorem units_store32 (s : Store NearState) (op n index address : Nat) (memory : Memory) (v : UInt32) :
    GasUnits s (storeI32 (paid s op n) index address memory v) op n :=
  (gasUnits_paid s op n).host_eq rfl
private theorem units_global (s : Store NearState) (op n index : Nat) (v : Value) :
    GasUnits s (setGlobal (paid s op n) index v) op n :=
  (gasUnits_paid s op n).host_eq rfl

theorem oldLinked_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (oldLinked cfg s p) (293*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  have tail := units_store32 (checked cfg s p) cfg.regularOpCost 6 p.memoryIndex
    ((AllocateGrowth.header (growthLayout p)).toNat+8) (AllocateGrowth.finalMemory (growthLayout p))
    (readI32 (AllocateGrowth.finalMemory (growthLayout p)) ((scratch p).toNat+12))
  simpa only [oldLinked,Nat.reduceAdd] using plus_units (checked_gas cfg s p) tail

theorem relinked_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (relinked cfg s p) (296*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  have tail := units_store32 (oldLinked cfg s p) cfg.regularOpCost 3 p.memoryIndex ((scratch p).toNat+12)
    (writeI32 (AllocateGrowth.finalMemory (growthLayout p)) ((AllocateGrowth.header (growthLayout p)).toNat+8)
      (readI32 (AllocateGrowth.finalMemory (growthLayout p)) ((scratch p).toNat+12)))
    (AllocateGrowth.header (growthLayout p))
  simpa only [relinked,Nat.reduceAdd] using plus_units (oldLinked_gas cfg s p) tail

theorem retried_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (retried cfg s p) (581*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  have a := plus_units (relinked_gas cfg s p) (gasUnits_paid (relinked cfg s p) cfg.regularOpCost 7)
  simpa only [retried,Nat.reduceAdd] using plus_units a
    (AllocateFlagged.gasUnits_callAfter (paid (relinked cfg s p) cfg.regularOpCost 7) cfg.regularOpCost (secondLayout p))

theorem found_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (found cfg s p) (582*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  simpa only [found,Nat.reduceAdd] using plus_units (retried_gas cfg s p) (gasUnits_paid (retried cfg s p) cfg.regularOpCost 1)

theorem updated_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (updated cfg s p) (586*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  have tail := units_store32 (found cfg s p) cfg.regularOpCost 4 p.memoryIndex p.allocator.toNat (searchedMemory p)
    (readI32 (searchedMemory p) ((scratch p).toNat+12))
  simpa only [updated,Nat.reduceAdd] using plus_units (found_gas cfg s p) tail

theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after cfg s p) (591*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (growthLayout p))) := by
  have global := units_global (updated cfg s p) cfg.regularOpCost 4 p.globalIndex (.i32 p.sp)
  have a := plus_units (updated_gas cfg s p) global
  simpa only [after,Nat.reduceAdd] using plus_units a
    (gasUnits_paid (setGlobal (paid (updated cfg s p) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp)) cfg.regularOpCost 1)
end WNear.Proofs.AllocateRetry
