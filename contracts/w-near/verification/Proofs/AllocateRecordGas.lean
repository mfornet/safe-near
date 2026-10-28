import Proofs.AllocateRecordState

/-! Exact689 charges, including the unique allocation growth fee. -/
namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
open AllocateGrowth (GasCost)
attribute [local irreducible] allocated selected after

theorem allocated_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (allocated cfg s p) ((AllocateZeroedRetry.bodyCost p.toZeroed+48)*cfg.regularOpCost+fee cfg p) := by
  have all := (GasCost.of_units (gasUnits_paid s cfg.regularOpCost 8)).trans
    (AllocateForwardRetry.callAfter313_gas cfg (paid s cfg.regularOpCost 8) p.toZeroed)
  have ce : 8*cfg.regularOpCost+((AllocateForwardRetry.cost313 p.toZeroed+11)*cfg.regularOpCost+
      AllocateForwardRetry.fee cfg p.toZeroed)=(AllocateZeroedRetry.bodyCost p.toZeroed+48)*cfg.regularOpCost+fee cfg p := by
    simp only [AllocateForwardRetry.cost313,AllocateForwardRetry.cost239,AllocateForwardRetry.fee,fee,Nat.add_mul];omega
  simpa only [allocated,ce] using all
 theorem selected_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (selected cfg s p) ((AllocateZeroedRetry.bodyCost p.toZeroed+50)*cfg.regularOpCost+fee cfg p) := by
  have all := (allocated_gas cfg s p).trans (GasCost.of_units (gasUnits_paid (allocated cfg s p) cfg.regularOpCost 2))
  have ce : (AllocateZeroedRetry.bodyCost p.toZeroed+48)*cfg.regularOpCost+fee cfg p+2*cfg.regularOpCost=
      (AllocateZeroedRetry.bodyCost p.toZeroed+50)*cfg.regularOpCost+fee cfg p := by simp only [Nat.add_mul];omega
  simpa only [selected,ce] using all

private theorem store_units (s : Store NearState) (op n index address : Nat) (memory : Memory) (value : UInt32) :
    GasUnits s (storeI32 (paid s op n) index address memory value) op n :=
  (gasUnits_paid s op n).host_eq rfl
 theorem recordStore_gas (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer size : UInt32) :
    GasUnits s (recordStore s op index memory out pointer size) op 6 := by
  have a := store_units s op 3 index (out.toNat+4) memory size
  have b := a.trans (store_units _ op 3 index out.toNat (writeI32 memory (out.toNat+4) size) pointer)
  simpa only [recordStore,Nat.reduceAdd] using b
 theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after cfg s p) (bodyCost p*cfg.regularOpCost+fee cfg p) := by
  have all := (selected_gas cfg s p).trans (GasCost.of_units
    (recordStore_gas (selected cfg s p) cfg.regularOpCost p.memoryIndex (allocatedMemory p) p.out (result p) p.size))
  have ce : (AllocateZeroedRetry.bodyCost p.toZeroed+50)*cfg.regularOpCost+fee cfg p+6*cfg.regularOpCost=
      bodyCost p*cfg.regularOpCost+fee cfg p := by simp only [bodyCost,Nat.add_mul];omega
  simpa only [after,ce] using all
 theorem after_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest)) :
    (after cfg s p).host.gas.Credits rest := (after_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateRecord
