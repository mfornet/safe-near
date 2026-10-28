import Proofs.AllocateZeroedRetryState
import Proofs.AllocateRetryGas

/-! Exact ordinary charges and one unrounded linear-growth fee for153retry. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_charge gasUnits_paid)
open AllocateGrowth (GasCost)
attribute [local irreducible] allocated after AllocateZeroed.tailAfter AllocateZeroed.tailFilled

theorem allocated_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (allocated cfg s p) (606*cfg.regularOpCost+fee cfg p) := by
  let op := cfg.regularOpCost
  have a := gasUnits_paid s op 3
  have b := gasUnits_charge (arguments s op) op 1
  simp only [Nat.one_mul] at b
  have c := gasUnits_charge (chargedStore (arguments s op) op) op 11
  have abc := (a.trans b).trans c
  have initial : GasCost s (allocateEntered (arguments s op) op) (15*op) := by
    simpa only [arguments,allocateEntered,Nat.reduceAdd] using GasCost.of_units abc
  have all := initial.trans (AllocateRetry.after_gas cfg (allocateEntered (arguments s op) op) p.toRetry)
  have ce : 15*op+(591*cfg.regularOpCost+memoryGrowCost cfg (AllocateGrowth.delta (AllocateRetry.growthLayout p.toRetry)))=
      606*cfg.regularOpCost+fee cfg p := by simp only [fee,op];omega
  simpa only [allocated,op,ce] using all

theorem tail_units (s : Store NearState) (op index : Nat) (memory : Memory) (ptr len : UInt32) :
    GasUnits s (AllocateZeroed.tailAfter s op index memory ptr len) op (ZeroFill.bodyCost len+19) := by
  have a := (gasUnits_paid s op 3).trans (gasUnits_paid (paid s op 3) op 3)
  have fill : GasUnits (paid (paid s op 3) op 3)
      (ZeroFill.callAfter (paid (paid s op 3) op 3) op index memory ptr 0 len) op (ZeroFill.bodyCost len+11) := by
    intro rest hc
    exact ZeroFill.callAfter_gas _ op index rest memory ptr 0 len hc
  have b := a.trans fill
  have c := b.trans (gasUnits_paid _ op 2)
  have ce : (3+3)+(ZeroFill.bodyCost len+11)+2=ZeroFill.bodyCost len+19 := by omega
  simpa only [AllocateZeroed.tailAfter,AllocateZeroed.tailFilled,ce] using c

theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after cfg s p) (bodyCost p*cfg.regularOpCost+fee cfg p) := by
  have all := (allocated_gas cfg s p).trans (GasCost.of_units
    (tail_units (allocated cfg s p) cfg.regularOpCost p.memoryIndex (allocatedMemory p) (result p) p.size))
  have ce : 606*cfg.regularOpCost+fee cfg p+(ZeroFill.bodyCost p.size+19)*cfg.regularOpCost=
      bodyCost p*cfg.regularOpCost+fee cfg p := by simp only [bodyCost,Nat.add_mul];omega
  simpa only [after,ce] using all
 theorem after_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest)) :
    (after cfg s p).host.gas.Credits rest := (after_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateZeroedRetry
