import Proofs.AllocateVectorOuterPhases
import Proofs.AllocateVectorGas

/-! Actual687 accounting: fourteen prefix instructions, real686 activation/body,
and fourteen tail instructions. The growth fee is charged once. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] reserved guarded arguments allocated after vectorEntered

theorem reserved_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (reserved s op p) op 5 := by
  unfold reserved
  exact (gasUnits_paid s op 5).host_eq rfl

theorem guarded_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (guarded s op p) op 9 := by
  have h := (reserved_gas s op p).trans (gasUnits_paid (reserved s op p) op 4)
  simpa only [guarded,Nat.reduceAdd] using h

theorem arguments_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (arguments s op p) op 14 := by
  have h := (guarded_gas s op p).trans (gasUnits_paid (guarded s op p) op 5)
  simpa only [arguments,Nat.reduceAdd] using h

theorem vectorEntered_gas (s : Store NearState) (op : Nat) : GasUnits s (vectorEntered s op) op 12 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have h := first.trans (gasUnits_charge (chargedStore s op) op 11)
  simpa only [vectorEntered,Nat.one_mul,Nat.reduceAdd] using h

theorem allocated_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (allocated cfg s p) ((AllocateVector.bodyCost p.toVector+26)*cfg.regularOpCost+fee cfg p) := by
  let op := cfg.regularOpCost
  have pref :=  (arguments_gas s op p).trans (vectorEntered_gas (arguments s op p) op)
  have body := AllocateVector.after_gas cfg (vectorEntered (arguments s op p) op) p.toVector
  have all := (GasCost.of_units pref).trans body
  have ce : (14+12)*op+(AllocateVector.bodyCost p.toVector*op+AllocateVector.fee cfg p.toVector)=
      (AllocateVector.bodyCost p.toVector+26)*cfg.regularOpCost+fee cfg p := by
    simp only [fee,Nat.add_mul,op];omega
  rw [ce] at all
  simpa only [allocated,op] using all

theorem allocated_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((AllocateVector.bodyCost p.toVector+26)*cfg.regularOpCost+fee cfg p+rest)) :
    (allocated cfg s p).host.gas.Credits rest := (allocated_gas cfg s p rest hc).2.2

theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after cfg s p) (bodyCost p*cfg.regularOpCost+fee cfg p) := by
  have tail := tailAfter_gas (allocated cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex
    (allocatedMemory p) p.out687 p.size p.outerSP
  have all := (allocated_gas cfg s p).trans (GasCost.of_units tail)
  have ce : (AllocateVector.bodyCost p.toVector+26)*cfg.regularOpCost+fee cfg p+14*cfg.regularOpCost=
      bodyCost p*cfg.regularOpCost+fee cfg p := by simp only [bodyCost,Nat.add_mul];omega
  rw [ce] at all
  simpa only [after] using all

theorem after_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest)) :
    (after cfg s p).host.gas.Credits rest := (after_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateVectorOuter
