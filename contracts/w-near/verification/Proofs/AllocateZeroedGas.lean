import Proofs.AllocateZeroedBody

/-! Exact symbolic billing of the actual allocate-and-zero path. -/
namespace WNear.Proofs.AllocateZeroed
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
attribute [local irreducible] arguments allocated checked fillArguments filled after

 theorem gasUnits_allocated (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (allocated s op p) op 361 := by
  have a : GasUnits s (arguments s op) op 3 := by simpa only [arguments] using gasUnits_paid s op 3
  have b := a.trans (AllocatePositive.gasUnits_callAfter (arguments s op) op p.toLayout)
  simpa only [allocated,Nat.reduceAdd] using b
 theorem gasUnits_fillArguments (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (fillArguments s op p) op 367 := by
  have a := (gasUnits_allocated s op p).trans (gasUnits_paid (allocated s op p) op 3)
  have aa : GasUnits s (checked s op p) op 364 := by simpa only [checked,Nat.reduceAdd] using a
  have b := aa.trans (gasUnits_paid (checked s op p) op 3)
  simpa only [fillArguments,Nat.reduceAdd] using b
 theorem gasUnits_after (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (after s op p) op (bodyCost p) := by
  have fill : GasUnits (fillArguments s op p) (filled s op p) op (ZeroFill.bodyCost p.size+11) := by
    intro rest hc
    simpa only [filled] using ZeroFill.callAfter_gas (fillArguments s op p) op p.memoryIndex rest (allocatedMemory p) (result p) 0 p.size hc
  have a := (gasUnits_fillArguments s op p).trans fill
  have b := a.trans (gasUnits_paid (filled s op p) op 2)
  have n : 367+(ZeroFill.bodyCost p.size+11)+2=bodyCost p := by simp only [bodyCost];omega
  simpa only [after,n] using b
 theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (bodyCost p*op+rest)) :
    (after s op p).host.gas.Credits rest := (gasUnits_after s op p rest hc).2.2
 theorem after_gas (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (bodyCost p*op+rest)) :
    (after s op p).host.gas.burnt=s.host.gas.burnt+bodyCost p*op ∧
    (after s op p).host.gas.promises=s.host.gas.promises ∧ (after s op p).host.gas.Credits rest :=
  gasUnits_after s op p rest hc
end WNear.Proofs.AllocateZeroed
