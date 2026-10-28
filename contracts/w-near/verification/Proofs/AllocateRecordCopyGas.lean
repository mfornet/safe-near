import Proofs.AllocateRecordCopyState
import Proofs.AllocateRecordGas

/-! Exact690 phase charges with a single inherited linear growth fee. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] reserved arguments recordEntered allocated copyDone after copied copyWord

private theorem global_units (s : Store NearState) (op n index : Nat) (value : Value) :
    GasUnits s (setGlobal (paid s op n) index value) op n :=
  (gasUnits_paid s op n).host_eq rfl
private theorem store_units (s : Store NearState) (op n index address : Nat) (memory : Memory) (value : UInt32) :
    GasUnits s (storeI32 (paid s op n) index address memory value) op n :=
  (gasUnits_paid s op n).host_eq rfl

theorem reserved_gas (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (reserved s op p) op 5 := by
  unfold reserved
  exact global_units s op 5 p.inner.globalIndex (.i32 p.inner.sp)
theorem arguments_gas (s : Store NearState) (op : Nat) (p : Layout) :
    GasUnits s (arguments s op p) op 11 := by
  have h := (reserved_gas s op p).trans (gasUnits_paid (reserved s op p) op 6)
  simpa only [arguments,Nat.reduceAdd] using h
 theorem recordEntered_gas (s : Store NearState) (op : Nat) :
    GasUnits s (recordEntered s op) op 11 := by
  have one := gasUnits_charge s op 1
  simp only [Nat.one_mul] at one
  simpa only [recordEntered,Nat.reduceAdd] using one.trans (gasUnits_charge (chargedStore s op) op 10)
 theorem allocated_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (allocated cfg s p) ((AllocateRecord.bodyCost p.inner+22)*cfg.regularOpCost+fee cfg p) := by
  have a := (arguments_gas s cfg.regularOpCost p).trans (recordEntered_gas (arguments s cfg.regularOpCost p) cfg.regularOpCost)
  have b := (GasCost.of_units a).trans (AllocateRecord.after_gas cfg (recordEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost) p.inner)
  have cost : (11+11)*cfg.regularOpCost+(AllocateRecord.bodyCost p.inner*cfg.regularOpCost+AllocateRecord.fee cfg p.inner)=
      (AllocateRecord.bodyCost p.inner+22)*cfg.regularOpCost+fee cfg p := by simp only [fee,Nat.add_mul];omega
  simpa only [allocated,cost] using b
 theorem copied_gas (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) :
    GasUnits s (copied s op index out source memory) op 8 := by
  have first := store_units s op 4 index (out.toNat+0) memory (readI32 memory (source.toNat+8))
  have second := first.trans (store_units _ op 4 index (out.toNat+4) (firstMemory memory out source)
    (readI32 (firstMemory memory out source) (source.toNat+12)))
  simpa only [copied,copyWord,Nat.reduceAdd] using second
 theorem copyDone_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (copyDone cfg s p) ((AllocateRecord.bodyCost p.inner+30)*cfg.regularOpCost+fee cfg p) := by
  have all := (allocated_gas cfg s p).trans (GasCost.of_units
    (copied_gas (allocated cfg s p) cfg.regularOpCost p.inner.memoryIndex p.out p.inner.sp (allocatedMemory p)))
  have cost : (AllocateRecord.bodyCost p.inner+22)*cfg.regularOpCost+fee cfg p+8*cfg.regularOpCost=
      (AllocateRecord.bodyCost p.inner+30)*cfg.regularOpCost+fee cfg p := by simp only [Nat.add_mul];omega
  simpa only [copyDone,cost] using all
 theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after cfg s p) (bodyCost p*cfg.regularOpCost+fee cfg p) := by
  have all := (copyDone_gas cfg s p).trans (GasCost.of_units
    (global_units (copyDone cfg s p) cfg.regularOpCost 4 p.inner.globalIndex (.i32 p.sp)))
  have cost : (AllocateRecord.bodyCost p.inner+30)*cfg.regularOpCost+fee cfg p+4*cfg.regularOpCost=
      bodyCost p*cfg.regularOpCost+fee cfg p := by simp only [bodyCost,Nat.add_mul];omega
  simpa only [after,cost] using all
 theorem after_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest)) :
    (after cfg s p).host.gas.Credits rest := (after_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateRecordCopy
