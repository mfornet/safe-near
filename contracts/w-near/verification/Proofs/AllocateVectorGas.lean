import Proofs.AllocateVectorPhases
import Proofs.AllocateRecordCopyResult
import Proofs.AllocateLayoutWrapperResult

/-! Complete686 phase accounting: one linear growth fee is inherited from690. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
open AllocateGrowth (GasCost)
set_option maxRecDepth 16384
attribute [local irreducible] reserved arguments laidOut guarded selected allocateArguments allocated cached joined nonzero recorded restored after

private theorem global_units (s : Store NearState) (op n index : Nat) (v : Value) :
    GasUnits s (setGlobal (paid s op n) index v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem store_units (s : Store NearState) (op n index address : Nat) (m : Memory) (v : UInt32) :
    GasUnits s (storeI32 (paid s op n) index address m v) op n := (gasUnits_paid s op n).host_eq rfl

theorem reserved_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (reserved s op p) op 5 := by
  unfold reserved
  exact global_units s op 5 p.globalIndex (.i32 (reservedSP p))
 theorem arguments_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (arguments s op p) op 9 := by
  have h := (reserved_gas s op p).trans (gasUnits_paid (reserved s op p) op 4)
  simpa only [arguments,Nat.reduceAdd] using h
 theorem laidOut_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (laidOut s op p) op 87 := by
  have callee : GasUnits (arguments s op p) (AllocateLayoutWrapper.called (arguments s op p) op (layout685 p)) op 78 := by
    intro rest hc
    exact AllocateLayoutWrapper.called_gas (arguments s op p) op rest (layout685 p) hc
  have h := (arguments_gas s op p).trans callee
  simpa only [laidOut,Nat.reduceAdd] using h
 theorem guarded_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (guarded s op p) op 98 := by
  have h := (laidOut_gas s op p).trans (gasUnits_paid (laidOut s op p) op 11)
  simpa only [guarded,Nat.reduceAdd] using h
 theorem selected_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (selected s op p) op 101 := by
  have h := (guarded_gas s op p).trans (gasUnits_paid (guarded s op p) op 3)
  simpa only [selected,Nat.reduceAdd] using h
 theorem allocateArguments_gas (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (allocateArguments s op p) op 106 := by
  have h := (selected_gas s op p).trans (gasUnits_paid (selected s op p) op 5)
  simpa only [allocateArguments,Nat.reduceAdd] using h

 theorem allocated_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (allocated cfg s p) ((AllocateRecordCopy.bodyCost (layout690 p)+117)*cfg.regularOpCost+fee cfg p) := by
  have callee : GasCost (allocateArguments s cfg.regularOpCost p)
      (AllocateRecordCopy.callAfter cfg (allocateArguments s cfg.regularOpCost p) (layout690 p))
      ((AllocateRecordCopy.bodyCost (layout690 p)+11)*cfg.regularOpCost+AllocateRecordCopy.fee cfg (layout690 p)) := by
    intro rest hc
    simpa only [Nat.add_assoc] using AllocateRecordCopy.callAfter_gas cfg (allocateArguments s cfg.regularOpCost p) (layout690 p) rest hc
  have all := (GasCost.of_units (allocateArguments_gas s cfg.regularOpCost p)).trans callee
  have ce : 106*cfg.regularOpCost+((AllocateRecordCopy.bodyCost (layout690 p)+11)*cfg.regularOpCost+AllocateRecordCopy.fee cfg (layout690 p))=
      (AllocateRecordCopy.bodyCost (layout690 p)+117)*cfg.regularOpCost+fee cfg p := by simp only [fee,Nat.add_mul];omega
  simpa only [allocated,ce] using all

private theorem cost_paid (cfg : WasmConfig) (s t : Store NearState) (p : Layout) (c n : Nat)
    (h : GasCost s t (c*cfg.regularOpCost+fee cfg p)) :
    GasCost s (paid t cfg.regularOpCost n) ((c+n)*cfg.regularOpCost+fee cfg p) := by
  have all := h.trans (GasCost.of_units (gasUnits_paid t cfg.regularOpCost n))
  simpa only [Nat.add_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
 theorem cached_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (cached cfg s p) ((AllocateRecordCopy.bodyCost (layout690 p)+123)*cfg.regularOpCost+fee cfg p) := by
  have h := cost_paid cfg s (allocated cfg s p) p _ 6 (allocated_gas cfg s p)
  simpa only [cached,Nat.add_assoc,Nat.reduceAdd] using h
 theorem joined_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (joined cfg s p) ((AllocateRecordCopy.bodyCost (layout690 p)+124)*cfg.regularOpCost+fee cfg p) := by
  have h := cost_paid cfg s (cached cfg s p) p _ 1 (cached_gas cfg s p)
  simpa only [joined,Nat.add_assoc,Nat.reduceAdd] using h
 theorem nonzero_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (nonzero cfg s p) ((AllocateRecordCopy.bodyCost (layout690 p)+127)*cfg.regularOpCost+fee cfg p) := by
  have h := cost_paid cfg s (joined cfg s p) p _ 3 (joined_gas cfg s p)
  simpa only [nonzero,Nat.add_assoc,Nat.reduceAdd] using h
 theorem recordStore_gas (s : Store NearState) (op index : Nat) (memory : Memory) (out pointer size : UInt32) :
    GasUnits s (recordStore s op index memory out pointer size) op 6 := by
  have first := store_units s op 3 index out.toNat memory pointer
  have both := first.trans (store_units _ op 3 index (out.toNat+4) (writeI32 memory out.toNat pointer) size)
  simpa only [recordStore,Nat.reduceAdd] using both
 theorem recorded_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (recorded cfg s p) ((AllocateRecordCopy.bodyCost (layout690 p)+133)*cfg.regularOpCost+fee cfg p) := by
  have all := (nonzero_gas cfg s p).trans (GasCost.of_units (recordStore_gas (nonzero cfg s p) cfg.regularOpCost p.memoryIndex (resultMemory p) p.out686 (result p) p.size))
  have ce : (AllocateRecordCopy.bodyCost (layout690 p)+127)*cfg.regularOpCost+fee cfg p+6*cfg.regularOpCost=
      (AllocateRecordCopy.bodyCost (layout690 p)+133)*cfg.regularOpCost+fee cfg p := by simp only [Nat.add_mul];omega
  simpa only [recorded,ce] using all
 theorem restored_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (restored cfg s p) ((AllocateRecordCopy.bodyCost (layout690 p)+137)*cfg.regularOpCost+fee cfg p) := by
  have all := (recorded_gas cfg s p).trans (GasCost.of_units (global_units (recorded cfg s p) cfg.regularOpCost 4 p.globalIndex (.i32 p.outerSP)))
  have ce : (AllocateRecordCopy.bodyCost (layout690 p)+133)*cfg.regularOpCost+fee cfg p+4*cfg.regularOpCost=
      (AllocateRecordCopy.bodyCost (layout690 p)+137)*cfg.regularOpCost+fee cfg p := by simp only [Nat.add_mul];omega
  simpa only [restored,ce] using all
 theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasCost s (after cfg s p) (bodyCost p*cfg.regularOpCost+fee cfg p) := by
  have charge := gasUnits_charge (restored cfg s p) cfg.regularOpCost 1
  simp only [Nat.one_mul] at charge
  have all := (restored_gas cfg s p).trans (GasCost.of_units charge)
  have ce : (AllocateRecordCopy.bodyCost (layout690 p)+137)*cfg.regularOpCost+fee cfg p+cfg.regularOpCost=
      bodyCost p*cfg.regularOpCost+fee cfg p := by simp only [bodyCost,Nat.add_mul];omega
  simp only [Nat.one_mul] at all
  rw [ce] at all
  simpa only [after] using all
 theorem after_credits (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits (bodyCost p*cfg.regularOpCost+fee cfg p+rest)) :
    (after cfg s p).host.gas.Credits rest := (after_gas cfg s p rest hc).2.2
end WNear.Proofs.AllocateVector
