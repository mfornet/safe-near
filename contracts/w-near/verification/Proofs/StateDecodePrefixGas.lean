import Proofs.StateDecodePrefixPhases
import Proofs.StateDecodePrefixEarlyGas
import Proofs.StateDecodePrefixOutputResult
import Proofs.StateDecodeVectorCopyGas
import Proofs.StateDecodeSlicesGas

/-! Exact accepted316 ledger, with all actual helper activations and copy iterations. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
set_option maxRecDepth 16384
private theorem global_units (s : Store NearState) (op n i : Nat) (v : Value) :
    GasUnits s (setGlobal (paid s op n) i v) op n := (gasUnits_paid s op n).host_eq rfl
private theorem drop_units (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (scratch slice n : UInt32) :
    GasUnits s (dropPayloadAfter cfg s i m scratch slice n) cfg.regularOpCost 35 := by
  have h:=(gasUnits_paid s cfg.regularOpCost 9).trans
    (StateDecodeSlices.callAfter_units true (paid s cfg.regularOpCost 9) cfg.regularOpCost i m (scratch+8)
      (readI32 m slice.toNat) (readI32 m (slice.toNat+4)) n)
  simpa only [dropPayloadAfter,WNear.Binary.StateDecodeSlices.bodyCost,ite_true,Nat.reduceAdd] using h
attribute [local irreducible] copyArguments allocated dropped outputted after allocationInput

theorem copyArguments_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (copyArguments cfg s p) cfg.regularOpCost 190 := by
  simpa only [copyArguments,Nat.reduceAdd] using (payloadPrefix_gas cfg s p).trans (gasUnits_paid (payloadPrefix cfg s p) cfg.regularOpCost 7)

theorem allocated_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    GasUnits s (allocated cfg s p q) cfg.regularOpCost (18*(count p).toNat+848) := by
  have native:=allocation_copy_native p q hn hd.toAllocationDomain
  have qs : (allocationInput p q).size=count p := by unfold allocationInput;exact hd.size
  have h:=(copyArguments_gas cfg s p).trans (StateDecodeVectorCopy.callAfter_gas cfg (copyArguments cfg s p) (allocationInput p q) native)
  simpa only [allocated,qs,show 190+(18*(count p).toNat+658)=18*(count p).toNat+848 by omega] using h

theorem dropped_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    GasUnits s (dropped cfg s p q) cfg.regularOpCost (18*(count p).toNat+883) := by
  have h:=(allocated_gas cfg s p q hn hd).trans
    (drop_units cfg (allocated cfg s p q) p.memoryIndex (allocatedMemory p q) (scratch p) p.slice (count p))
  simpa only [dropped,show (18*(count p).toNat+848)+35=18*(count p).toNat+883 by omega] using h

theorem outputted_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    GasUnits s (outputted cfg s p q) cfg.regularOpCost (18*(count p).toNat+903) := by
  have h:=(dropped_gas cfg s p q hn hd).trans (Output.after_gas (dropped cfg s p q) cfg.regularOpCost (outputLayout p q))
  simpa only [outputted,show (18*(count p).toNat+883)+20=18*(count p).toNat+903 by omega] using h

theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    GasUnits s (after cfg s p q) cfg.regularOpCost (bodyCost p) := by
  have h:=(outputted_gas cfg s p q hn hd).trans
    (global_units (outputted cfg s p q) cfg.regularOpCost 4 p.globalIndex (.i32 p.sp))
  simpa only [after,bodyCost,show (18*(count p).toNat+903)+4=18*(count p).toNat+907 by omega] using h
end WNear.Proofs.StateDecodePrefix
