import Proofs.StateDecodePrefixMemoryNative
import Proofs.StateDecodePrefixEarlyMemory
import Proofs.StateDecodeVectorCopyFrame
import Proofs.StateDecodeVectorCopyMemory
import Proofs.StateDecodePrefixOutputResult

/-! Original inputs derive all selected316 memory snapshots and output bounds. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private theorem paid_mems (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem input_index (p : Layout) (q : StateDecodeVectorCopy.Layout) (hd : AcceptedDomain p q) :
    (allocationInput p q).memoryIndex=p.memoryIndex := by unfold allocationInput;exact hd.memoryIndex
private theorem input_memory (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    (allocationInput p q).memory=takenPayloadMemory p:=rfl
attribute [local irreducible] allocationInput allocatedMemory droppedMemory finalMemory copyArguments allocated dropped outputted after

theorem allocated_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (allocated cfg s p q).mems[p.memoryIndex]?=some (allocatedMemory p q) := by
  have before : (copyArguments cfg s p).mems[(allocationInput p q).memoryIndex]?=some (allocationInput p q).memory := by
    rw[input_index p q hd,input_memory,copyArguments,paid_mems]
    exact payloadPrefix_memory cfg s p hm hn
  have h:=StateDecodeVectorCopy.callAfter_memory cfg (copyArguments cfg s p) (allocationInput p q)
    (allocation_copy_native p q hn hd.toAllocationDomain) before
  rw[input_index p q hd] at h
  simpa only [allocated,allocatedMemory] using h

theorem dropped_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (dropped cfg s p q).mems[p.memoryIndex]?=some (droppedMemory p q) := by
  have before : (paid (allocated cfg s p q) cfg.regularOpCost 9).mems[p.memoryIndex]?=some (allocatedMemory p q) := by
    rw[paid_mems];exact allocated_memory cfg s p q hn hd hm
  unfold dropped dropPayloadAfter droppedMemory
  exact StateDecodeSlices.callAfter_memory true _ _ _ _ _ _ _ _ before

theorem outputted_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (outputted cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q) := by
  unfold outputted finalMemory
  exact Output.after_memory (dropped cfg s p q) cfg.regularOpCost (outputLayout p q) (dropped_memory cfg s p q hn hd hm)

theorem after_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (after cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q) := by
  simpa only [after,setGlobal,paid_mems] using outputted_memory cfg s p q hn hd hm
end WNear.Proofs.StateDecodePrefix
