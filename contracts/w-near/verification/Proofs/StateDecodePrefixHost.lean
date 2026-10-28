import Proofs.StateDecodePrefixCall
import Proofs.StateDecodeVectorCopyFrame
import Proofs.StateDecodePrefixLeavesWordResult
import Proofs.StateDecodePrefixLeavesRecordResult

/-! Functional host preservation for actual316. Only gas and its profile are
masked: usedGas, actionProfile, registers and all other host fields are framed. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (op : Nat) : view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) : view seed (setGlobal s i v).host=view seed s.host:=rfl
private theorem view_store32 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_store64 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : view seed (storeI64 s i a m v).host=view seed s.host:=rfl
private theorem view_mask (seed original actual : NearState)
    (h : {actual with gas:=original.gas,gasProfile:=original.gasProfile}=original) : view seed actual=view seed original := by
  have result:=congrArg (view seed) h
  exact result
private theorem view_slice (seed : NearState) (drop : Bool) (s : Store NearState) (op i : Nat) (m : Memory) (out ptr len split : UInt32) :
    view seed (StateDecodeSlices.callAfter drop s op i m out ptr len split).host=view seed s.host :=
  view_mask seed s.host _ (StateDecodeSlices.callAfter_host drop s op i m out ptr len split)
private theorem view_word (seed : NearState) (cfg : WasmConfig) (s : Store NearState) :
    view seed (StateDecodePrefixLeaves.wordCallAfter cfg s).host=view seed s.host :=
  view_mask seed s.host _ (StateDecodePrefixLeaves.wordCallAfter_host cfg s)
private theorem view_record (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out len : UInt32) :
    view seed (StateDecodePrefixLeaves.recordCallAfter cfg s i m out len).host=view seed s.host :=
  view_mask seed s.host _ (StateDecodePrefixLeaves.recordCallAfter_host cfg s i m out len)
private theorem view_vector (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (q : StateDecodeVectorCopy.Layout) :
    view seed (StateDecodeVectorCopy.callAfter cfg s q).host=view seed s.host :=
  view_mask seed s.host _ (StateDecodeVectorCopy.callAfter_functional_host cfg s q)
private theorem view_output (seed : NearState) (s : Store NearState) (op : Nat) (p : Output.Layout) :
    view seed (Output.after s op p).host=view seed s.host := by
  simp only[Output.after,Output.described,Output.tagged,Output.low,Output.high,Output.cached,
    outputHighStore,outputLowStore,outputTagStore,StateDecodeScalar.store64Local,
    view_charge,view_store32,view_store64,view_paid]
attribute [local irreducible] reservedPrefix guardedPrefix takenPrefix wordPrefix statusPrefix droppedPrefix advancedPrefix
  countedPrefix lengthPrefix lengthCheckedPrefix enoughPrefix payloadPrefix copyArguments allocated dropped outputted after
  takenPayloadMemory takenFourMemory droppedFourMemory advancedMemory lengthMemory allocatedMemory droppedMemory

private theorem view_reservedPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (reservedPrefix s cfg.regularOpCost p).host=view seed s.host := by
  rw[reservedPrefix,view_global,view_paid]

theorem reservedPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(reservedPrefix s cfg.regularOpCost p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (reservedPrefix s cfg.regularOpCost p).host=s.host
  rw[view_reservedPrefix];rfl

private theorem view_guardedPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (guardedPrefix s cfg.regularOpCost p).host=view seed s.host := by
  rw[guardedPrefix,view_paid,view_reservedPrefix]

theorem guardedPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(guardedPrefix s cfg.regularOpCost p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (guardedPrefix s cfg.regularOpCost p).host=s.host
  rw[view_guardedPrefix];rfl

private theorem view_takenPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (takenPrefix cfg s p).host=view seed s.host := by
  rw[takenPrefix,takeAfter,view_slice,view_paid,view_guardedPrefix]

theorem takenPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(takenPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (takenPrefix cfg s p).host=s.host
  rw[view_takenPrefix];rfl

private theorem view_wordPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (wordPrefix cfg s p).host=view seed s.host := by
  rw[wordPrefix,wordAfter,view_word,view_paid,view_takenPrefix]

theorem wordPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(wordPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (wordPrefix cfg s p).host=s.host
  rw[view_wordPrefix];rfl

private theorem view_statusPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (statusPrefix cfg s p).host=view seed s.host := by
  rw[statusPrefix,view_paid,view_wordPrefix]

theorem statusPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(statusPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (statusPrefix cfg s p).host=s.host
  rw[view_statusPrefix];rfl

private theorem view_droppedPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (droppedPrefix cfg s p).host=view seed s.host := by
  rw[droppedPrefix,dropFourAfter,view_slice,view_paid,view_statusPrefix]

theorem droppedPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(droppedPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (droppedPrefix cfg s p).host=s.host
  rw[view_droppedPrefix];rfl

private theorem view_advancedPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (advancedPrefix cfg s p).host=view seed s.host := by
  rw[advancedPrefix,advanceAfter,view_store64,view_paid,view_droppedPrefix]

theorem advancedPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(advancedPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (advancedPrefix cfg s p).host=s.host
  rw[view_advancedPrefix];rfl

private theorem view_countedPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (countedPrefix cfg s p).host=view seed s.host := by
  rw[countedPrefix,view_paid,view_advancedPrefix]

theorem countedPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(countedPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (countedPrefix cfg s p).host=s.host
  rw[view_countedPrefix];rfl

private theorem view_lengthPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (lengthPrefix cfg s p).host=view seed s.host := by
  rw[lengthPrefix,lengthAfter,view_record,view_paid,view_countedPrefix]

theorem lengthPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(lengthPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (lengthPrefix cfg s p).host=s.host
  rw[view_lengthPrefix];rfl

private theorem view_lengthCheckedPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (lengthCheckedPrefix cfg s p).host=view seed s.host := by
  rw[lengthCheckedPrefix,view_paid,view_lengthPrefix]

theorem lengthCheckedPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(lengthCheckedPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (lengthCheckedPrefix cfg s p).host=s.host
  rw[view_lengthCheckedPrefix];rfl

private theorem view_enoughPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (enoughPrefix cfg s p).host=view seed s.host := by
  rw[enoughPrefix,view_paid,view_lengthCheckedPrefix]

theorem enoughPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(enoughPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (enoughPrefix cfg s p).host=s.host
  rw[view_enoughPrefix];rfl

private theorem view_payloadPrefix (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (payloadPrefix cfg s p).host=view seed s.host := by
  rw[payloadPrefix,view_slice,view_paid,view_enoughPrefix]

theorem payloadPrefix_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(payloadPrefix cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (payloadPrefix cfg s p).host=s.host
  rw[view_payloadPrefix];rfl

private theorem view_copyArguments (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (copyArguments cfg s p).host=view seed s.host := by
  rw[copyArguments,view_paid,view_payloadPrefix]

theorem copyArguments_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(copyArguments cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (copyArguments cfg s p).host=s.host
  rw[view_copyArguments];rfl

private theorem view_early (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (copyArguments cfg s p).host=view seed s.host :=
  view_mask seed s.host _ (copyArguments_functional_host cfg s p)
private theorem view_allocated (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    view seed (allocated cfg s p q).host=view seed s.host := by
  rw[allocated,view_vector,view_early]
private theorem view_dropped (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    view seed (dropped cfg s p q).host=view seed s.host := by
  rw[dropped,dropPayloadAfter,view_slice,view_paid,view_allocated]
private theorem view_outputted (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    view seed (outputted cfg s p q).host=view seed s.host := by
  rw[outputted,view_output,view_dropped]
private theorem view_after (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    view seed (after cfg s p q).host=view seed s.host := by
  rw[after,view_global,view_paid,view_outputted]

theorem allocated_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    {(allocated cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (allocated cfg s p q).host=s.host
  rw[view_allocated];rfl

theorem dropped_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    {(dropped cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (dropped cfg s p q).host=s.host
  rw[view_dropped];rfl

theorem outputted_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    {(outputted cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (outputted cfg s p q).host=s.host
  rw[view_outputted];rfl

theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    {(after cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after cfg s p q).host=s.host
  rw[view_after];rfl
theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    {(callAfter cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter cfg s p q).host=s.host
  rw[callAfter,view_after,entered,view_charge,view_charge];rfl
end WNear.Proofs.StateDecodePrefix
