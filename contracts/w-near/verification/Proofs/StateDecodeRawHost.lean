import Proofs.StateDecodeRawPhases
import Proofs.StateDecodeRawRecordResources
import Proofs.AllocateLayoutWrapperHost

/-! Functional host frames for the complete selected raw-allocation path. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (op : Nat) : view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) : view seed (setGlobal s i v).host=view seed s.host:=rfl
private theorem view_store (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_mask (seed original actual : NearState)
    (h : {actual with gas:=original.gas,gasProfile:=original.gasProfile}=original) : view seed actual=view seed original := by
  have result:=congrArg (view seed) h
  exact result
private theorem view_layout (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocateLayoutWrapper.Layout) :
    view seed (AllocateLayoutWrapper.called s op p).host=view seed s.host := view_mask seed s.host _ (AllocateLayoutWrapper.called_functional_host s op p)
private theorem view_record (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : AllocatePositive.Layout) (out : UInt32) :
    view seed (recordCallAfter cfg s p out).host=view seed s.host := view_mask seed s.host _ (recordCallAfter_functional_host cfg s p out)
private theorem view_copy (seed : NearState) (s : Store NearState) (op i a b : Nat) (src dst : UInt32) (m : Memory) :
    view seed (PanicAllocateCopy.copyStore s op i a b src dst m).host=view seed s.host := by
  simp only [PanicAllocateCopy.copyStore,view_store,view_paid]
private theorem view_finished (seed : NearState) (s : Store NearState) (op i g : Nat) (m : Memory) (out ptr len scratch : UInt32) :
    view seed (finished s op i g m out ptr len scratch).host=view seed s.host := by
  simp only [finished,AllocateVector.finished,AllocateVector.recordStore,view_store,view_paid,view_charge,view_global]
attribute [local irreducible] after769 highCopied769 lowCopied769 allocated769 arguments769 reserved769
  afterRaw cachedRaw allocatedRaw argumentsRaw flagCheckedRaw checkedRaw alignedRaw laidOutRaw layoutArgumentsRaw reservedRaw
private theorem view_after769 (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (after769 cfg s p).host=view seed s.host := by
  simp only [after769,view_global,view_paid,highCopied769,lowCopied769,view_copy,
    allocated769,view_record,arguments769,reserved769,view_paid,view_global]

theorem after769_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after769 cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after769 cfg s p).host=s.host
  rw [view_after769];rfl

theorem callAfter769_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter769 cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter769 cfg s p).host=s.host
  rw [callAfter769,view_after769,entered769,view_charge,view_charge];rfl
private theorem view_afterRaw (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (afterRaw cfg s p).host=view seed s.host := by
  simp only [afterRaw,view_finished,cachedRaw,view_paid,allocatedRaw,callAfter769,view_after769,
    entered769,view_charge,argumentsRaw,flagCheckedRaw,checkedRaw,alignedRaw,view_paid,
    laidOutRaw,view_layout,layoutArgumentsRaw,reservedRaw,view_paid,view_global]

theorem afterRaw_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(afterRaw cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (afterRaw cfg s p).host=s.host
  rw [view_afterRaw];rfl

theorem callAfterRaw_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfterRaw cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfterRaw cfg s p).host=s.host
  rw [callAfterRaw,view_afterRaw,enteredRaw,view_charge,view_charge];rfl
end WNear.Proofs.StateDecodeRaw
