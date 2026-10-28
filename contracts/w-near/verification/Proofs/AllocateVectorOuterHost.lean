import Proofs.AllocateVectorOuterPhases
import Proofs.AllocateLayoutWrapperHost
import Proofs.AllocateRecordCopyResult

/-! Functional host state is preserved through both actual vector wrappers;
only gas and gas profiling may change. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] reserved guarded arguments allocated after vectorEntered tailAfter exitAfter outputAfter
attribute [local irreducible] AllocateVector.reserved AllocateVector.arguments AllocateVector.laidOut AllocateVector.guarded AllocateVector.selected AllocateVector.allocateArguments AllocateVector.allocated AllocateVector.cached AllocateVector.joined AllocateVector.nonzero AllocateVector.recorded AllocateVector.restored AllocateVector.after

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (n : Nat) : view seed (chargedStore s n).host=view seed s.host := rfl
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) :
    view seed (setGlobal s i v).host=view seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) :
    view seed (storeI32 s i a m v).host=view seed s.host := rfl
private theorem view_mask (seed original actual : NearState)
    (h : {actual with gas:=original.gas,gasProfile:=original.gasProfile}=original) : view seed actual=view seed original := by
  have result := congrArg (view seed) h
  exact result
private theorem view_layout (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocateLayoutWrapper.Layout) :
    view seed (AllocateLayoutWrapper.called s op p).host=view seed s.host :=
  view_mask seed s.host _ (AllocateLayoutWrapper.called_functional_host s op p)
private theorem view_copy (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : AllocateRecordCopy.Layout) :
    view seed (AllocateRecordCopy.callAfter cfg s p).host=view seed s.host :=
  view_mask seed s.host _ (AllocateRecordCopy.callAfter_functional_host cfg s p)

private theorem view_vector_arguments (seed : NearState) (s : Store NearState) (op : Nat) (p : AllocateVector.Layout) :
    view seed (AllocateVector.arguments s op p).host=view seed s.host := by
  rw [AllocateVector.arguments,view_paid,AllocateVector.reserved,view_global,view_paid]
private theorem view_vector_after (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : AllocateVector.Layout) :
    view seed (AllocateVector.after cfg s p).host=view seed s.host := by
  rw [AllocateVector.after,view_charge,AllocateVector.restored,view_global,view_paid,
    AllocateVector.recorded,AllocateVector.recordStore,view_store,view_paid,view_store,view_paid,
    AllocateVector.nonzero,view_paid,AllocateVector.joined,view_paid,AllocateVector.cached,view_paid,
    AllocateVector.allocated,view_copy,AllocateVector.allocateArguments,view_paid,AllocateVector.selected,view_paid,
    AllocateVector.guarded,view_paid,AllocateVector.laidOut,view_layout,view_vector_arguments]

private theorem view_arguments (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    view seed (arguments s op p).host=view seed s.host := by
  rw [arguments,view_paid,guarded,view_paid,reserved,view_global,view_paid]
private theorem view_allocated (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (allocated cfg s p).host=view seed s.host := by
  rw [allocated,view_vector_after,vectorEntered,view_charge,view_charge,view_arguments]

theorem allocated_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(allocated cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (allocated cfg s p).host=s.host
  rw [view_allocated]
  rfl

private theorem view_output (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory)
    (out count : UInt32) (cached : UInt64) :
    view seed (outputAfter s op index memory out count cached).host=view seed s.host :=
  view_mask seed s.host _ (outputAfter_functional_host s op index memory out count cached)

theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after cfg s p).host=s.host
  rw [after,tailAfter,exitAfter,view_global,view_paid,view_output,view_paid,view_allocated]
  rfl
end WNear.Proofs.AllocateVectorOuter
