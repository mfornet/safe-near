import Proofs.StateReadRegisterOuterPhases
import Proofs.StateDispatchReadCallHost
import Proofs.StateDispatchLengthCallHost
import Proofs.AllocateVectorOuterResult

/-! Functional host framing for f523 retains the actual register-host gas observer
update; only gas, gasProfile and context.usedGas are reset in the comparison. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open StateReadRegister (functionalHostView view_paid view_charge view_mask)
set_option maxRecDepth 16384
attribute [local irreducible] lengthArguments looked guarded vectorArguments allocated readArguments readDone copyDone branched after

private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) :
    functionalHostView seed (setGlobal s i v).host=functionalHostView seed s.host := rfl
private theorem view_store32 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) :
    functionalHostView seed (storeI32 s i a m v).host=functionalHostView seed s.host := rfl
private theorem view_store64 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) :
    functionalHostView seed (storeI64 s i a m v).host=functionalHostView seed s.host := rfl
private theorem view_pair_mask (seed before actual : NearState)
    (h : {actual with gas:=before.gas,gasProfile:=before.gasProfile}=before) :
    functionalHostView seed actual=functionalHostView seed before := by
  have eq := congrArg (functionalHostView seed) h
  exact eq
private theorem view_arguments (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    functionalHostView seed (lengthArguments s op p).host=functionalHostView seed s.host := by
  simp only [lengthArguments,registerStore,reserved,view_paid,view_store64,view_global]
private theorem view_looked (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView seed (looked cfg s p).host=functionalHostView seed s.host := by
  unfold looked
  have h := view_mask seed (lengthArguments s cfg.regularOpCost p).host _
    (StateDispatchLengthOuter.callAfter_functional_host cfg (lengthArguments s cfg.regularOpCost p) (actualLength p))
  exact h.trans (view_arguments seed s cfg.regularOpCost p)
private theorem view_vectorArguments (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView seed (vectorArguments cfg s p).host=functionalHostView seed s.host := by
  rw [vectorArguments,view_paid,guarded,view_paid,view_looked]
private theorem view_allocated (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView seed (allocated cfg s p).host=functionalHostView seed s.host := by
  unfold allocated
  have h := view_pair_mask seed (vectorArguments cfg s p).host _
    (AllocateVectorOuter.callAfter_functional_host cfg (vectorArguments cfg s p) (actualVector p))
  exact h.trans (view_vectorArguments seed cfg s p)
private theorem view_readDone (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView seed (readDone cfg s p).host=functionalHostView seed s.host := by
  unfold readDone
  have h := view_mask seed (readArguments cfg s p).host _
    (StateDispatchRead.callAfter_functional_host cfg (readArguments cfg s p) (readLayout p) p.bytes)
  have args : functionalHostView seed (readArguments cfg s p).host=
      functionalHostView seed (allocated cfg s p).host := by rw [readArguments,view_paid]
  exact h.trans (args.trans (view_allocated seed cfg s p))
private theorem view_copied (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (out sp : UInt32) :
    functionalHostView seed (copied s op index memory out sp).host=functionalHostView seed s.host := by
  simp only [copied,copyLow,copyHigh,view_store32,view_store64,view_paid]

theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView s.host (after cfg s p).host=s.host := by
  rw [after,view_global,view_paid,branched,view_charge,copyDone,view_copied,view_readDone]
  rfl

theorem after_actionProfile (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).host.actionProfile=s.host.actionProfile := by
  have eq := congrArg NearState.actionProfile (after_functional_host cfg s p)
  exact eq
end WNear.Proofs.StateReadRegisterOuter
