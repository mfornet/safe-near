import Proofs.StateReadRegisterCallHost
import Proofs.StateDispatchReadCall

/-! Precise functional-host frame for the actual read-register dispatcher.
The register host synchronizes context.usedGas; this observer is masked in
addition to gas and gasProfile. In particular actionProfile is retained. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open StateReadRegister (functionalHostView view_paid view_charge view_mask)
set_option maxRecDepth 16384

private theorem view_two (seed before after : NearState)
    (h : {after with gas:=before.gas,gasProfile:=before.gasProfile}=before) :
    functionalHostView seed after=functionalHostView seed before := by
  have eq := congrArg (functionalHostView seed) h
  exact eq
private theorem view_global (seed : NearState) (s : Store NearState) (index : Nat) (value : Value) :
    functionalHostView seed (setGlobal s index value).host=functionalHostView seed s.host := rfl
private theorem view_finish (seed : NearState) (s : Store NearState) (op index : Nat) (scratch : UInt32) :
    functionalHostView seed (StateDispatchReadFinish.after s op index scratch).host=functionalHostView seed s.host := by
  simp only [StateDispatchReadFinish.after,StateDispatchReadFinish.checked,ValueReturnOuter.checkAfter,
    ValueReturnOuter.nonnullEntry,ValueReturnBorrow.checkedStore,view_global,view_paid,view_charge]
private theorem view_cleanup (seed : NearState) (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    functionalHostView seed (StateDispatchReadCleanup.after s op index counter memory).host=functionalHostView seed s.host := by
  exact view_two seed s.host _ (StateDispatchReadCleanup.after_host s op index counter memory)
private theorem view_returned (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    functionalHostView seed (StateDispatchReadTail.returned cfg s p bytes).host=functionalHostView seed s.host := by
  unfold StateDispatchReadTail.returned
  have h := view_mask seed (StateDispatchReadTail.arguments s cfg.regularOpCost).host _
    (StateReadRegister.readCallAfter_functional_host cfg (StateDispatchReadTail.arguments s cfg.regularOpCost) p.mi (ptr p) bytes)
  exact h.trans (view_paid seed s cfg.regularOpCost 9)
private theorem view_tail (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    functionalHostView seed (StateDispatchReadTail.after cfg s p bytes).host=functionalHostView seed s.host := by
  simp only [StateDispatchReadTail.after,view_finish,StateDispatchReadTail.cleaned,view_cleanup,view_returned]

theorem finalStore_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    functionalHostView s.host (finalStore cfg s p bytes).host=s.host := by
  unfold finalStore
  have h := view_two s.host s.host _ (checked_host s cfg.regularOpCost p)
  exact (view_tail s.host cfg (checked s cfg.regularOpCost p) p bytes).trans h

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    functionalHostView s.host (callAfter cfg s p bytes).host=s.host := by
  unfold callAfter
  have h := view_mask s.host (entered s cfg.regularOpCost).host _
    (finalStore_functional_host cfg (entered s cfg.regularOpCost) p bytes)
  exact h.trans (view_charge s.host (chargedStore s cfg.regularOpCost) (11*cfg.regularOpCost))

theorem callAfter_actionProfile (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :
    (callAfter cfg s p bytes).host.actionProfile=s.host.actionProfile := by
  have eq := congrArg NearState.actionProfile (callAfter_functional_host cfg s p bytes)
  exact eq
end WNear.Proofs.StateDispatchRead
