import Proofs.StateReadRegisterCallHost
import Proofs.StateDispatchLengthOuterCall

/-! Register-length dispatcher host effects, including the actual usedGas synchronization. -/
namespace WNear.Proofs.StateDispatchLength
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
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt32) :
    functionalHostView seed (storeI32 s index address memory value).host=functionalHostView seed s.host := rfl
private theorem view_borrow (seed : NearState) (s : Store NearState) (op index : Nat) (memory : Memory) (scratch : UInt32) :
    functionalHostView seed (StateDispatchLengthBorrow.after s op index memory scratch).host=functionalHostView seed s.host := by
  simp only [StateDispatchLengthBorrow.after,StateDispatchLengthBorrow.low,StateDispatchLengthBorrow.high,
    ValueReturnOuter.nonnullAfter,ValueReturnOuter.nonnullEntry,view_paid,view_charge,view_store]
private theorem view_checked (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    functionalHostView seed (checked s op p).host=functionalHostView seed s.host := by
  have hb := view_borrow seed (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p)
  have ha := view_two seed s.host _ (StateDispatchPrefix.acquired_host s op p.toLayout)
  exact hb.trans ha
private theorem view_release (seed : NearState) (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    functionalHostView seed (ValueReturnBorrowCounters.releasedStore s op index counter memory).host=functionalHostView seed s.host := by
  simp only [ValueReturnBorrowCounters.releasedStore,ValueReturnBorrowCounters.calledSwapStore,
    ValueReturnBorrowCounters.swapStore,ValueReturnBorrowCounters.swapEntryStore,view_paid,view_charge,view_store]
private theorem view_cleanup (seed : NearState) (s : Store NearState) (op index : Nat) (counter : UInt32) (memory : Memory) :
    functionalHostView seed (StateDispatchLengthCleanup.after s op index counter memory).host=functionalHostView seed s.host := by
  simp only [StateDispatchLengthCleanup.after,StateDispatchLengthCleanup.released,StateDispatchLengthCleanup.releaseBefore,
    ValueReturnOuter.releaseAfter,ValueReturnOuter.nonnullEntry,view_paid,view_charge,view_release]
private theorem view_finish (seed : NearState) (s : Store NearState) (op index : Nat) (scratch : UInt32) :
    functionalHostView seed (StateDispatchLengthFinish.after s op index scratch).host=functionalHostView seed s.host := by
  simp only [StateDispatchLengthFinish.after,StateDispatchLengthFinish.returned,StateDispatchLengthFinish.afterReturn,
    StateDispatchReturn.callAfter,StateDispatchReturn.entered,StateDispatchReturn.after,StateDispatchReturn.reserved,
    StateDispatchReturn.suffixAfter,view_global,view_paid,view_charge]
private theorem view_returned (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView seed (returned cfg s p).host=functionalHostView seed s.host := by
  unfold returned
  have h := view_mask seed (arguments s cfg.regularOpCost p).host _
    (StateReadRegister.lengthCallAfter_functional_host cfg (arguments s cfg.regularOpCost p) p.mi)
  exact h.trans ((view_paid seed (checked s cfg.regularOpCost p) cfg.regularOpCost 7).trans (view_checked seed s cfg.regularOpCost p))

theorem finalStore_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView s.host (finalStore cfg s p).host=s.host := by
  simp only [finalStore,view_finish,cleaned,view_cleanup,view_returned]
  rfl

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView s.host (callAfter cfg s p).host=s.host := by
  unfold callAfter
  have h := view_mask s.host (entered s cfg.regularOpCost).host _ (finalStore_functional_host cfg (entered s cfg.regularOpCost) p)
  exact h.trans (view_charge s.host (chargedStore s cfg.regularOpCost) (12*cfg.regularOpCost))
end WNear.Proofs.StateDispatchLength

namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open StateReadRegister (functionalHostView view_paid view_charge view_mask)

private theorem view_global (seed : NearState) (s : Store NearState) (index : Nat) (value : Value) :
    functionalHostView seed (setGlobal s index value).host=functionalHostView seed s.host := rfl
private theorem view_store (seed : NearState) (s : Store NearState) (index address : Nat) (memory : Memory) (value : UInt64) :
    functionalHostView seed (storeI64 s index address memory value).host=functionalHostView seed s.host := rfl
private theorem view_arguments (seed : NearState) (s : Store NearState) (op : Nat) (p : Layout) :
    functionalHostView seed (arguments s op p).host=functionalHostView seed s.host := by
  simp only [arguments,inputStore,reserved,view_paid,view_global,view_store]
private theorem view_tail (seed : NearState) (s : Store NearState) (op index globalIndex : Nat) (memory : Memory) (out scratch : UInt32) (value : UInt64) :
    functionalHostView seed (StateDispatchLengthOuterTail.after s op index globalIndex memory out scratch value).host=functionalHostView seed s.host := by
  simp only [StateDispatchLengthOuterTail.after,StateDispatchLengthOuterTail.lowStore,StateDispatchLengthOuterTail.highStore,
    view_paid,view_global,view_store]

theorem finalStore_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView s.host (finalStore cfg s p).host=s.host := by
  have hl := view_mask s.host (arguments s cfg.regularOpCost p).host _
    (StateDispatchLength.callAfter_functional_host cfg (arguments s cfg.regularOpCost p) p.inner)
  have ht := view_tail s.host (looked cfg s p) cfg.regularOpCost p.inner.memoryIndex p.inner.globalIndex
    (StateDispatchLength.finalMemory p.inner) p.out (scratch p) (resultValue s p)
  exact ht.trans (hl.trans (view_arguments s.host s cfg.regularOpCost p))

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    functionalHostView s.host (callAfter cfg s p).host=s.host := by
  unfold callAfter
  have h := view_mask s.host (entered s cfg.regularOpCost).host _ (finalStore_functional_host cfg (entered s cfg.regularOpCost) p)
  exact h.trans (view_charge s.host (chargedStore s cfg.regularOpCost) (10*cfg.regularOpCost))

theorem callAfter_actionProfile (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).host.actionProfile=s.host.actionProfile := by
  have eq := congrArg NearState.actionProfile (callAfter_functional_host cfg s p)
  exact eq
end WNear.Proofs.StateDispatchLengthOuter
