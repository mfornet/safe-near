import Proofs.ValueReturnOuterState
import Proofs.ValueReturnDispatchGas

namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] acquired high low reserved arguments looked lookupBefore

theorem paid_globals (s : Store NearState) (op count : Nat) : (paid s op count).globals = s.globals := by
  induction count with
  | zero => rfl
  | succ n ih => exact ih

theorem lookup_globals (s : Store NearState) (op : Nat) :
    (ValueReturnThreadLocal.indirectAfter s op).globals = s.globals := by
  simp only [ValueReturnThreadLocal.indirectAfter, ValueReturnThreadLocal.lookupAfter,
    ValueReturnThreadLocal.callAfter, ValueReturnThreadLocal.entered, ValueReturnThreadLocal.indirectEntered,
    paid_globals, chargedStore]

theorem arguments_globals (s : Store NearState) (op : Nat) (p : Layout) :
    (arguments s op p).globals = (reserved s op p).globals := by
  rw [arguments, paid_globals, paid_globals, looked, lookup_globals, lookupBefore, paid_globals]

theorem reserved_global (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (reserved s op p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  simp only [reserved, setGlobal, paid_globals]
  simp [Array.getElem?_modify, hg]

theorem acquired_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (acquired s op p).globals = (reserved s op p).globals := by
  have hargs : (arguments s op p).globals[p.globalIndex]? =
      some {p.global with value := .i32 (scratch p)} := by
    rw [arguments_globals]
    exact reserved_global s op p hg
  have rule := ValueReturnAcquire.calledAcquireStore_globals (arguments s op p) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p) 1074904 p.memory {p.global with value := .i32 (scratch p)} hargs rfl
  simpa only [acquired] using rule.trans (arguments_globals s op p)

theorem nonnullAfter_globals (s : Store NearState) (op : Nat) :
    (ValueReturnOuter.nonnullAfter s op).globals = s.globals := by
  unfold ValueReturnOuter.nonnullAfter
  rw [paid_globals]
  rfl

theorem dispatch_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (dispatchBefore s op p).globals = (reserved s op p).globals := by
  rw [dispatchBefore, nonnullAfter_globals, paid_globals, status, paid_globals,
    low, storeI32_globals, paid_globals, high, storeI32_globals, paid_globals]
  exact acquired_globals s op p hg

theorem returned_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]? = some p.global) :
    (returned cfg s p).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
  have hr := ValueReturnDispatchGas.fragmentAfter_resources cfg (dispatchBefore s cfg.regularOpCost p) p.mi p.len p.ptr
  have hglobals := congrArg (fun t : Store NearState => t.globals) hr
  change (ValueReturnDispatch.fragmentAfter cfg (dispatchBefore s cfg.regularOpCost p) p.mi p.len p.ptr).globals =
    (dispatchBefore s cfg.regularOpCost p).globals at hglobals
  rw [returned, hglobals, dispatch_globals s cfg.regularOpCost p hg]
  exact reserved_global s cfg.regularOpCost p hg

end WNear.Proofs.ValueReturnOuterBody
