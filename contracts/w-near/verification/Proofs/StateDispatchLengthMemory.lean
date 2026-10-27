import Proofs.StateDispatchLengthState
import Proofs.StateDispatchPrefixMemory

/-! Memory shape follows from the original bounds through both record copies. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32

theorem acquiredMemory_specs (p : Layout) (hw : p.memory.wf)
    (hc : 1074904 + 4 ≤ p.memory.byteSize) (ho : (scratch p).toNat + 8 ≤ p.memory.byteSize) :
    (acquiredMemory p).wf ∧ (acquiredMemory p).byteSize = p.memory.byteSize ∧ (acquiredMemory p).max = p.memory.max :=
  StateDispatchPrefix.acquiredMemory_specs p.toLayout hw hc ho

theorem highMemory_specs (p : Layout) (hw : (acquiredMemory p).wf)
    (hh : (scratch p).toNat + 16 ≤ (acquiredMemory p).byteSize) :
    (highMemory p).wf ∧ (highMemory p).byteSize = (acquiredMemory p).byteSize ∧ (highMemory p).max = (acquiredMemory p).max := by
  have h := writeI32_spec (acquiredMemory p) ((scratch p).toNat + 12)
    (readI32 (acquiredMemory p) ((scratch p).toNat + 4)) hw (by omega)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem lowMemory_specs (p : Layout) (hw : (highMemory p).wf)
    (hl : (scratch p).toNat + 12 ≤ (highMemory p).byteSize) :
    (lowMemory p).wf ∧ (lowMemory p).byteSize = (highMemory p).byteSize ∧ (lowMemory p).max = (highMemory p).max := by
  have h := writeI32_spec (highMemory p) ((scratch p).toNat + 8) (borrowed p) hw (by omega)
  exact ⟨h.1,h.2.1,h.2.2.1⟩

theorem Ready.lowMemory_specs (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (extra : Nat) (h : Ready s limits frame callers p extra) :
    (lowMemory p).wf ∧ (lowMemory p).byteSize = p.memory.byteSize ∧ (lowMemory p).max = p.memory.max := by
  have a := acquiredMemory_specs p h.prefixReady.memoryWf h.prefixReady.cellBound h.prefixReady.acquireOutBound
  have b := highMemory_specs p a.1 h.highBound
  have c := StateDispatchLength.lowMemory_specs p b.1 h.lowBound
  exact ⟨c.1,c.2.1.trans (b.2.1.trans a.2.1),c.2.2.trans (b.2.2.trans a.2.2)⟩

end WNear.Proofs.StateDispatchLength
