import Proofs.ValueReturnOuterState
import Proofs.ValueReturnOuterMemory
import Proofs.ValueReturnPacked

/-! Derived readiness facts for actual phase memories and unsigned lengths.
These are consequences of original memory resolution and dispatch reads. -/
namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic

namespace Ready
variable {cfg : WasmConfig} {extra : Nat} {s : Store NearState} {limits : ExecLimits}
  {frame : CallFrame} {callers : List CallFrame} {p : Layout}

theorem acquiredMemoryLookup (r : Ready cfg extra s limits frame callers p) :
    (acquired s cfg.regularOpCost p).mems[p.memoryIndex]? = some (acquiredMemory p) :=
  acquired_memory s cfg.regularOpCost p r.memory

theorem highMemoryLookup (r : Ready cfg extra s limits frame callers p) :
    (high s cfg.regularOpCost p).mems[p.memoryIndex]? = some (highMemory p) :=
  high_memory s cfg.regularOpCost p r.memory

theorem lowMemoryLookup (r : Ready cfg extra s limits frame callers p) :
    (low s cfg.regularOpCost p).mems[p.memoryIndex]? = some (lowMemory p) :=
  low_memory s cfg.regularOpCost p r.memory

theorem dispatchMemoryLookup (r : Ready cfg extra s limits frame callers p) :
    (dispatchBefore s cfg.regularOpCost p).mems[p.memoryIndex]? = some (lowMemory p) :=
  dispatch_memory s cfg.regularOpCost p r.memory

theorem fixedLength (r : Ready cfg extra s limits frame callers p) : p.len ≠ u64Max := by
  rw [← r.lengthRead]
  exact ValueReturnPacked.packed32_ne_sentinel (lowMemory p) (p.slice.toNat + 4)

end Ready
end WNear.Proofs.ValueReturnOuterBody
