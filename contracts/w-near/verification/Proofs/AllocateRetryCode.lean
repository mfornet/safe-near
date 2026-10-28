import Proofs.AllocateRetryFrame
import Proofs.AllocateRetryDomain

/-! Original installed functions and the preserved callback word supply both retry callees. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32

theorem Code.growth (s : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p) :
    AllocateGrowth.Code s inst (growthLayout p) := by
  refine ⟨h.originalCode.search.module,h.originalCode.search.memoryIndex,
    h.originalCode.alignIndex,h.originalCode.alignFunction,h.index569,h.function569,
    h.originalCode.search.unitsIndex,h.originalCode.search.unitsFunction,h.index573,h.function573,
    h.originalCode.search.minimumIndex,h.originalCode.search.minimumFunction⟩

/-- The indirect callback still resolves from the original table because every
actual intervening memory write preserves its original vtable word. -/
theorem Code.second (s : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p) (hn : Native p) :
    AllocateSearch.SearchCode s (secondLayout p) inst := by
  have original := h.originalCode.search
  refine ⟨⟨original.module,original.memoryIndex,original.tableIndex,original.table,?_,
    original.callbackType,original.callbackFunction,original.unitsIndex,original.unitsFunction,
    original.minimumIndex,original.minimumFunction⟩,original.sizeIndex,original.sizeFunction⟩
  change p.table.elems[(readI32 (secondLayout p).memory (1057464+16)).toNat]?=some (.func p.callbackAddress)
  rw [callback_word p hn]
  exact original.callbackElement
end WNear.Proofs.AllocateRetry
