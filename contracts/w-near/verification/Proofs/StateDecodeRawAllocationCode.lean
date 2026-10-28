import Proofs.StateDecodeRawNative

/-! The real allocator callback selector survives752's stack layout writes.
All other installed descriptors are independent of the replaced memory. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] laidOutMemory readI32 writeI32

theorem actual_positive_code (s : Store NearState) (inst : Nat) (p : Layout)
    (hn : Native p) (hc : AllocatePositive.Code s inst p.toPositive) :
    AllocatePositive.Code s inst (actualPositive p) := by
  refine { search := ?_
           globalIndex := hc.globalIndex
           alignIndex := hc.alignIndex
           alignFunction := hc.alignFunction
           roundIndex := hc.roundIndex
           roundFunction := hc.roundFunction
           searchIndex := hc.searchIndex
           searchFunction := hc.searchFunction }
  refine { module := hc.search.module
           memoryIndex := hc.search.memoryIndex
           tableIndex := hc.search.tableIndex
           table := hc.search.table
           callbackElement := ?_ 
           callbackType := hc.search.callbackType
           callbackFunction := hc.search.callbackFunction
           unitsIndex := hc.search.unitsIndex
           unitsFunction := hc.search.unitsFunction
           minimumIndex := hc.search.minimumIndex
           minimumFunction := hc.search.minimumFunction
           sizeIndex := hc.search.sizeIndex
           sizeFunction := hc.search.sizeFunction }
  change p.table.elems[(readI32 (actualSaved p) (1057464+16)).toNat]?=some (.func p.callbackAddress)
  rw [callback_word p hn]
  exact hc.search.callbackElement
end WNear.Proofs.StateDecodeRaw
