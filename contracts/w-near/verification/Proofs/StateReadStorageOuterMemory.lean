import Proofs.StateDispatchStorageCall
import Proofs.StateDispatchLengthOuterFootprint

/-! Complete459 memory is its borrow records followed by counter release.
The actual canonical storage-read host changes registers and accounting, not guest memory. -/
namespace WNear.Proofs.StateDispatchStorage
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 returned finalStore callAfter

abbrev finalMemory (p : Layout) := StateDispatchLength.finalMemory p
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_global (s : Store NearState) (index : Nat) (value : Value) : (setGlobal s index value).mems=s.mems := rfl
private theorem mems_charge (s : Store NearState) (cost : Nat) : (chargedStore s cost).mems=s.mems := rfl
private theorem finish_mems (s : Store NearState) (op index : Nat) (sp : UInt32) :
    (StateDispatchStorageFinish.after s op index sp).mems=s.mems := by
  simp only [StateDispatchStorageFinish.after,StateDispatchStorageFinish.afterReturn,
    StateDispatchLengthFinish.afterReturn,StateDispatchStorageFinish.returned,StateDispatchReturn.callAfter,
    StateDispatchReturn.entered,StateDispatchReturn.after,StateDispatchReturn.suffixAfter,StateDispatchReturn.reserved,
    mems_paid,mems_global,mems_charge]

theorem finalStore_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (finalStore cfg s p ctx key value).mems[p.memoryIndex]?=some (finalMemory p) := by
  have h := returned_memory cfg s p ctx key value hi hm
  have cleanup := StateDispatchStorageCleanup.after_memory (returned cfg s p ctx key value) cfg.regularOpCost
    p.memoryIndex (counter p) (lowMemory p) h
  unfold finalStore StateDispatchStorageTail.after StateDispatchStorageTail.cleaned
  rw [finish_mems]
  simpa only [StateDispatchStorageTail.returned,StateDispatchStorageTail.arguments,returned,arguments,
    finalMemory,StateDispatchLength.finalMemory] using cleanup

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (ctx : NearInterface.Context) (key value : List UInt8)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter cfg s p ctx key value).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold callAfter
  apply finalStore_memory cfg _ p ctx key value hi
  simpa only [entered,mems_charge] using hm
end WNear.Proofs.StateDispatchStorage
