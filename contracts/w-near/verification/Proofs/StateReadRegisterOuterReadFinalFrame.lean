import Proofs.StateReadRegisterOuterReadFinal
import Proofs.StateDispatchReadCleanupFrame

/-! Exact full435 memory: register payload first, counter release second, then
memory-free status/SP epilogue. No execution or future-resource premise is used. -/
namespace WNear.Proofs.StateReadRegisterOuterReadMemory
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32 StateDispatchRead.returned

def cleanupMemory (p : StateDispatchRead.Layout) (bytes : List UInt8) :=
  let memory := StateDispatchRead.readMemory p bytes
  let counter := StateDispatchRead.counter p bytes
  writeI32 memory counter.toNat (readI32 memory counter.toNat+4294967295)

private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl |succ n ih=>exact ih
private theorem mems_global (s : Store NearState) (index : Nat) (value : Value) : (setGlobal s index value).mems=s.mems := rfl
private theorem mems_charge (s : Store NearState) (cost : Nat) : (chargedStore s cost).mems=s.mems := rfl
private theorem finish_mems (s : Store NearState) (op index : Nat) (scratch : UInt32) :
    (StateDispatchReadFinish.after s op index scratch).mems=s.mems := by
  simp only [StateDispatchReadFinish.after,StateDispatchReadFinish.checked,ValueReturnOuter.checkAfter,
    ValueReturnOuter.nonnullEntry,ValueReturnBorrow.checkedStore,mems_global,mems_paid,mems_charge]

theorem finalStore_memory (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchRead.Layout) (bytes : List UInt8)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (StateDispatchRead.finalStore cfg s p bytes).mems[p.memoryIndex]?=some (cleanupMemory p bytes) := by
  have h := StateDispatchRead.returned_memory cfg s p bytes hi hm
  have cleanup := StateDispatchReadCleanup.after_memory (StateDispatchRead.returned cfg s p bytes) cfg.regularOpCost
    p.memoryIndex (StateDispatchRead.counter p bytes) (StateDispatchRead.readMemory p bytes) h
  unfold StateDispatchRead.finalStore StateDispatchReadTail.after StateDispatchReadTail.cleaned
  rw [finish_mems]
  simpa only [StateDispatchReadTail.returned,StateDispatchReadTail.arguments,StateDispatchRead.returned,
    StateDispatchRead.arguments,cleanupMemory] using cleanup

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : StateDispatchRead.Layout) (bytes : List UInt8)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (StateDispatchRead.callAfter cfg s p bytes).mems[p.memoryIndex]?=some (cleanupMemory p bytes) := by
  unfold StateDispatchRead.callAfter
  apply finalStore_memory cfg _ p bytes hi
  simpa only [StateDispatchRead.entered,mems_charge] using hm
end WNear.Proofs.StateReadRegisterOuterReadMemory

namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic

theorem read_call_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hi : p.mi.memAddrs[0]?=some p.memoryIndex) (hm : s.mems[p.memoryIndex]?=some (readInputMemory p)) :
    (StateDispatchRead.callAfter cfg s (readLayout p) p.bytes).mems[p.memoryIndex]?=some (readFinalMemory p) := by
  have index : (readLayout p).memoryIndex=p.memoryIndex := rfl
  simpa only [StateReadRegisterOuterReadMemory.cleanupMemory,readFinalMemory,readCounter,readOutputMemory,index] using
    StateReadRegisterOuterReadMemory.callAfter_memory cfg s (readLayout p) p.bytes hi hm
end WNear.Proofs.StateReadRegisterOuter
