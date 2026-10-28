import Binary.AllocateRecord
import Proofs.AllocateForwardRetryOuterCall
import Proofs.AllocateForwardRetryResources
import Proofs.InterfaceInstall

/-! Original resources and exact sequential states of689's positive zeroed path. -/
namespace WNear.Proofs.AllocateRecord
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toZeroed : AllocateZeroedRetry.Layout where
  out : UInt32
  address153 : Nat
  address239 : Nat
  address313 : Nat
structure Native (p : Layout) : Prop where
  allocation : AllocateZeroedRetry.Native p.toZeroed
  outputBound : p.out.toNat+8≤p.memory.byteSize
structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  allocation : AllocateZeroedRetry.Code s inst p.toZeroed
  index153 : p.mi.funcAddrs[153]?=some p.address153
  function153 : s.funcs[p.address153]?=some (.wasm WNear.Binary.AllocateZeroed.signature inst WNear.Binary.AllocateZeroed.function)
  index239 : p.mi.funcAddrs[239]?=some p.address239
  function239 : s.funcs[p.address239]?=some (.wasm WNear.Binary.AllocateForward.signature inst WNear.Binary.AllocateForward.function239)
  index313 : p.mi.funcAddrs[313]?=some p.address313
  function313 : s.funcs[p.address313]?=some (.wasm WNear.Binary.AllocateForward.signature inst WNear.Binary.AllocateForward.function313)

def result (p : Layout) := AllocateZeroedRetry.result p.toZeroed
def allocatedMemory (p : Layout) := AllocateZeroedRetry.finalMemory p.toZeroed
def recordMemory (memory : Memory) (out : Nat) (pointer size : UInt32) :=
  writeI32 (writeI32 memory (out+4) size) out pointer
def finalMemory (p : Layout) := recordMemory (allocatedMemory p) p.out.toNat (result p) p.size

def recordStore (s : Store NearState) (op index : Nat) (memory : Memory) (out : UInt32) (pointer size : UInt32) :=
  let high := storeI32 (paid s op 3) index (out.toNat+4) memory size
  storeI32 (paid high op 3) index out.toNat (writeI32 memory (out.toNat+4) size) pointer
def allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateForwardRetry.callAfter313 cfg (paid s cfg.regularOpCost 8) p.toZeroed
def selected (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (allocated cfg s p) cfg.regularOpCost 2
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  recordStore (selected cfg s p) cfg.regularOpCost p.memoryIndex (allocatedMemory p) p.out (result p) p.size

def resultFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 2 (.i32 (result p))}
def bodyCost (p : Layout) := AllocateZeroedRetry.bodyCost p.toZeroed+56
def bodySteps (p : Layout) := AllocateZeroedRetry.bodySteps p.toZeroed+31
def fee (cfg : WasmConfig) (p : Layout) := AllocateZeroedRetry.fee cfg p.toZeroed

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  refine ⟨h.allocation.transport s t inst p.toZeroed hf hm ht,h.index153,?_,h.index239,?_,h.index313,?_⟩
  · rw [hf];exact h.function153
  · rw [hf];exact h.function239
  · rw [hf];exact h.function313
 theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (h : Code s inst p) : Code (paid s op n) inst p := by
  induction n with | zero=>exact h | succ n ih=>exact ih.transport _ _ inst p rfl rfl rfl
end WNear.Proofs.AllocateRecord
