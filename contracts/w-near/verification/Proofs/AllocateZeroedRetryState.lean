import Proofs.AllocateRetryState
import Proofs.AllocateZeroedTail

/-! Actual153 states for the positive empty-list/growth/retry581 path.
Every native premise describes original data or deterministic Memory.grow. -/
namespace WNear.Proofs.AllocateZeroedRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toRetry : AllocateRetry.Layout where
  allocateAddress : Nat
  fillAddress : Nat
abbrev Native (p : Layout) := AllocateRetry.Native p.toRetry
structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  retry : AllocateRetry.Code s inst p.toRetry
  allocateIndex : p.mi.funcAddrs[581]?=some p.allocateAddress
  allocateFunction : s.funcs[p.allocateAddress]?=some (.wasm WNear.Binary.Allocate.signature inst WNear.Binary.Allocate.function)
  fillIndex : p.mi.funcAddrs[952]?=some p.fillAddress
  fillFunction : s.funcs[p.fillAddress]?=some (.wasm WNear.Binary.ZeroFill.signature inst WNear.Binary.ZeroFill.function)

def result (p : Layout) := AllocateRetry.result p.toRetry
def allocatedMemory (p : Layout) := AllocateRetry.finalMemory p.toRetry
def finalMemory (p : Layout) := ZeroFill.filledMemory (allocatedMemory p) (result p) 0 p.size.toNat

def arguments (s : Store NearState) (op : Nat) := paid s op 3
def allocateEntered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateRetry.after cfg (allocateEntered (arguments s cfg.regularOpCost) cfg.regularOpCost) p.toRetry
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateZeroed.tailAfter (allocated cfg s p) cfg.regularOpCost p.memoryIndex (allocatedMemory p) (result p) p.size

def resultFrame (frame : CallFrame) (p : Layout) := AllocateZeroed.tailFrame frame (result p)
def bodyCost (p : Layout) := 625+ZeroFill.bodyCost p.size
def bodySteps (p : Layout) := 506+ZeroFill.bodySteps p.size
def fee (cfg : WasmConfig) (p : Layout) := memoryGrowCost cfg (AllocateGrowth.delta (AllocateRetry.growthLayout p.toRetry))

theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  have original := h.retry.originalCode.transport s t inst p.toRetry.toLayout hf hm ht
  refine ⟨⟨original,h.retry.index569,?_,h.retry.index573,?_,h.retry.growthIndex,?_⟩,
    h.allocateIndex,?_,h.fillIndex,?_⟩
  · rw [hf];exact h.retry.function569
  · rw [hf];exact h.retry.function573
  · rw [hf];exact h.retry.growthFunction
  · rw [hf];exact h.allocateFunction
  · rw [hf];exact h.fillFunction
 theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (h : Code s inst p) : Code (paid s op n) inst p := by
  induction n with | zero=>exact h | succ n ih=>exact ih.transport _ _ inst p rfl rfl rfl
end WNear.Proofs.AllocateZeroedRetry
