import Binary.AllocateZeroed
import Proofs.AllocatePositiveResult
import Proofs.ZeroFillResources

/-! Original resources and exact sequential stores of the selected actual f153 path. -/
namespace WNear.Proofs.AllocateZeroed
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends AllocatePositive.Layout where
  allocateAddress : Nat
  fillAddress : Nat

abbrev Native (p : Layout) := AllocatePositive.Native p.toLayout
structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  positive : AllocatePositive.Code s inst p.toLayout
  allocateIndex : p.mi.funcAddrs[581]?=some p.allocateAddress
  allocateFunction : s.funcs[p.allocateAddress]?=some (.wasm WNear.Binary.Allocate.signature inst WNear.Binary.Allocate.function)
  fillIndex : p.mi.funcAddrs[952]?=some p.fillAddress
  fillFunction : s.funcs[p.fillAddress]?=some (.wasm WNear.Binary.ZeroFill.signature inst WNear.Binary.ZeroFill.function)

def result (p : Layout) := AllocatePositive.result p.toLayout
def allocatedMemory (p : Layout) := AllocatePositive.finalMemory p.toLayout
def finalMemory (p : Layout) := ZeroFill.filledMemory (allocatedMemory p) (result p) 0 p.size.toNat

def arguments (s : Store NearState) (op : Nat) := paid s op 3
def allocated (s : Store NearState) (op : Nat) (p : Layout) := AllocatePositive.callAfter (arguments s op) op p.toLayout
def checked (s : Store NearState) (op : Nat) (p : Layout) := paid (allocated s op p) op 3
def fillArguments (s : Store NearState) (op : Nat) (p : Layout) := paid (checked s op p) op 3
def filled (s : Store NearState) (op : Nat) (p : Layout) :=
  ZeroFill.callAfter (fillArguments s op p) op p.memoryIndex (allocatedMemory p) (result p) 0 p.size
def after (s : Store NearState) (op : Nat) (p : Layout) := paid (filled s op p) op 2

def resultFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 0 (.i32 (result p))}
def bodyCost (p : Layout) := 380+ZeroFill.bodyCost p.size
def bodySteps (p : Layout) := 314+ZeroFill.bodySteps p.size

 theorem Code.transport (s t : Store NearState) (inst : Nat) (p : Layout) (h : Code s inst p)
    (hf : t.funcs=s.funcs) (hm : t.modules=s.modules) (ht : t.tables=s.tables) : Code t inst p := by
  refine ⟨h.positive.transport s t inst p.toLayout hf hm ht,h.allocateIndex,?_,h.fillIndex,?_⟩
  · rw [hf];exact h.allocateFunction
  · rw [hf];exact h.fillFunction
 theorem Code.paid (s : Store NearState) (op n inst : Nat) (p : Layout) (h : Code s inst p) : Code (paid s op n) inst p := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.transport _ _ inst p rfl rfl rfl

end WNear.Proofs.AllocateZeroed
