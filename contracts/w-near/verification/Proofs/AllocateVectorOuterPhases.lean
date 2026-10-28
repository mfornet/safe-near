import Proofs.AllocateVectorOuterCode
import Proofs.AllocateVectorOuterTail
import Proofs.AllocateVectorPhases

/-! Exact687 accepted-path stores. The record is cached before either output write. -/
namespace WNear.Proofs.AllocateVectorOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 p.outerSP)
def guarded (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 4
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (guarded s op p) op 5
def vectorEntered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateVector.after cfg (vectorEntered (arguments s cfg.regularOpCost p) cfg.regularOpCost) p.toVector

def allocatedMemory (p : Layout) := AllocateVector.finalMemory p.toVector
def cacheWord (p : Layout) := readI64 (allocatedMemory p) (p.outerSP.toNat+8)
def finalMemory (p : Layout) := outputMemory (allocatedMemory p) p.out687 p.size (cacheWord p)
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  tailAfter (allocated cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (allocatedMemory p) p.out687 p.size p.outerSP

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 3 (.i32 p.outerSP)}
def finalFrame (frame : CallFrame) (p : Layout) := cachedFrame (reservedFrame frame p) (allocatedMemory p) p.outerSP

def bodyCost (p : Layout) := AllocateVector.bodyCost p.toVector+40
def bodySteps (p : Layout) := AllocateVector.bodySteps p.toVector+31
def fee (cfg : WasmConfig) (p : Layout) := AllocateVector.fee cfg p.toVector
end WNear.Proofs.AllocateVectorOuter
