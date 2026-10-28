import Proofs.AllocateVectorState
import Proofs.AllocateVectorSteps
import Proofs.AllocateRecordCopyCall

/-! Deterministic accepted686 phases. The output words are cached before either
output write, preserving arbitrary overlap with the caller's result record. -/
namespace WNear.Proofs.AllocateVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def result (p : Layout) := AllocateRecord.result (actualRecord p)
def resultMemory (p : Layout) := AllocateRecordCopy.resultMemory (layout690 p)
def guarded (s : Store NearState) (op : Nat) (p : Layout) := paid (laidOut s op p) op 11
def selected (s : Store NearState) (op : Nat) (p : Layout) := paid (guarded s op p) op 3
def allocateArguments (s : Store NearState) (op : Nat) (p : Layout) := paid (selected s op p) op 5
def allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateRecordCopy.callAfter cfg (allocateArguments s cfg.regularOpCost p) (layout690 p)
def cached (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (allocated cfg s p) cfg.regularOpCost 6
def joined (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (cached cfg s p) cfg.regularOpCost 1
def nonzero (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (joined cfg s p) cfg.regularOpCost 3
def recorded (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  recordStore (nonzero cfg s p) cfg.regularOpCost p.memoryIndex (resultMemory p) p.out686 (result p) p.size
def restored (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  setGlobal (paid (recorded cfg s p) cfg.regularOpCost 4) p.globalIndex (.i32 p.outerSP)
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) := chargedStore (restored cfg s p) cfg.regularOpCost

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 3 (.i32 (reservedSP p))}
def guardedFrame (frame : CallFrame) (p : Layout) :=
  {frame with locals:=(frame.locals.set! 1 (.i32 1)).set! 4 (.i32 p.size)}
def cachedFrame (frame : CallFrame) (p : Layout) :=
  {frame with locals:=(frame.locals.set! 5 (.i32 p.size)).set! 2 (.i32 (result p))}
def finalFrame (frame : CallFrame) (p : Layout) := cachedFrame (guardedFrame (reservedFrame frame p) p) p

def finalMemory (p : Layout) := recordMemory (resultMemory p) p.out686 (result p) p.size
def fee (cfg : WasmConfig) (p : Layout) := AllocateRecordCopy.fee cfg (layout690 p)
def bodyCost (p : Layout) := AllocateRecordCopy.bodyCost (layout690 p)+138
def bodySteps (p : Layout) := AllocateRecordCopy.bodySteps (layout690 p)+116
end WNear.Proofs.AllocateVector
