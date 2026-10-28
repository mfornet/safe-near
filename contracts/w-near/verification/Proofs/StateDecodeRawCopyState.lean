import Proofs.StateDecodeRawRecordInvoke
import Proofs.StateDecodeRawLayout
import Proofs.PanicAllocateCopy

/-! Exact f769 sequential states. Its high source is read after the low output
store; no early original-memory snapshot or alias assumption is substituted. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def reserved769 (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch769 p))
def reserved769Frame (frame : CallFrame) (p : Layout) :=
  {frame with locals:=frame.locals.set! 3 (.i32 (scratch769 p))}
def arguments769 (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved769 s op p) op 6
def allocated769 (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  recordCallAfter cfg (arguments769 s cfg.regularOpCost p) (actualPositive p) (out770 p)
def lowCopied769 (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  PanicAllocateCopy.copyStore (allocated769 cfg s p) cfg.regularOpCost p.memoryIndex 8 0 (scratch769 p) (scratch p+16) (memory770 p)
def highCopied769 (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  PanicAllocateCopy.copyStore (lowCopied769 cfg s p) cfg.regularOpCost p.memoryIndex 12 4 (scratch769 p) (scratch p+16) (lowMemory769 p)
def after769 (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  setGlobal (paid (highCopied769 cfg s p) cfg.regularOpCost 4) p.globalIndex (.i32 (scratch p))
def entered769 (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def callAfter769 (cfg : WasmConfig) (s : Store NearState) (p : Layout) := after769 cfg (entered769 s cfg.regularOpCost) p
end WNear.Proofs.StateDecodeRaw
