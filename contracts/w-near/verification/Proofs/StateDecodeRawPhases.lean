import Proofs.StateDecodeRaw767Prefix
import Proofs.StateDecodeRawCopyState
import Proofs.StateDecodeRawCache
import Proofs.StateDecodeRawFinish

/-! Actual767 flag-zero selected states. The sole caller output sequence runs
only after both words from the actual769 record have been cached. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def alignedRaw (s : Store NearState) (op : Nat) (p : Layout) := paid (laidOutRaw s op p) op 5
def checkedRaw (s : Store NearState) (op : Nat) (p : Layout) := paid (alignedRaw s op p) op 6
def flagCheckedRaw (s : Store NearState) (op : Nat) (p : Layout) := paid (checkedRaw s op p) op 3
def argumentsRaw (s : Store NearState) (op : Nat) (p : Layout) := paid (flagCheckedRaw s op p) op 5
def allocatedRaw (cfg : WasmConfig) (s : Store NearState) (p : Layout) := callAfter769 cfg (argumentsRaw s cfg.regularOpCost p) p
def cachedRaw (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (allocatedRaw cfg s p) cfg.regularOpCost 6
def afterRaw (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  finished (cachedRaw cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memory769 p)
    p.outRaw (cachedPointer p) (cachedLength p) (scratch p)
def alignedRawFrame (frame : CallFrame) (p : Layout) := AllocateVector.loadedFrame (reservedRawFrame frame p) 1 1
def checkedRawFrame (frame : CallFrame) (p : Layout) := AllocateVector.loadedFrame (alignedRawFrame frame p) 4 p.size
def cachedRawFrame (frame : CallFrame) (p : Layout) := cacheFrame (checkedRawFrame frame p) (memory769 p) (scratch p)
def enteredRaw (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11*op)
def callAfterRaw (cfg : WasmConfig) (s : Store NearState) (p : Layout) := afterRaw cfg (enteredRaw s cfg.regularOpCost) p
end WNear.Proofs.StateDecodeRaw
