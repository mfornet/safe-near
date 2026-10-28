import Proofs.StateDecodePrefixEarlyWP
import Proofs.StateDecodePrefixAllocationBridge
import Proofs.StateDecodeVectorCopyCall
import Proofs.StateDecodePrefixDropPayloadCall
import Proofs.StateDecodePrefixOutputState

/-! Actual316's complete accepted states. Allocation uses its original native
heap domain transferred through the concrete preallocation memory, not a future
allocation outcome. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure AcceptedDomain (p : Layout) (q : StateDecodeVectorCopy.Layout) : Prop extends AllocationDomain p q where
  module : q.mi=p.mi
  memoryIndex : q.memoryIndex=p.memoryIndex
  globalIndex : q.globalIndex=p.globalIndex
  global : q.globalVector={p.global with value:=.i32 (scratch p)}

def allocatedMemory (p : Layout) (q : StateDecodeVectorCopy.Layout) :=StateDecodeVectorCopy.finalMemory (allocationInput p q)
def copyArguments (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=paid (payloadPrefix cfg s p) cfg.regularOpCost 7
def allocated (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :=
  StateDecodeVectorCopy.callAfter cfg (copyArguments cfg s p) (allocationInput p q)
def droppedMemory (p : Layout) (q : StateDecodeVectorCopy.Layout) :=StateDecodeSlices.finalMemory true (allocatedMemory p q)
  (dropPayloadOut p) (readI32 (allocatedMemory p q) p.slice.toNat) (readI32 (allocatedMemory p q) (p.slice.toNat+4)) (count p)
def dropped (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :=
  dropPayloadAfter cfg (allocated cfg s p q) p.memoryIndex (allocatedMemory p q) (scratch p) p.slice (count p)
def outputLayout (p : Layout) (q : StateDecodeVectorCopy.Layout) : Output.Layout :=
  {memory:=droppedMemory p q,index:=p.memoryIndex,out:=p.out,scratch:=scratch p,slice:=p.slice}
def outputted (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :=
  Output.after (dropped cfg s p q) cfg.regularOpCost (outputLayout p q)
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :=
  setGlobal (paid (outputted cfg s p q) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp)
def finalMemory (p : Layout) (q : StateDecodeVectorCopy.Layout) :=Output.finalMemory (outputLayout p q)
def finalFrame (frame : CallFrame) (p : Layout) (q : StateDecodeVectorCopy.Layout) :=Output.cachedFrame (enoughPrefixFrame frame p) (outputLayout p q)
def bodyCost (p : Layout) :=18*(count p).toNat+907
def bodySteps (p : Layout) :=17*(count p).toNat+725
end WNear.Proofs.StateDecodePrefix
