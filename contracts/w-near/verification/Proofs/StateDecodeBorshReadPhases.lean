import Proofs.StateDecodeBorshReadNative
import Proofs.StateDecodeBorshWrapperCall

/-! Actual161 accepted operational phases. Every forward-copy source is read
from the memory produced by the preceding stage. The OR4 destination is literal. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def wrappedMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=StateDecodeBorshWrapper.finalMemory (actualWrapper p) (actualAllocation p q)
def packedValue(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI64 (wrappedMemory p q) ((scratch p).toNat+100)
def tagValue(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI32 (wrappedMemory p q) ((scratch p).toNat+96)
def scratchMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  ForwardCopyMemory.forward (wrappedMemory p q) (scratch p+60).toNat (scratch p+108).toNat 36
def upperMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  writeI32 (scratchMemory p q) ((scratch p).toNat+16) (UInt32.ofNat ((packedValue p q>>>32).toNat))
def acceptedMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  ForwardCopyMemory.forward (upperMemory p q) ((scratch p+16)|||4).toNat (scratch p+60).toNat 36
def resultMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  ForwardCopyMemory.forward (acceptedMemory p q) (p.out161+8).toNat (scratch p+16).toNat 40
def finalMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI32 (resultMemory p q) p.out161.toNat 0

def reserved(s:Store NearState)(op:Nat)(p:Layout):=setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def highSaved(s:Store NearState)(op:Nat)(p:Layout):=
  storeI32 (paid (reserved s op p) op 3) p.memoryIndex ((scratch p).toNat+12) p.memory p.length
def sliceSaved(s:Store NearState)(op:Nat)(p:Layout):=
  storeI32 (paid (highSaved s op p) op 3) p.memoryIndex ((scratch p).toNat+8) (highSetupMemory p) p.pointer
def wrapperArguments(s:Store NearState)(op:Nat)(p:Layout):=paid (sliceSaved s op p) op 6
def wrapped(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodeBorshWrapper.callAfter cfg (wrapperArguments s cfg.regularOpCost p) (actualWrapper p) (actualAllocation p q)
def packedCached(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (wrapped cfg s p q) cfg.regularOpCost 3
def tagCached(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (packedCached cfg s p q) cfg.regularOpCost 3
def firstCopyArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (tagCached cfg s p q) cfg.regularOpCost 7
def firstCopied(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  UnwrapStateCopyEntry.callAfter (firstCopyArguments cfg s p q) cfg.regularOpCost p.memoryIndex (scratch p+60) (scratch p+108) (wrappedMemory p q) 36
def firstDropped(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (firstCopied cfg s p q) cfg.regularOpCost 1
def guarded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (firstDropped cfg s p q) cfg.regularOpCost 4
def upperSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (guarded cfg s p q) cfg.regularOpCost 5) p.memoryIndex ((scratch p).toNat+16) (scratchMemory p q) (UInt32.ofNat ((packedValue p q>>>32).toNat))
def acceptedCopyArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (upperSaved cfg s p q) cfg.regularOpCost 9
def acceptedCopied(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  UnwrapStateCopyEntry.callAfter (acceptedCopyArguments cfg s p q) cfg.regularOpCost p.memoryIndex ((scratch p+16)|||4) (scratch p+60) (upperMemory p q) 36
def acceptedDropped(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (acceptedCopied cfg s p q) cfg.regularOpCost 1
def exhausted(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (acceptedDropped cfg s p q) cfg.regularOpCost 4
def resultCopyArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (exhausted cfg s p q) cfg.regularOpCost 7
def resultCopied(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  UnwrapStateCopyEntry.callAfter (resultCopyArguments cfg s p q) cfg.regularOpCost p.memoryIndex (p.out161+8) (scratch p+16) (acceptedMemory p q) 40
def resultDropped(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (resultCopied cfg s p q) cfg.regularOpCost 1
def tagged(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (resultDropped cfg s p q) cfg.regularOpCost 3) p.memoryIndex p.out161.toNat (resultMemory p q) 0
def branched(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=chargedStore (tagged cfg s p q) cfg.regularOpCost
def after(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  setGlobal (paid (branched cfg s p q) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp161)

def reservedFrame(frame:CallFrame)(p:Layout):={frame with locals:=frame.locals.set! 3 (.i32 (scratch p))}
def packedFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {reservedFrame frame p with locals:=(reservedFrame frame p).locals.set! 4 (.i64 (packedValue p q))}
def finalFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {packedFrame frame p q with locals:=(packedFrame frame p q).locals.set! 1 (.i32 (tagValue p q))}
def bodyCost(p:Layout):=18*(count p).toNat+4984
def bodySteps(p:Layout):=17*(count p).toNat+4493
end WNear.Proofs.StateDecodeBorshRead
