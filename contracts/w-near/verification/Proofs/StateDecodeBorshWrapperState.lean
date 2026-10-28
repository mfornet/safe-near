import Binary.StateDecodeBorshWrapper
import Proofs.StateDecodeBorshResult
import Proofs.UnwrapStateCopyEffects

/-! Original162 resources and exact sequential accepted phases. The two36-byte
copies include425's four trailing padding bytes; no snapshot is silently
substituted for a later sequential read. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
structure Layout extends toBorsh:StateDecodeBorsh.Layout where
  sp162:UInt32
  global162:GlobalInst
  out162:UInt32
  address425:Nat
  address951:Nat

def scratch(p:Layout):=p.sp162-96
def count(p:Layout):=StateDecodeBorsh.count p.toBorsh
structure Native(p:Layout):Prop where
  child:StateDecodeBorsh.Native p.toBorsh
  childSP:p.sp425=scratch p
  childOut:p.out425=scratch p+48
  childGlobal:p.global425={p.global162 with value:=.i32 (scratch p)}
  spLower:352≤p.sp162.toNat
  spBound:p.sp162.toNat≤p.memory.byteSize
  outputBound:p.out162.toNat+48≤p.memory.byteSize
structure Code(s:Store NearState)(inst:Nat)(p:Layout)(q:StateDecodeVectorCopy.Layout)(a581 a236:Nat):Prop where
  child:StateDecodeBorsh.Code s inst p.toBorsh q a581 a236
  index425:p.mi.funcAddrs[425]?=some p.address425
  function425:s.funcs[p.address425]?=some (.wasm WNear.Binary.StateDecodeBorsh.signature inst WNear.Binary.StateDecodeBorsh.function)
  index951:p.mi.funcAddrs[951]?=some p.address951
  function951:s.funcs[p.address951]?=some (.wasm WNear.Binary.UnwrapState.Copy.signature inst WNear.Binary.UnwrapState.Copy.function)

def decodedMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=StateDecodeBorsh.finalMemory p.toBorsh q
def packedValue(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI64 (decodedMemory p q) ((scratch p).toNat+52)
def tagValue(p:Layout)(q:StateDecodeVectorCopy.Layout):=readI32 (decodedMemory p q) ((scratch p).toNat+48)
def firstMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  ForwardCopyMemory.forward (decodedMemory p q) (scratch p+12).toNat ((scratch p+48)+12).toNat 36
def packedMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  writeI32 (firstMemory p q) (p.out162+8).toNat (UInt32.ofNat ((packedValue p q >>>32).toNat))
def secondMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  ForwardCopyMemory.forward (packedMemory p q) (p.out162+12).toNat (scratch p+12).toNat 36
def finalMemory(p:Layout)(q:StateDecodeVectorCopy.Layout):=writeI32 (secondMemory p q) p.out162.toNat 0

def reserved(s:Store NearState)(op:Nat)(p:Layout):=setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def arguments(s:Store NearState)(op:Nat)(p:Layout):=paid (reserved s op p) op 4
def decoded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodeBorsh.callAfter cfg (arguments s cfg.regularOpCost p) p.toBorsh q
def packedCached(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (decoded cfg s p q) cfg.regularOpCost 3
def tagCached(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (packedCached cfg s p q) cfg.regularOpCost 3
def copyArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (tagCached cfg s p q) cfg.regularOpCost 9
def copied(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  UnwrapStateCopyEntry.callAfter (copyArguments cfg s p q) cfg.regularOpCost p.memoryIndex (scratch p+12) ((scratch p+48)+12) (decodedMemory p q) 36
def guarded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (copied cfg s p q) cfg.regularOpCost 7
def packedSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (guarded cfg s p q) cfg.regularOpCost 7) p.memoryIndex (p.out162+8).toNat (firstMemory p q) (UInt32.ofNat ((packedValue p q >>>32).toNat))
def outputArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (packedSaved cfg s p q) cfg.regularOpCost 7
def outputCopied(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  UnwrapStateCopyEntry.callAfter (outputArguments cfg s p q) cfg.regularOpCost p.memoryIndex (p.out162+12) (scratch p+12) (packedMemory p q) 36
def accepted(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (outputCopied cfg s p q) cfg.regularOpCost 4
def tagged(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (accepted cfg s p q) cfg.regularOpCost 3) p.memoryIndex p.out162.toNat (secondMemory p q) 0
def after(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  setGlobal (paid (tagged cfg s p q) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp162)

def reservedFrame(frame:CallFrame)(p:Layout):={frame with locals:=frame.locals.set! 2 (.i32 (scratch p))}
def packedFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {reservedFrame frame p with locals:=(reservedFrame frame p).locals.set! 3 (.i64 (packedValue p q))}
def tagFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {packedFrame frame p q with locals:=(packedFrame frame p q).locals.set! 4 (.i32 (tagValue p q))}
def guardedFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {tagFrame frame p q with locals:=(tagFrame frame p q).locals.set! 1 (.i32 1)}
def finalFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {guardedFrame frame p q with locals:=(guardedFrame frame p q).locals.set! 1 (.i32 0)}
def bodyCost(p:Layout):=18*(count p).toNat+2835
def bodySteps(p:Layout):=17*(count p).toNat+2478
end WNear.Proofs.StateDecodeBorshWrapper
