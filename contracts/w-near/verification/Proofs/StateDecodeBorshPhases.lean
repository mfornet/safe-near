import Proofs.StateDecodeBorshState

/-! Actual425 accepted store/frame outline. These are concrete callee adapters
and scalar effects; no phase execution equation is a premise. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

def reserved(s:Store NearState)(op:Nat)(p:Layout):=setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def prefixArguments(s:Store NearState)(op:Nat)(p:Layout):=paid (reserved s op p) op 4
def prefixDecoded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodePrefixWrapper.callAfter cfg (prefixArguments s cfg.regularOpCost p) p.toPrefixWrapper q
def prefixCached(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (prefixDecoded cfg s p q) cfg.regularOpCost 3
def prefixGuarded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (prefixCached cfg s p q) cfg.regularOpCost 5
def prefixHighSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (prefixGuarded cfg s p q) cfg.regularOpCost 7) p.memoryIndex ((scratch p).toNat+24) (prefixMemory p q) (prefixLength p q)
def prefixSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (prefixHighSaved cfg s p q) cfg.regularOpCost 3) p.memoryIndex ((scratch p).toNat+16) (prefixHighMemory p q) (prefixPacked p q)
def wideArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (prefixSaved cfg s p q) cfg.regularOpCost 4
def wideDecoded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodeScalar.callAfter true cfg (wideArguments cfg s p q) (wideLayout p q)
def wideFirstSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (wideDecoded cfg s p q) cfg.regularOpCost 8) p.memoryIndex ((scratch p+32)+8).toNat (wideMemory p q) (readI64 (wideMemory p q) (scratch p+68).toNat)
def wideSecondSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (wideFirstSaved cfg s p q) cfg.regularOpCost 8) p.memoryIndex (scratch p+48).toNat (wideFirstMemory p q) (readI32 (wideFirstMemory p q) (scratch p+76).toNat)
def wideSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (wideSecondSaved cfg s p q) cfg.regularOpCost 4) p.memoryIndex ((scratch p).toNat+32) (wideSecondMemory p q) (readI64 (wideSecondMemory p q) ((scratch p).toNat+60))
def wideGuarded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (wideSaved cfg s p q) cfg.regularOpCost 5
def wideCached(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (wideGuarded cfg s p q) cfg.regularOpCost 10
def narrowArguments(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (wideCached cfg s p q) cfg.regularOpCost 4
def narrowDecoded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodeScalar.callAfter false cfg (narrowArguments cfg s p q) (narrowLayout p q)
def narrowHighSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (narrowDecoded cfg s p q) cfg.regularOpCost 12) p.memoryIndex ((scratch p+80)+8).toNat (narrowMemory p q) (readI32 (narrowMemory p q) ((scratch p+56)+12).toNat)
def narrowSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (narrowHighSaved cfg s p q) cfg.regularOpCost 4) p.memoryIndex ((scratch p).toNat+80) (narrowHighMemory p q) (readI64 (narrowHighMemory p q) ((scratch p).toNat+60))
def narrowGuarded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (narrowSaved cfg s p q) cfg.regularOpCost 5
def vectorHighSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (narrowGuarded cfg s p q) cfg.regularOpCost 11) p.memoryIndex (scratch p+8).toNat (savedNarrowMemory p q) (vectorLength p q)
def vectorSaved(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (vectorHighSaved cfg s p q) cfg.regularOpCost 5) p.memoryIndex (scratch p).toNat (vectorHighMemory p q) (vectorPacked p q)
def usageCached(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=paid (vectorSaved cfg s p q) cfg.regularOpCost 3

def output16(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (usageCached cfg s p q) cfg.regularOpCost 5) p.memoryIndex (p.out425+16).toNat (cachedMemory p q) (wideHigh p q)
def output8(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (output16 cfg s p q) cfg.regularOpCost 5) p.memoryIndex (p.out425+8).toNat (output16Memory p q) (wideLow p q)
def output24(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (output8 cfg s p q) cfg.regularOpCost 5) p.memoryIndex (p.out425+24).toNat (output8Memory p q) (usageValue p q)
def output32(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI64 (paid (output24 cfg s p q) cfg.regularOpCost 5) p.memoryIndex (p.out425+32).toNat (output24Memory p q) (vectorPacked p q)
def output40(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (output32 cfg s p q) cfg.regularOpCost 5) p.memoryIndex (p.out425+40).toNat (output32Memory p q) (vectorLength p q)
def tagged(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  storeI32 (paid (output40 cfg s p q) cfg.regularOpCost 3) p.memoryIndex p.out425.toNat (output40Memory p q) 0
def branched(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=chargedStore (tagged cfg s p q) cfg.regularOpCost
def after(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  setGlobal (paid (branched cfg s p q) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp425)

def reservedFrame(frame:CallFrame)(p:Layout):={frame with locals:=frame.locals.set! 2 (.i32 (scratch p))}
def prefixFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {reservedFrame frame p with locals:=(reservedFrame frame p).locals.set! 3 (.i64 (prefixPacked p q))}
def savedPrefixFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {prefixFrame frame p q with locals:=(prefixFrame frame p q).locals.set! 4 (.i32 (scratch p+68))}
def wideFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {savedPrefixFrame frame p q with locals:=((savedPrefixFrame frame p q).locals.set! 3 (.i64 (wideHigh p q))).set! 5 (.i64 (wideLow p q))}
def vectorFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {wideFrame frame p q with locals:=((wideFrame frame p q).locals.set! 1 (.i32 (vectorLength p q))).set! 6 (.i64 (vectorPacked p q))}
def finalFrame(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  {vectorFrame frame p q with locals:=(vectorFrame frame p q).locals.set! 7 (.i64 (usageValue p q))}
def bodyCost(p:Layout):=18*(count p).toNat+1434
def bodySteps(p:Layout):=17*(count p).toNat+1170
end WNear.Proofs.StateDecodeBorsh
