import Proofs.AllocateRetryNative
import Proofs.AllocatePositiveState
import Proofs.AllocateGrowthCallFrame
import Proofs.AllocateFlaggedGas
import Proofs.AllocateFlaggedHost
import Proofs.AllocateEmptyResources

/-! Exact sequential581 states for its successful growth-and-retry path. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends AllocatePositive.Layout where
  grown : Memory
  address569 : Nat
  address573 : Nat
  growthAddress : Nat

def scratch (p : Layout) := AllocatePositive.scratch p.toLayout
def words (p : Layout) := AllocatePositive.words p.toLayout
def savedMemory (p : Layout) := AllocatePositive.savedMemory p.toLayout
def growthLayout (p : Layout) : AllocateGrowth.Layout :=
  {mi:=p.mi,memoryIndex:=p.memoryIndex,memory:=savedMemory p,grown:=p.grown,
   record:=scratch p,words:=words p,alignment:=1,address568:=p.alignAddress,
   address569:=p.address569,address572:=p.unitsAddress,address573:=p.address573,address574:=p.minimumAddress}
def secondLayout (p : Layout) := retryLayout (AllocatePositive.searchLayout p.toLayout) (growthLayout p)
def result (p : Layout) := AllocateSearch.pointer (secondLayout p)
def searchedMemory (p : Layout) := AllocateFlagged.finalMemory (secondLayout p)
def finalMemory (p : Layout) := writeI32 (searchedMemory p) p.allocator.toNat
  (readI32 (searchedMemory p) ((scratch p).toNat+12))
def reserved (s : Store NearState) (op : Nat) (p : Layout) := AllocatePositive.reserved s op p.toLayout
def prefixed (s : Store NearState) (op : Nat) (p : Layout) := AllocatePositive.prefixed s op p.toLayout
def firstAttempt (s : Store NearState) (op : Nat) (p : Layout) := AllocateEmpty.callAfter (paid (prefixed s op p) op 7) op
def firstMiss (s : Store NearState) (op : Nat) (p : Layout) := paid (firstAttempt s op p) op 2
def beforeGrow (s : Store NearState) (op : Nat) (p : Layout) := paid (firstMiss s op p) op 4
def grown (cfg : WasmConfig) (s : Store NearState) (p : Layout) := AllocateGrowth.callAfter cfg (beforeGrow s cfg.regularOpCost p) (growthLayout p)
def checked (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (grown cfg s p) cfg.regularOpCost 5
/-- The old saved head is read after growth, exactly as in the instruction stream. -/
def oldLinked (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  storeI32 (paid (checked cfg s p) cfg.regularOpCost 6) p.memoryIndex ((AllocateGrowth.header (growthLayout p)).toNat+8)
    (AllocateGrowth.finalMemory (growthLayout p))
    (readI32 (AllocateGrowth.finalMemory (growthLayout p)) ((scratch p).toNat+12))
def relinked (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  storeI32 (paid (oldLinked cfg s p) cfg.regularOpCost 3) p.memoryIndex ((scratch p).toNat+12)
    (writeI32 (AllocateGrowth.finalMemory (growthLayout p)) ((AllocateGrowth.header (growthLayout p)).toNat+8)
      (readI32 (AllocateGrowth.finalMemory (growthLayout p)) ((scratch p).toNat+12)))
    (AllocateGrowth.header (growthLayout p))
def retried (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  AllocateFlagged.callAfter (paid (relinked cfg s p) cfg.regularOpCost 7) cfg.regularOpCost (secondLayout p)
def found (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (retried cfg s p) cfg.regularOpCost 1
def updated (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  storeI32 (paid (found cfg s p) cfg.regularOpCost 4) p.memoryIndex p.allocator.toNat (searchedMemory p)
    (readI32 (searchedMemory p) ((scratch p).toNat+12))
def after (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  paid (setGlobal (paid (updated cfg s p) cfg.regularOpCost 4) p.globalIndex (.i32 p.sp)) cfg.regularOpCost 1

def prefixFrame (frame : CallFrame) (p : Layout) := AllocatePositive.prefixFrame frame p.toLayout
def missedFrame (frame : CallFrame) := {frame with locals:=frame.locals.set! 1 (.i32 0)}
def relinkedFrame (frame : CallFrame) (p : Layout) :=
  {missedFrame frame with locals:=(missedFrame frame).locals.set! 1 (.i32 (AllocateGrowth.header (growthLayout p)))}
def resultFrame (frame : CallFrame) (p : Layout) := {prefixFrame frame p with locals:=(prefixFrame frame p).locals.set! 1 (.i32 (result p))}

structure Native (p : Layout) : Prop where
  positive : p.size≠0
  rounding : p.size.toNat+4<2^32
  wf : p.memory.wf
  width : p.memory.byteSize≤2^32
  spLower : 16≤p.sp.toNat
  spBound : p.sp.toNat≤p.memory.byteSize
  allocatorBound : p.allocator.toNat+4≤p.memory.byteSize
  empty : readI32 p.memory p.allocator.toNat=0
  growth : AllocateGrowth.Native (growthLayout p)
  oldPositive : 0<p.memory.size
  pagesBound : p.memory.size+(AllocateGrowth.delta (growthLayout p)).toNat<65536
  wordsPositive : 0<(words p).toNat
  room : 80+(words p).toNat*4≤(AllocateGrowth.delta (growthLayout p)).toNat*65536
  vtableBound : 1057464+20≤p.memory.byteSize
  callbackSep : (scratch p).toNat+16≤1057464+16 ∨ 1057464+20≤(scratch p).toNat

structure Code (s : Store NearState) (inst : Nat) (p : Layout) : Prop where
  originalCode : AllocatePositive.Code s inst p.toLayout
  index569 : p.mi.funcAddrs[569]?=some p.address569
  function569 : s.funcs[p.address569]?=some (.wasm WNear.Binary.AllocateGrowth.signature569 inst WNear.Binary.AllocateGrowth.function569)
  index573 : p.mi.funcAddrs[573]?=some p.address573
  function573 : s.funcs[p.address573]?=some (.wasm WNear.Binary.AllocateGrowth.signature573 inst WNear.Binary.AllocateGrowth.function573)
  growthIndex : p.mi.funcAddrs[577]?=some p.growthAddress
  growthFunction : s.funcs[p.growthAddress]?=some (.wasm WNear.Binary.AllocateGrowth.signature inst WNear.Binary.AllocateGrowth.function)
end WNear.Proofs.AllocateRetry
