import Binary.StateDecodeVector
import Proofs.StateDecodeRawPhases

/-! Actual373 caches both allocation words before its caller-visible stores. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toRaw : StateDecodeRaw.Layout where
  spVector : UInt32
  globalVector : GlobalInst
  outVector : UInt32
  address767 : Nat

def scratch (p:Layout) := p.spVector-16
def memoryAllocated (p:Layout) := StateDecodeRaw.finalMemory p.toRaw
def packed (p:Layout) := readI64 (memoryAllocated p) ((scratch p).toNat+8)
def zeroMemory (p:Layout) := writeI32 (memoryAllocated p) (p.outVector.toNat+8) 0
def finalMemory (p:Layout) := writeI64 (zeroMemory p) p.outVector.toNat (packed p)

def reserved (s:Store NearState) (op:Nat) (p:Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def arguments (s:Store NearState) (op:Nat) (p:Layout) := paid (reserved s op p) op 5
def allocated (cfg:WasmConfig) (s:Store NearState) (p:Layout) := StateDecodeRaw.callAfterRaw cfg (arguments s cfg.regularOpCost p) p.toRaw
def cached (cfg:WasmConfig) (s:Store NearState) (p:Layout) := paid (allocated cfg s p) cfg.regularOpCost 3
def zeroed (cfg:WasmConfig) (s:Store NearState) (p:Layout) := storeI32 (paid (cached cfg s p) cfg.regularOpCost 3)
  p.memoryIndex (p.outVector.toNat+8) (memoryAllocated p) 0
def copied (cfg:WasmConfig) (s:Store NearState) (p:Layout) := storeI64 (paid (zeroed cfg s p) cfg.regularOpCost 3)
  p.memoryIndex p.outVector.toNat (zeroMemory p) (packed p)
def after (cfg:WasmConfig) (s:Store NearState) (p:Layout) := setGlobal (paid (copied cfg s p) cfg.regularOpCost 4)
  p.globalIndex (.i32 (scratch p+16))
def entered (s:Store NearState) (op:Nat) := chargedStore (chargedStore s op) (11*op)
def callAfter (cfg:WasmConfig) (s:Store NearState) (p:Layout) := after cfg (entered s cfg.regularOpCost) p

def reservedFrame (frame:CallFrame) (p:Layout) := {frame with locals:=frame.locals.set! 2 (.i32 (scratch p))}
def cachedFrame (frame:CallFrame) (p:Layout) := {reservedFrame frame p with locals:=(reservedFrame frame p).locals.set! 3 (.i64 (packed p))}

structure Native (p:Layout) : Prop where
  raw : StateDecodeRaw.Native p.toRaw
  childSP : p.spRaw=p.spVector-16
  childOut : p.outRaw=p.spRaw+8
  childGlobal : p.globalRaw={p.globalVector with value:=.i32 p.spRaw}
  spLower : 80≤p.spVector.toNat
  spBound : p.spVector.toNat≤p.memory.byteSize
  outBound : p.outVector.toNat+12≤p.memory.byteSize
end WNear.Proofs.StateDecodeVector
