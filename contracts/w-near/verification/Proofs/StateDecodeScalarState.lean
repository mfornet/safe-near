import Binary.StateDecodeScalar
import Proofs.StateDecodeWordsFrame
import Proofs.StateDecodeSlicesResult

/-! Original scalar-reader inputs and exact accepted sequential phases. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  memory : Memory
  sp : UInt32
  out : UInt32
  slice : UInt32
  pointer : UInt32
  length : UInt32
  addressTake : Nat
  addressWord : Nat
  addressDrop : Nat

def scratch (p : Layout) := p.sp-48
def width (wide : Bool) := WNear.Binary.StateDecodeScalar.width wide
def widthNat (wide : Bool) : Nat := if wide then 16 else 8
def takeOut (wide : Bool) (p : Layout) := scratch p+WNear.Binary.StateDecodeScalar.takeOffset wide
def wordOut (wide : Bool) (p : Layout) := scratch p+WNear.Binary.StateDecodeScalar.wordOffset wide
def dropOut (wide : Bool) (p : Layout) := scratch p+(if wide then 0 else 8)
def takenMemory (wide : Bool) (p : Layout) := StateDecodeSlices.finalMemory false p.memory (takeOut wide p) p.pointer p.length (width wide)
def wordMemory (wide : Bool) (p : Layout) := StateDecodeWords.finalMemory wide (takenMemory wide p) (wordOut wide p) p.pointer
def droppedMemory (wide : Bool) (p : Layout) := StateDecodeSlices.finalMemory true (wordMemory wide p) (dropOut wide p) p.pointer p.length (width wide)
def lowValue (wide : Bool) (p : Layout) := readI64 (wordMemory wide p) ((scratch p).toNat+(if wide then 17 else 25))
def highValue (p : Layout) := readI64 (wordMemory true p) (scratch p+25).toNat
def dropValue (wide : Bool) (p : Layout) := readI64 (droppedMemory wide p) ((scratch p).toNat+(if wide then 0 else 8))
def valuesMemory (wide : Bool) (p : Layout) :=
  if wide then writeI64 (writeI64 (droppedMemory wide p) (p.out+16).toNat (highValue p)) (p.out+8).toNat (lowValue wide p)
  else writeI64 (droppedMemory wide p) (p.out+8).toNat (lowValue wide p)
def updatedMemory (wide : Bool) (p : Layout) := writeI64 (valuesMemory wide p) p.slice.toNat (dropValue wide p)
def finalMemory (wide : Bool) (p : Layout) := writeI32 (updatedMemory wide p) p.out.toNat 0

def reserved (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def guarded (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 6
def takeArguments (s : Store NearState) (op : Nat) (p : Layout) := paid (guarded s op p) op 8
def taken (wide : Bool) (s : Store NearState) (op : Nat) (p : Layout) :=
  StateDecodeSlices.callAfter false (takeArguments s op p) op p.memoryIndex p.memory (takeOut wide p) p.pointer p.length (width wide)
def wordArguments (wide : Bool) (s : Store NearState) (op : Nat) (p : Layout) := paid (taken wide s op p) op 7
def readWords (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDecodeWords.callAfter wide cfg (wordArguments wide s cfg.regularOpCost p) p.memoryIndex (takenMemory wide p) (wordOut wide p) p.pointer
def accepted (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (readWords wide cfg s p) cfg.regularOpCost 5
def cached (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (accepted wide cfg s p) cfg.regularOpCost (if wide then 8 else 3)
def dropArguments (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (cached wide cfg s p) cfg.regularOpCost (if wide then 7 else 9)
def dropped (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDecodeSlices.callAfter true (dropArguments wide cfg s p) cfg.regularOpCost p.memoryIndex (wordMemory wide p) (dropOut wide p) p.pointer p.length (width wide)
def dropCached (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (dropped wide cfg s p) cfg.regularOpCost 3

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 2 (.i32 (scratch p))}
def guardedFrame (frame : CallFrame) (p : Layout) := {reservedFrame frame p with locals:=(reservedFrame frame p).locals.set! 3 (.i32 p.length)}
def cachedFrame (wide : Bool) (frame : CallFrame) (p : Layout) :=
  if wide then {frame with locals:=(frame.locals.set! 4 (.i64 (highValue p))).set! 5 (.i64 (lowValue wide p))}
  else {frame with locals:=frame.locals.set! 4 (.i64 (lowValue wide p))}
def dropCachedFrame (wide : Bool) (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! (if wide then 6 else 5) (.i64 (dropValue wide p))}
end WNear.Proofs.StateDecodeScalar
