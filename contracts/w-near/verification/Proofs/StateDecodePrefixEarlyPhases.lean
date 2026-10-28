import Proofs.StateDecodePrefixTakeCall
import Proofs.StateDecodePrefixWordCall
import Proofs.StateDecodePrefixDropCall
import Proofs.StateDecodePrefixAdvance
import Proofs.StateDecodePrefixLengthCall
import Proofs.StateDecodePrefixStatus
import Proofs.StateDecodePrefixCodeFrame

/-! Actual316 states before its374 allocation call. Every memory snapshot is the
sequential one produced by its preceding slice and word helper executions. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateVector (loadedFrame)

def reservedPrefix (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def guardedPrefix (s : Store NearState) (op : Nat) (p : Layout) := paid (reservedPrefix s op p) op 6
def takenPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  takeAfter cfg (guardedPrefix s cfg.regularOpCost p) p.memoryIndex p.memory (scratch p) p.pointer p.length
def wordPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) := wordAfter cfg (takenPrefix cfg s p)
def statusPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (wordPrefix cfg s p) cfg.regularOpCost 6
def droppedPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  dropFourAfter cfg (statusPrefix cfg s p) p.memoryIndex (takenFourMemory p) (scratch p) p.pointer p.length
def advancedPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  advanceAfter (droppedPrefix cfg s p) cfg.regularOpCost p.memoryIndex (droppedFourMemory p) (scratch p) p.slice
def countedPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (advancedPrefix cfg s p) cfg.regularOpCost 6
def lengthPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  lengthAfter cfg (countedPrefix cfg s p) p.memoryIndex (advancedMemory p) (scratch p) (count p)
def lengthCheckedPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (lengthPrefix cfg s p) cfg.regularOpCost 3
def enoughPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) := paid (lengthCheckedPrefix cfg s p) cfg.regularOpCost 8
def payloadPrefix (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDecodeSlices.callAfter false (paid (enoughPrefix cfg s p) cfg.regularOpCost 8) cfg.regularOpCost p.memoryIndex
    (lengthMemory p) (takePayloadOut p) (payloadPointer p) (remaining p) (count p)

def reservedPrefixFrame (frame : CallFrame) (p : Layout) := {frame with locals:=frame.locals.set! 2 (.i32 (scratch p))}
def guardedPrefixFrame (frame : CallFrame) (p : Layout) := loadedFrame (reservedPrefixFrame frame p) 3 p.length
def statusPrefixFrame (frame : CallFrame) (p : Layout) := statusFrame (guardedPrefixFrame frame p) (count p)
def countedPrefixFrame (frame : CallFrame) (p : Layout) := countFrame (statusPrefixFrame frame p) (count p)
def enoughPrefixFrame (frame : CallFrame) (p : Layout) := enoughFrame (countedPrefixFrame frame p) (lengthMemory p) p.slice (scratch p)

def prefixLabels (frame : CallFrame) (height : Nat) (code : Expr) :=
  emptyBlockFrame (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame frame height
    (WNear.Binary.StateDecodePrefix.restore++code)) height WNear.Binary.StateDecodePrefix.invalid)
      height WNear.Binary.StateDecodePrefix.short) height WNear.Binary.StateDecodePrefix.panic

def payloadRest : Expr := WNear.Binary.StateDecodePrefix.copyArguments++WNear.Binary.StateDecodePrefix.dropPayload++WNear.Binary.StateDecodePrefix.output
end WNear.Proofs.StateDecodePrefix
