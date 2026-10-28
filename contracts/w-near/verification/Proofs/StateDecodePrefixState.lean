import Binary.StateDecodePrefix
import Proofs.StateDecodePrefixLeavesRecordResult
import Proofs.StateDecodePrefixLeavesWordResult
import Proofs.StateDecodeSlicesResult

/-! Original316 inputs and its exact pre-allocation memory path. No allocator
outcome or decoded-state premise is contained in these definitions. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic

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
  takeAddress : Nat
  dropAddress : Nat
  wordAddress : Nat
  lengthAddress : Nat
  copyAddress : Nat

def scratch (p : Layout) := p.sp-64
def count (p : Layout) := readI32 p.memory p.pointer.toNat
def payloadPointer (p : Layout) := p.pointer+4
def remaining (p : Layout) := p.length-4
def takeFourOut (p : Layout) := scratch p+40
def dropFourOut (p : Layout) := scratch p+32
def lengthOut (p : Layout) := scratch p+24
def takePayloadOut (p : Layout) := scratch p+16
def allocatedOut (p : Layout) := scratch p+48
def dropPayloadOut (p : Layout) := scratch p+8

def takenFourMemory (p : Layout) := StateDecodeSlices.finalMemory false p.memory (takeFourOut p) p.pointer p.length 4
def droppedFourMemory (p : Layout) := StateDecodeSlices.finalMemory true (takenFourMemory p) (dropFourOut p) p.pointer p.length 4
def advancedPacked (p : Layout) := readI64 (droppedFourMemory p) (dropFourOut p).toNat
def advancedMemory (p : Layout) := writeI64 (droppedFourMemory p) p.slice.toNat (advancedPacked p)
def lengthMemory (p : Layout) := StateDecodePrefixLeaves.recordMemory (advancedMemory p) (lengthOut p) (count p)
def takenPayloadMemory (p : Layout) := StateDecodeSlices.finalMemory false (lengthMemory p) (takePayloadOut p) (payloadPointer p) (remaining p) (count p)
end WNear.Proofs.StateDecodePrefix
