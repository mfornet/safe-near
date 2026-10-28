import Proofs.AllocateVectorOuterResult
import Proofs.StateDispatchLengthOuterResult
import Proofs.StateDispatchLengthOuterCall

/-! Original523 input and exact register-save/length/allocation setup. All
allocation templates describe the original memory, before any523 instruction. -/
namespace WNear.Proofs.StateReadRegisterOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout extends toVectorOuter : AllocateVectorOuter.Layout where
  sp523 : UInt32
  global523 : GlobalInst
  out523 : UInt32
  register : UInt64
  bytes : List UInt8
  lookupElement : UInt32
  dispatchVtable : UInt32
  address524 : Nat
  address687 : Nat
  address435 : Nat

def scratch (p : Layout) := p.sp523-48
def registerMemory (p : Layout) := writeI64 p.memory ((scratch p).toNat+24) p.register

def lengthOn (p : Layout) (memory : Memory) : StateDispatchLengthOuter.Layout :=
  let outerGlobal := {p.global523 with value:=.i32 (scratch p)}
  let innerSP := scratch p-16
  let input := innerSP+8
  {inner:={mi:=p.mi,globalIndex:=p.globalIndex,memoryIndex:=p.memoryIndex,
            tableAddress:=p.tableAddress,table:=p.table,global:={outerGlobal with value:=.i32 innerSP},
            sp:=innerSP,interface:=1055020,lookupElement:=p.lookupElement,
            memory:=writeI64 memory (innerSP.toNat+8) p.register,input:=input},
   memory,global:=outerGlobal,sp:=scratch p,out:=scratch p+8,register:=p.register}

def originalLength (p : Layout) := lengthOn p p.memory
def actualLength (p : Layout) := lengthOn p (registerMemory p)
def lengthMemory (p : Layout) := StateDispatchLengthOuterTail.finalMemory
  (StateDispatchLength.finalMemory (actualLength p).inner) (actualLength p).out (UInt64.ofNat p.bytes.length)

def vectorMemoryTemplate (p : Layout) : AllocateVectorOuter.Layout :=
  {p.toVectorOuter with memory:=lengthMemory p}
def vectorSaved (p : Layout) := AllocateRetry.savedMemory (vectorMemoryTemplate p).toRecord.toZeroed.toRetry
def vectorDelta (p : Layout) := AllocateGrowth.delta (AllocateRetry.growthLayout p.toRecord.toZeroed.toRetry)
def vectorGrown (p : Layout) : Memory :=
  {vectorSaved p with pages:=(vectorSaved p).pages++Array.replicate (vectorDelta p).toNat ByteArray.empty}
def actualVector (p : Layout) : AllocateVectorOuter.Layout :=
  {vectorMemoryTemplate p with grown:=vectorGrown p}

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def registerStore (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI64 (paid (reserved s op p) op 3) p.memoryIndex ((scratch p).toNat+24) p.memory p.register
def lengthArguments (s : Store NearState) (op : Nat) (p : Layout) := paid (registerStore s op p) op 4
def looked (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDispatchLengthOuter.callAfter cfg (lengthArguments s cfg.regularOpCost p) (actualLength p)
def reservedFrame (frame : CallFrame) (p : Layout) :=
  {frame with locals:=frame.locals.set! 2 (.i32 (scratch p))}
end WNear.Proofs.StateReadRegisterOuter
