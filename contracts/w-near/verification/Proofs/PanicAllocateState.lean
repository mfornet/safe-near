import Proofs.PanicAllocateArguments
import Proofs.PanicAllocateZero
import Proofs.InterfaceStack

/-! Deterministic sequential states of f508's zero-size allocation wrapper. -/
namespace WNear.Proofs.PanicAllocateState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  sp : UInt32
  out : UInt32
  alignment : UInt32
  memory : Memory

def scratch (p : Layout) := p.sp - 16

def reserved (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 6

def allocatedMemory (p : Layout) := PanicAllocateZero.zeroMemory p.memory (scratch p + 8).toNat p.alignment

def allocated (s : Store NearState) (op : Nat) (p : Layout) :=
  PanicAllocateZero.calledStore (arguments s op p) op p.memoryIndex (scratch p + 8) p.alignment p.memory

def low (s : Store NearState) (op : Nat) (p : Layout) :=
  PanicAllocateCopy.copyStore (allocated s op p) op p.memoryIndex 8 0 (scratch p) p.out (allocatedMemory p)
def lowMemory (p : Layout) := writeI32 (allocatedMemory p) p.out.toNat (readI32 (allocatedMemory p) ((scratch p).toNat + 8))
def high (s : Store NearState) (op : Nat) (p : Layout) :=
  PanicAllocateCopy.copyStore (low s op p) op p.memoryIndex 12 4 (scratch p) p.out (lowMemory p)
def finalMemory (p : Layout) := writeI32 (lowMemory p) (p.out.toNat + 4) (readI32 (lowMemory p) ((scratch p).toNat + 12))
def after (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid (high s op p) op 4) p.globalIndex (.i32 (scratch p + 16))
def afterFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 3 (.i32 (scratch p))}

structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) : Prop where
  module : s.modules[frame.inst]? = some p.mi
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  functionIndex : p.mi.funcAddrs[509]? = some 509
  function : s.funcs[509]? = some (.wasm WNear.Binary.PanicAllocateZero.signature frame.inst WNear.Binary.PanicAllocateZero.function)
  out : frame.locals[0]? = some (.i32 p.out)
  size : frame.locals[1]? = some (.i32 0)
  alignment : frame.locals[2]? = some (.i32 p.alignment)
  localSize : 4 ≤ frame.locals.size
  wf : p.memory.wf
  width : p.memory.byteSize ≤ 2 ^ 32
  scratchBound : (scratch p).toNat + 16 ≤ p.memory.byteSize
  outBound : p.out.toNat + 8 ≤ p.memory.byteSize
  depth : callers.length + 1 < limits.maxCallDepth

end WNear.Proofs.PanicAllocateState
