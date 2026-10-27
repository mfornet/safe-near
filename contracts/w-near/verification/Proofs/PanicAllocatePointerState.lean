import Proofs.PanicAllocateCall
import Proofs.PanicAllocateNative
import Proofs.StorePairAddresses

/-! Concrete original resources and sequential states for zero-size f503. -/
namespace WNear.Proofs.PanicAllocatePointerState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  sp : UInt32
  memory : Memory

def scratch (p : Layout) := p.sp - 16

def inner (p : Layout) : PanicAllocateState.Layout :=
  {mi := p.mi, globalIndex := p.globalIndex, memoryIndex := p.memoryIndex,
   global := {p.global with value := .i32 (scratch p)}, sp := scratch p,
   out := scratch p + 8, alignment := 1, memory := p.memory}

def reserved (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 5

def allocated (s : Store NearState) (op : Nat) (p : Layout) := PanicAllocateCall.callAfter (arguments s op p) op (inner p)
def checked (s : Store NearState) (op : Nat) (p : Layout) := paid (allocated s op p) op 4
def restored (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid (checked s op p) op 4) p.globalIndex (.i32 (scratch p + 16))
def after (s : Store NearState) (op : Nat) (p : Layout) := paid (restored s op p) op 1

def preparedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 2 (.i32 (scratch p))}
def finalFrame (frame : CallFrame) (p : Layout) := {preparedFrame frame p with locals := (preparedFrame frame p).locals.set! 3 (.i32 1)}
def finalMemory (p : Layout) := PanicAllocateState.finalMemory (inner p)

structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) : Prop where
  module : s.modules[frame.inst]? = some p.mi
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  function508Index : p.mi.funcAddrs[508]? = some 508
  function508 : s.funcs[508]? = some (.wasm WNear.Binary.PanicAllocate.signature508 frame.inst WNear.Binary.PanicAllocate.function508)
  function509Index : p.mi.funcAddrs[509]? = some 509
  function509 : s.funcs[509]? = some (.wasm WNear.Binary.PanicAllocateZero.signature frame.inst WNear.Binary.PanicAllocateZero.function)
  size : frame.locals[0]? = some (.i32 0)
  alignment : frame.locals[1]? = some (.i32 1)
  localSize : 4 ≤ frame.locals.size
  wf : p.memory.wf
  width : p.memory.byteSize ≤ 2 ^ 32
  spLower : 32 ≤ p.sp.toNat
  stackBound : p.sp.toNat ≤ p.memory.byteSize
  depth : callers.length + 2 < limits.maxCallDepth

end WNear.Proofs.PanicAllocatePointerState
