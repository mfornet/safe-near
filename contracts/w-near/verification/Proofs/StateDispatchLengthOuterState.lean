import Proofs.StateDispatchLengthCall
import Binary.StateDispatchLengthOuter

/-! Original resources and pure native conditions for f524's actual nested f440. -/
namespace WNear.Proofs.StateDispatchLengthOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384

structure Layout where
  inner : StateDispatchLength.Layout
  memory : Memory
  global : GlobalInst
  sp : UInt32
  out : UInt32
  register : UInt64

def scratch (p : Layout) := p.sp - 16
def inputMemory (p : Layout) := writeI64 p.memory ((scratch p).toNat + 8) p.register

def reserved (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.inner.globalIndex (.i32 (scratch p))
def inputStore (s : Store NearState) (op : Nat) (p : Layout) := storeI64 (paid (reserved s op p) op 3) p.inner.memoryIndex ((scratch p).toNat + 8) p.memory p.register
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (inputStore s op p) op 5

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 2 (.i32 (scratch p))}

/-- All conditions refer to original data and explicit sequential memory expressions. -/
structure Native (p : Layout) : Prop where
  memory_eq : p.inner.memory = inputMemory p
  global_eq : p.inner.global = {p.global with value := .i32 (scratch p)}
  sp_eq : p.inner.sp = scratch p
  interface_eq : p.inner.interface = 1055020
  input_eq : p.inner.input = scratch p + 8
  interfaceBound : p.inner.interface.toNat + 4 ≤ p.inner.memory.byteSize
  interfaceRead : readI32 p.inner.memory p.inner.interface.toNat = p.inner.lookupElement
  threadBound : 1074900 + 4 ≤ p.inner.memory.byteSize
  threadStatus : readI32 p.inner.memory 1074900 = 1
  cellBound : 1074904 + 4 ≤ p.inner.memory.byteSize
  acquireOutBound : (StateDispatchLength.scratch p.inner).toNat + 8 ≤ p.inner.memory.byteSize
  countAccepted : Numeric.irelop32 .ge_s (ValueReturnAcquire.nextCount p.inner.memory 1074904) 1 = true
  highBound : (StateDispatchLength.scratch p.inner).toNat + 16 ≤ (StateDispatchLength.acquiredMemory p.inner).byteSize
  lowBound : (StateDispatchLength.scratch p.inner).toNat + 12 ≤ (StateDispatchLength.highMemory p.inner).byteSize
  selectBound : (StateDispatchLength.borrowed p.inner).toNat + 4 ≤ (StateDispatchLength.lowMemory p.inner).byteSize
  selectedNonzero : StateDispatchLength.selected p.inner ≠ 0
  selectedBound : (StateDispatchLength.selected p.inner).toNat + 8 ≤ (StateDispatchLength.lowMemory p.inner).byteSize
  inputBound : p.inner.input.toNat + 8 ≤ (StateDispatchLength.lowMemory p.inner).byteSize
  vtableBound : (StateDispatchLength.vtable p.inner).toNat + 20 ≤ (StateDispatchLength.lowMemory p.inner).byteSize
  releaseBound : ((StateDispatchLength.scratch p.inner + 8) ||| 4).toNat + 4 ≤ (StateDispatchLength.lowMemory p.inner).byteSize
  counterBound : (StateDispatchLength.counter p.inner).toNat + 4 ≤ (StateDispatchLength.lowMemory p.inner).byteSize

structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame) (callers : List CallFrame) (p : Layout) (extra : Nat) : Prop where
  code : StateDispatchLength.Code s p.inner frame.inst extra
  native : Native p
  outLocal : frame.locals[0]? = some (.i32 p.out)
  registerLocal : frame.locals[1]? = some (.i64 p.register)
  localSize : 3 ≤ frame.locals.size
  memory : s.mems[p.inner.memoryIndex]? = some p.memory
  global : s.globals[p.inner.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryWf : p.memory.wf
  outBound : p.out.toNat + 16 ≤ p.memory.byteSize
  inputWriteBound : (scratch p).toNat + 16 ≤ p.memory.byteSize
  lengthIndex : p.inner.mi.funcAddrs[440]? = some 440
  lengthFunction : s.funcs[440]? = some (.wasm WNear.Binary.StateDispatchLength.signature frame.inst WNear.Binary.StateDispatchLength.function)
  depth : callers.length + 4 < limits.maxCallDepth
end WNear.Proofs.StateDispatchLengthOuter
