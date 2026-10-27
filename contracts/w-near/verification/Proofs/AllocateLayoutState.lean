import Proofs.AllocateLayoutRounded
import Proofs.InterfaceStack

/-! Exact accepted alignment-one leaf states, shared by f751 and f684. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  sp : UInt32
  out : UInt32
  input : UInt32
  memory : Memory

def scratch (p : Layout) := p.sp - 16
def size (p : Layout) := readI32 p.memory p.input.toNat
def reserved (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def guarded (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 7
def loaded (s : Store NearState) (op : Nat) (p : Layout) := paid (guarded s op p) op 3
def highMemory (p : Layout) := writeI32 p.memory (p.out.toNat + 4) 1
def high (s : Store NearState) (op : Nat) (p : Layout) := storeI32 (paid (loaded s op p) op 3) p.memoryIndex (p.out.toNat + 4) p.memory 1
def low (s : Store NearState) (op : Nat) (p : Layout) := roundedStore (high s op p) op p.memoryIndex p.out (size p) (highMemory p)
def finalMemory (p : Layout) := writeI32 (highMemory p) p.out.toNat (size p)
def after (s : Store NearState) (op : Nat) (p : Layout) := setGlobal (paid (low s op p) op 4) p.globalIndex (.i32 (scratch p + 16))
def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 2 (.i32 (scratch p))}
def guardedFrame (frame : CallFrame) (p : Layout) := {(reservedFrame frame p) with locals := (reservedFrame frame p).locals.set! 3 (.i32 1)}
def finalFrame (frame : CallFrame) (p : Layout) := {(guardedFrame frame p) with locals := (guardedFrame frame p).locals.set! 1 (.i32 (size p))}

structure Ready (s : Store NearState) (frame : CallFrame) (p : Layout) : Prop where
  module : s.modules[frame.inst]? = some p.mi
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  memory : s.mems[p.memoryIndex]? = some p.memory
  out : frame.locals[0]? = some (.i32 p.out)
  input : frame.locals[1]? = some (.i32 p.input)
  locals : 4 ≤ frame.locals.size
  wf : p.memory.wf
  inputBound : p.input.toNat + 8 ≤ p.memory.byteSize
  outBound : p.out.toNat + 8 ≤ p.memory.byteSize
  alignment : readI32 p.memory (p.input.toNat + 4) = 1

end WNear.Proofs.AllocateLayout
