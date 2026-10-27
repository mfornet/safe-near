import Proofs.ValueReturnOuter
import Proofs.ValueReturnAcquire
import Proofs.ValueReturnThreadLocal
import Proofs.ValueReturnDispatchGas

/-! Deterministic phase states of the actual accepted outer return method. -/
namespace WNear.Proofs.ValueReturnOuterBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open WNear.Proofs.ValueReturnOuter
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

structure Layout where
  mi : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  tableAddress : Nat
  global : GlobalInst
  table : TableInst
  sp : UInt32
  interface : UInt32
  slice : UInt32
  lookupElement : UInt32
  receiver : UInt32
  vtable : UInt32
  returnElement : UInt32
  len : UInt64
  ptr : UInt64
  memory : Memory

def scratch (p : Layout) := p.sp - 16

def acquiredMemory (p : Layout) := ValueReturnAcquire.recordMemory
  (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904)) (scratch p) 1074904

def highMemory (p : Layout) := writeI32 (acquiredMemory p) ((scratch p).toNat + 12)
  (readI32 (acquiredMemory p) ((scratch p).toNat + 4))
def borrowed (p : Layout) := readI32 (highMemory p) (scratch p).toNat

def lowMemory (p : Layout) := writeI32 (highMemory p) ((scratch p).toNat + 8) (borrowed p)
def selected (p : Layout) := if readI32 (lowMemory p) (borrowed p).toNat ≠ 0 then borrowed p else 0

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))
def lookupBefore (s : Store NearState) (op : Nat) (p : Layout) := paid (reserved s op p) op 2
def looked (s : Store NearState) (op : Nat) (p : Layout) := ValueReturnThreadLocal.indirectAfter (lookupBefore s op p) op

def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (paid (looked s op p) op 3) op 3
def acquired (s : Store NearState) (op : Nat) (p : Layout) :=
  ValueReturnAcquire.calledAcquireStore (arguments s op p) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p) 1074904 p.memory

def high (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (acquired s op p) op 4) p.memoryIndex ((scratch p).toNat + 12) (acquiredMemory p)
    (readI32 (acquiredMemory p) ((scratch p).toNat + 4))
def low (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (high s op p) op 5) p.memoryIndex ((scratch p).toNat + 8) (highMemory p) (borrowed p)
def status (s : Store NearState) (op : Nat) (p : Layout) := paid (low s op p) op 2

def dispatchBefore (s : Store NearState) (op : Nat) (p : Layout) := nonnullAfter (paid (status s op p) op 6) op

def returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  ValueReturnDispatch.fragmentAfter cfg (dispatchBefore s cfg.regularOpCost p) p.mi p.len p.ptr

def counter (p : Layout) := readI32 (lowMemory p) (((scratch p + 8) ||| 4).toNat)
def finalStore (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  cleanupAfter (returned cfg s p) cfg.regularOpCost p.globalIndex p.memoryIndex (scratch p) (counter p) (lowMemory p)

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 2 (.i32 (scratch p))}
def guardedFrame (frame : CallFrame) (p : Layout) := {reservedFrame frame p with locals := (reservedFrame frame p).locals.set! 0 (.i32 1074904)}
def pointerFrame (frame : CallFrame) (p : Layout) := {guardedFrame frame p with locals := (guardedFrame frame p).locals.set! 3 (.i32 (borrowed p))}
def statusFrame (frame : CallFrame) (p : Layout) := {pointerFrame frame p with locals := (pointerFrame frame p).locals.set! 0 (.i32 0)}
def finalFrame (frame : CallFrame) (p : Layout) := ValueReturnDispatch.dispatchFrame (statusFrame frame p) (selected p)

/-- Primitive installed-code and table facts, with no execution premise. -/
structure Code (s : Store NearState) (p : Layout) (inst extra : Nat) : Prop where
  module : s.modules[inst]? = some p.mi
  tableIndex : p.mi.tableAddrs[0]? = some p.tableAddress
  table : s.tables[p.tableAddress]? = some p.table
  lookupElement : p.table.elems[p.lookupElement.toNat]? = some (.func 565)
  lookupType : p.mi.types[1]? = some WNear.Binary.ValueReturnThreadLocal.lookupSignature
  lookupFunction : s.funcs[565]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.lookupSignature inst WNear.Binary.ValueReturnThreadLocal.lookupFunction)
  helperIndex : p.mi.funcAddrs[468]? = some 468
  helperFunction : s.funcs[468]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature inst WNear.Binary.ValueReturnThreadLocal.function)
  acquireLinks : ValueReturnAcquire.Links s p.mi inst
  acquireIndex : p.mi.funcAddrs[429]? = some 429
  acquireFunction : s.funcs[429]? = some (.wasm WNear.Binary.ValueReturnAcquire.acquireSignature inst WNear.Binary.ValueReturnAcquire.acquireFunction)
  nonnullIndex : p.mi.funcAddrs[430]? = some 430
  nonnullFunction : s.funcs[430]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction)
  releaseIndex : p.mi.funcAddrs[431]? = some 431
  releaseFunction : s.funcs[431]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction)
  swapIndex : p.mi.funcAddrs[672]? = some 672
  swapFunction : s.funcs[672]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  checkIndex : p.mi.funcAddrs[433]? = some 433
  checkFunction : s.funcs[433]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.checkFunction)
  returnElement : p.table.elems[p.returnElement.toNat]? = some (.func 260)
  returnType : p.mi.types[4]? = some WNear.Binary.ValueReturnLeaf.signature
  returnFunction : s.funcs[260]? = some (.wasm WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function)
  hostIndex : p.mi.funcAddrs[20]? = some 20
  hostFunction : s.funcs[20]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn)
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex

theorem Code.transport (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : t.funcs = s.funcs) (hm : t.modules = s.modules)
    (ht : t.tables = s.tables) : Code t p inst extra := by
  exact {
    module := by rw [hm]; exact h.module
    tableIndex := h.tableIndex
    table := by rw [ht]; exact h.table
    lookupElement := h.lookupElement
    lookupType := h.lookupType
    lookupFunction := by rw [hf]; exact h.lookupFunction
    helperIndex := h.helperIndex
    helperFunction := by rw [hf]; exact h.helperFunction
    acquireLinks := ValueReturnAcquire.links_resources s t p.mi inst hm hf h.acquireLinks
    acquireIndex := h.acquireIndex
    acquireFunction := by rw [hf]; exact h.acquireFunction
    nonnullIndex := h.nonnullIndex
    nonnullFunction := by rw [hf]; exact h.nonnullFunction
    releaseIndex := h.releaseIndex
    releaseFunction := by rw [hf]; exact h.releaseFunction
    swapIndex := h.swapIndex
    swapFunction := by rw [hf]; exact h.swapFunction
    checkIndex := h.checkIndex
    checkFunction := by rw [hf]; exact h.checkFunction
    returnElement := h.returnElement
    returnType := h.returnType
    returnFunction := by rw [hf]; exact h.returnFunction
    hostIndex := h.hostIndex
    hostFunction := by rw [hf]; exact h.hostFunction
    memoryIndex := h.memoryIndex
    globalIndex := h.globalIndex
  }

/-- Actual-layout and primitive resource predicates for the accepted path.
All memories below are explicit sequential writes of the original memory. -/
structure Ready (cfg : WasmConfig) (extra : Nat) (s : Store NearState) (limits : ExecLimits)
    (frame : CallFrame) (callers : List CallFrame) (p : Layout) : Prop where
  code : Code s p frame.inst extra
  interfaceLocal : frame.locals[0]? = some (.i32 p.interface)
  sliceLocal : frame.locals[1]? = some (.i32 p.slice)
  localSize : 4 ≤ frame.locals.size
  memory : s.mems[p.memoryIndex]? = some p.memory
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryWf : p.memory.wf
  interfaceBound : p.interface.toNat + 4 ≤ p.memory.byteSize
  interfaceRead : readI32 p.memory p.interface.toNat = p.lookupElement
  threadBound : 1074900 + 4 ≤ p.memory.byteSize
  threadStatus : readI32 p.memory 1074900 = 1
  cellBound : 1074904 + 4 ≤ p.memory.byteSize
  acquireOutBound : (scratch p).toNat + 8 ≤ p.memory.byteSize
  countAccepted : Numeric.irelop32 .ge_s (ValueReturnAcquire.nextCount p.memory 1074904) 1 = true
  highBound : (scratch p).toNat + 16 ≤ (acquiredMemory p).byteSize
  lowBound : (scratch p).toNat + 12 ≤ (highMemory p).byteSize
  selectBound : (borrowed p).toNat + 4 ≤ (lowMemory p).byteSize
  selectedNonzero : selected p ≠ 0
  returnCellBound : (selected p).toNat + 8 ≤ (lowMemory p).byteSize
  sliceBound : p.slice.toNat + 8 ≤ (lowMemory p).byteSize
  vtableBound : p.vtable.toNat + 96 ≤ (lowMemory p).byteSize
  receiverRead : readI32 (lowMemory p) (selected p).toNat = p.receiver
  vtableRead : readI32 (lowMemory p) ((selected p).toNat + 4) = p.vtable
  elementRead : readI32 (lowMemory p) (p.vtable.toNat + 92) = p.returnElement
  lengthRead : ValueReturnDispatch.packed32 (lowMemory p) (p.slice.toNat + 4) = p.len
  pointerRead : ValueReturnDispatch.packed32 (lowMemory p) p.slice.toNat = p.ptr
  returnBound : p.ptr.toNat + p.len.toNat ≤ (lowMemory p).byteSize
  returnLimit : withinLimit (dispatchBefore s cfg.regularOpCost p).host.config.maxReturnLen p.len.toNat = true
  cleanupRecordBound : ((scratch p + 8) ||| 4).toNat + 4 ≤ (lowMemory p).byteSize
  counterBound : (counter p).toNat + 4 ≤ (lowMemory p).byteSize
  depth : callers.length + 3 < limits.maxCallDepth

attribute [local irreducible] writeI32 storeI32 acquired high low acquiredMemory highMemory lowMemory

theorem acquired_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]? = some p.memory) :
    (acquired s op p).mems[p.memoryIndex]? = some (acquiredMemory p) := by
  unfold acquired acquiredMemory
  apply ValueReturnAcquire.calledAcquireStore_memory
  simpa only [arguments, looked, lookupBefore, reserved, ValueReturnThreadLocal.indirectAfter,
    ValueReturnThreadLocal.indirectEntered, ValueReturnThreadLocal.lookupAfter, ValueReturnThreadLocal.callAfter,
    ValueReturnThreadLocal.entered, paid, chargedStore, setGlobal] using hm


end WNear.Proofs.ValueReturnOuterBody
