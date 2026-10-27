import Proofs.StateDispatchPrefixState
import Proofs.StateDispatchLengthState
import Proofs.StateDispatchHosts
import Proofs.StateDispatchReadBorrow
import Proofs.StateDispatchReadCleanup
import Proofs.StateDispatchReadFinish
import Proofs.StateDispatchStorageState

/-! Original resources and exact sequential memory for deployed f435. -/
namespace WNear.Proofs.StateDispatchRead
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid)
set_option maxRecDepth 16384

structure Layout extends StateDispatchPrefix.Layout where
  inputRegister : UInt32
  inputPointer : UInt32

def asLength (p : Layout) : StateDispatchLength.Layout := {toLayout := p.toLayout,input := p.inputRegister}
def scratch (p : Layout) := StateDispatchPrefix.scratch p.toLayout
def acquiredMemory (p : Layout) := StateDispatchLength.acquiredMemory (asLength p)
def highMemory (p : Layout) := StateDispatchReadBorrow.highMemory (acquiredMemory p) (scratch p)
def borrowed (p : Layout) := StateDispatchReadBorrow.pointer (acquiredMemory p) (scratch p)
def lowMemory (p : Layout) := StateDispatchReadBorrow.lowMemory (acquiredMemory p) (scratch p)
def selected (p : Layout) := StateDispatchReadBorrow.selected (acquiredMemory p) (scratch p)
def receiver (p : Layout) := readI32 (lowMemory p) (selected p).toNat
def vtable (p : Layout) := readI32 (lowMemory p) ((selected p).toNat + 4)
def element (p : Layout) := readI32 (lowMemory p) ((vtable p).toNat + 12)
def register (p : Layout) := readI64 (lowMemory p) p.inputRegister.toNat
def ptr (p : Layout) := ValueReturnDispatch.packed32 (lowMemory p) p.inputPointer.toNat
def readMemory (p : Layout) (bytes : List UInt8) := (lowMemory p).writeList (ptr p).toNat bytes
def counter (p : Layout) (bytes : List UInt8) := readI32 (readMemory p bytes) (((scratch p + 8) ||| 4).toNat)

def acquired (s : Store NearState) (op : Nat) (p : Layout) := StateDispatchPrefix.acquired s op p.toLayout
def checked (s : Store NearState) (op : Nat) (p : Layout) :=
  StateDispatchReadBorrow.after (acquired s op p) op p.memoryIndex (acquiredMemory p) (scratch p)
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (checked s op p) op 9
def returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) (bytes : List UInt8) :=
  StateReadRegister.readCallAfter cfg (arguments s cfg.regularOpCost p) p.mi (ptr p) bytes

def acquiredFrame (frame : CallFrame) (p : Layout) := StateDispatchPrefix.guardedFrame frame p.toLayout 3
def copiedFrame (frame : CallFrame) (p : Layout) := StateDispatchReadBorrow.finalFrame (acquiredFrame frame p) (acquiredMemory p) (scratch p)
def argumentFrame (frame : CallFrame) (p : Layout) := {copiedFrame frame p with locals := (copiedFrame frame p).locals.set! 4 (.i32 (selected p))}

structure Code (s : Store NearState) (p : Layout) (inst extra : Nat) : Prop where
  prefixCode : StateDispatchPrefix.Code s p.toLayout inst
  nonnullIndex : p.mi.funcAddrs[430]? = some 430
  nonnullFunction : s.funcs[430]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction)
  releaseIndex : p.mi.funcAddrs[431]? = some 431
  releaseFunction : s.funcs[431]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction)
  swapIndex : p.mi.funcAddrs[672]? = some 672
  swapFunction : s.funcs[672]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  returnIndex : p.mi.funcAddrs[433]? = some 433
  returnFunction : s.funcs[433]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.checkFunction)
  readElement : p.table.elems[(element p).toNat]? = some (.func 240)
  readType : p.mi.types[4]? = some WNear.Binary.StateRead.registerForwardSignature
  readIndex : p.mi.funcAddrs[240]? = some 240
  readFunction : s.funcs[240]? = some (.wasm WNear.Binary.StateRead.registerForwardSignature inst WNear.Binary.StateRead.registerForwardFunction)
  hostIndex : p.mi.funcAddrs[0]? = some 0
  hostFunction : s.funcs[0]? = some (.host (metered extra "read_register" readRegisterFn).toHostFn)

structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame) (callers : List CallFrame) (p : Layout) (bytes : List UInt8) (extra : Nat) : Prop where
  code : Code s p frame.inst extra
  prefixReady : StateDispatchPrefix.Ready s limits frame callers p.toLayout 3
  registerLocal : frame.locals[1]? = some (.i32 p.inputRegister)
  pointerLocal : frame.locals[2]? = some (.i32 p.inputPointer)
  localSize : 5 ≤ frame.locals.size
  highBound : (scratch p).toNat + 16 ≤ (acquiredMemory p).byteSize
  lowBound : (scratch p).toNat + 12 ≤ (highMemory p).byteSize
  selectBound : (borrowed p).toNat + 4 ≤ (lowMemory p).byteSize
  selectedNonzero : selected p ≠ 0
  cellBound : (selected p).toNat + 8 ≤ (lowMemory p).byteSize
  registerBound : p.inputRegister.toNat + 8 ≤ (lowMemory p).byteSize
  pointerBound : p.inputPointer.toNat + 4 ≤ (lowMemory p).byteSize
  vtableBound : (vtable p).toNat + 16 ≤ (lowMemory p).byteSize
  registerValue : s.host.registers (register p).toNat = some bytes
  payloadBound : (ptr p).toNat + bytes.length ≤ (lowMemory p).byteSize
  releaseBound : ((scratch p + 8) ||| 4).toNat + 4 ≤ (readMemory p bytes).byteSize
  counterBound : (counter p bytes).toNat + 4 ≤ (readMemory p bytes).byteSize

 theorem Code.transport (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : t.funcs = s.funcs) (hm : t.modules = s.modules) (ht : t.tables = s.tables) : Code t p inst extra := by
  refine ⟨h.prefixCode.transport s t p.toLayout inst hf hm ht,h.nonnullIndex,?_,h.releaseIndex,?_,h.swapIndex,?_,h.returnIndex,?_,
    h.readElement,h.readType,h.readIndex,?_,h.hostIndex,?_⟩ <;> rw [hf]
  · exact h.nonnullFunction
  · exact h.releaseFunction
  · exact h.swapFunction
  · exact h.returnFunction
  · exact h.readFunction
  · exact h.hostFunction
end WNear.Proofs.StateDispatchRead
