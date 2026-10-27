import Proofs.StateDispatchPrefixState
import Proofs.StateDispatchHosts
import Proofs.StateDispatchBorrow
import Proofs.StateDispatchLengthCleanup
import Proofs.StateDispatchLengthFinish

/-! Original resources and deterministic accepted phases of deployed f440. -/
namespace WNear.Proofs.StateDispatchLength
open Wasm Wasm.Near MeteredLogic MeteredHosts
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

structure Layout extends StateDispatchPrefix.Layout where
  input : UInt32

def scratch (p : Layout) := StateDispatchPrefix.scratch p.toLayout

def acquiredMemory (p : Layout) := ValueReturnAcquire.recordMemory
  (writeI32 p.memory 1074904 (ValueReturnAcquire.nextCount p.memory 1074904)) (scratch p) 1074904
def highMemory (p : Layout) := writeI32 (acquiredMemory p) ((scratch p).toNat + 12)
  (readI32 (acquiredMemory p) ((scratch p).toNat + 4))
def borrowed (p : Layout) := readI32 (highMemory p) (scratch p).toNat
def lowMemory (p : Layout) := writeI32 (highMemory p) ((scratch p).toNat + 8) (borrowed p)
def selected (p : Layout) := if readI32 (lowMemory p) (borrowed p).toNat ≠ 0 then borrowed p else 0
def receiver (p : Layout) := readI32 (lowMemory p) (selected p).toNat
def vtable (p : Layout) := readI32 (lowMemory p) ((selected p).toNat + 4)
def element (p : Layout) := readI32 (lowMemory p) ((vtable p).toNat + 16)
def register (p : Layout) := readI64 (lowMemory p) p.input.toNat
def counter (p : Layout) := readI32 (lowMemory p) (((scratch p + 8) ||| 4).toNat)

def acquired (s : Store NearState) (op : Nat) (p : Layout) := StateDispatchPrefix.acquired s op p.toLayout

def high (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (acquired s op p) op 4) p.memoryIndex ((scratch p).toNat + 12) (acquiredMemory p)
    (readI32 (acquiredMemory p) ((scratch p).toNat + 4))
def low (s : Store NearState) (op : Nat) (p : Layout) :=
  storeI32 (paid (high s op p) op 5) p.memoryIndex ((scratch p).toNat + 8) (highMemory p) (borrowed p)
def checked (s : Store NearState) (op : Nat) (p : Layout) := ValueReturnOuter.nonnullAfter (paid (low s op p) op 6) op
def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (checked s op p) op 7
def resultValue (s : Store NearState) (op : Nat) (p : Layout) := StateReadRegister.lengthValue (arguments s op p) (register p)
def returned (cfg : WasmConfig) (s : Store NearState) (p : Layout) := StateReadRegister.lengthCallAfter cfg (arguments s cfg.regularOpCost p) p.mi
def cleaned (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDispatchLengthCleanup.after (returned cfg s p) cfg.regularOpCost p.memoryIndex (counter p) (lowMemory p)
def finalStore (cfg : WasmConfig) (s : Store NearState) (p : Layout) :=
  StateDispatchLengthFinish.after (cleaned cfg s p) cfg.regularOpCost p.globalIndex (scratch p)

def acquiredFrame (frame : CallFrame) (p : Layout) := StateDispatchPrefix.guardedFrame frame p.toLayout 2
def copiedFrame (frame : CallFrame) (p : Layout) :=
  {acquiredFrame frame p with locals := (acquiredFrame frame p).locals.set! 0 (.i32 (borrowed p))}
def argumentFrame (frame : CallFrame) (p : Layout) :=
  {copiedFrame frame p with locals := (copiedFrame frame p).locals.set! 0 (.i32 (selected p))}
def cleanedFrame (frame : CallFrame) (p : Layout) (value : UInt64) := StateDispatchLengthCleanup.finalFrame (argumentFrame frame p) value
def finalFrame (frame : CallFrame) (p : Layout) (value : UInt64) := StateDispatchLengthFinish.finalFrame (cleanedFrame frame p value) value

structure Code (s : Store NearState) (p : Layout) (inst extra : Nat) : Prop where
  prefixCode : StateDispatchPrefix.Code s p.toLayout inst
  nonnullIndex : p.mi.funcAddrs[430]? = some 430
  nonnullFunction : s.funcs[430]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.nonnullFunction)
  releaseIndex : p.mi.funcAddrs[431]? = some 431
  releaseFunction : s.funcs[431]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.releaseFunction)
  swapIndex : p.mi.funcAddrs[672]? = some 672
  swapFunction : s.funcs[672]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  returnIndex : p.mi.funcAddrs[432]? = some 432
  returnFunction : s.funcs[432]? = some (.wasm WNear.Binary.StateDispatch.returnSignature inst WNear.Binary.StateDispatch.returnFunction)
  lengthElement : p.table.elems[(element p).toNat]? = some (.func 241)
  lengthType : p.mi.types[7]? = some WNear.Binary.StateRead.lengthForwardSignature
  lengthIndex : p.mi.funcAddrs[241]? = some 241
  lengthFunction : s.funcs[241]? = some (.wasm WNear.Binary.StateRead.lengthForwardSignature inst WNear.Binary.StateRead.lengthForwardFunction)
  hostIndex : p.mi.funcAddrs[1]? = some 1
  hostFunction : s.funcs[1]? = some (.host (metered extra "register_len" registerLenFn).toHostFn)

structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame) (callers : List CallFrame) (p : Layout) (extra : Nat) : Prop where
  code : Code s p frame.inst extra
  prefixReady : StateDispatchPrefix.Ready s limits frame callers p.toLayout 2
  inputLocal : frame.locals[1]? = some (.i32 p.input)
  localSize : 5 ≤ frame.locals.size
  highBound : (scratch p).toNat + 16 ≤ (acquiredMemory p).byteSize
  lowBound : (scratch p).toNat + 12 ≤ (highMemory p).byteSize
  selectBound : (borrowed p).toNat + 4 ≤ (lowMemory p).byteSize
  selectedNonzero : selected p ≠ 0
  cellBound : (selected p).toNat + 8 ≤ (lowMemory p).byteSize
  inputBound : p.input.toNat + 8 ≤ (lowMemory p).byteSize
  vtableBound : (vtable p).toNat + 20 ≤ (lowMemory p).byteSize
  releaseBound : ((scratch p + 8) ||| 4).toNat + 4 ≤ (lowMemory p).byteSize
  counterBound : (counter p).toNat + 4 ≤ (lowMemory p).byteSize

 theorem Code.transport (s t : Store NearState) (p : Layout) (inst extra : Nat)
    (h : Code s p inst extra) (hf : t.funcs = s.funcs) (hm : t.modules = s.modules) (ht : t.tables = s.tables) : Code t p inst extra := by
  refine ⟨h.prefixCode.transport s t p.toLayout inst hf hm ht,h.nonnullIndex,?_,h.releaseIndex,?_,h.swapIndex,?_,h.returnIndex,?_,
    h.lengthElement,h.lengthType,h.lengthIndex,?_,h.hostIndex,?_⟩ <;> rw [hf]
  · exact h.nonnullFunction
  · exact h.releaseFunction
  · exact h.swapFunction
  · exact h.returnFunction
  · exact h.lengthFunction
  · exact h.hostFunction
end WNear.Proofs.StateDispatchLength
