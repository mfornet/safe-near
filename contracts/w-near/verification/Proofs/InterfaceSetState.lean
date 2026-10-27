import Proofs.InterfaceSetBody
import Proofs.InterfaceInstall
import Binary.InterfaceBorrow
import Binary.ValueReturnThreadLocal

/-! Original-data layout and code resources for the actual interface setter. -/
namespace WNear.Proofs.InterfaceSetState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open WNear.Proofs.InterfaceSetBody
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
  receiver : UInt32
  vtable : UInt32
  lookupElement : UInt32
  memory : Memory

def scratch (p : Layout) := p.sp - 32

def reserved (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid s op 5) p.globalIndex (.i32 (scratch p))

def savedMemory (p : Layout) := writeI32 (writeI32 p.memory ((scratch p).toNat + 20) p.vtable)
  ((scratch p).toNat + 16) p.receiver

def savedArguments (s : Store NearState) (op : Nat) (p : Layout) :=
  twoWordsStore (reserved s op p) op p.memoryIndex 20 16 (scratch p) p.vtable p.receiver p.memory

def lookupBefore (s : Store NearState) (op : Nat) (p : Layout) := paid (savedArguments s op p) op 2

def reservedFrame (frame : CallFrame) (p : Layout) := {frame with locals := frame.locals.set! 3 (.i32 (scratch p))}
def guardedFrame (frame : CallFrame) (p : Layout) := {reservedFrame frame p with locals := (reservedFrame frame p).locals.set! 0 (.i32 1074904)}

def nested (frame : CallFrame) (height : Nat) (code : List Instr) :=
  emptyBlockFrame (emptyBlockFrame frame height (WNear.Binary.InterfaceSet.epilogue ++ code))
    height WNear.Binary.InterfaceSet.fallback

/-- Only concrete module/function/table facts, not successful execution. -/
structure Code (s : Store NearState) (p : Layout) (inst : Nat) : Prop where
  module : s.modules[inst]? = some p.mi
  tableIndex : p.mi.tableAddrs[0]? = some p.tableAddress
  table : s.tables[p.tableAddress]? = some p.table
  lookupElement : p.table.elems[p.lookupElement.toNat]? = some (.func 565)
  lookupType : p.mi.types[1]? = some WNear.Binary.ValueReturnThreadLocal.lookupSignature
  lookupFunction : s.funcs[565]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.lookupSignature inst WNear.Binary.ValueReturnThreadLocal.lookupFunction)
  helperIndex : p.mi.funcAddrs[468]? = some 468
  helperFunction : s.funcs[468]? = some (.wasm WNear.Binary.ValueReturnThreadLocal.signature inst WNear.Binary.ValueReturnThreadLocal.function)
  acquireIndex : p.mi.funcAddrs[441]? = some 441
  acquireFunction : s.funcs[441]? = some (.wasm WNear.Binary.InterfaceBorrow.acquireSignature inst WNear.Binary.InterfaceBorrow.acquireFunction)
  takeIndex : p.mi.funcAddrs[492]? = some 492
  takeFunction : s.funcs[492]? = some (.wasm WNear.Binary.InterfaceBorrow.takeSignature inst WNear.Binary.InterfaceBorrow.takeFunction)
  guardIndex : p.mi.funcAddrs[464]? = some 464
  guardFunction : s.funcs[464]? = some (.wasm WNear.Binary.InterfaceInstall.guardSignature inst WNear.Binary.InterfaceInstall.guardFunction)
  releaseIndex : p.mi.funcAddrs[442]? = some 442
  releaseFunction : s.funcs[442]? = some (.wasm WNear.Binary.InterfaceBorrow.releaseSignature inst WNear.Binary.InterfaceBorrow.releaseFunction)
  swapIndex : p.mi.funcAddrs[672]? = some 672
  swapFunction : s.funcs[672]? = some (.wasm WNear.Binary.ValueReturnBorrow.nonnullSignature inst WNear.Binary.ValueReturnBorrow.swapFunction)
  checkIndex : p.mi.funcAddrs[433]? = some 433
  checkFunction : s.funcs[433]? = some (.wasm WNear.Binary.ValueReturnBorrow.voidSignature inst WNear.Binary.ValueReturnBorrow.checkFunction)
  memoryIndex : p.mi.memAddrs[0]? = some p.memoryIndex
  globalIndex : p.mi.globalAddrs[0]? = some p.globalIndex

theorem Code.transport (s t : Store NearState) (p : Layout) (inst : Nat)
    (h : Code s p inst) (hf : t.funcs = s.funcs) (hm : t.modules = s.modules)
    (ht : t.tables = s.tables) : Code t p inst := by
  exact {
    module := by rw [hm]; exact h.module
    tableIndex := h.tableIndex
    table := by rw [ht]; exact h.table
    lookupElement := h.lookupElement
    lookupType := h.lookupType
    lookupFunction := by rw [hf]; exact h.lookupFunction
    helperIndex := h.helperIndex
    helperFunction := by rw [hf]; exact h.helperFunction
    acquireIndex := h.acquireIndex
    acquireFunction := by rw [hf]; exact h.acquireFunction
    takeIndex := h.takeIndex
    takeFunction := by rw [hf]; exact h.takeFunction
    guardIndex := h.guardIndex
    guardFunction := by rw [hf]; exact h.guardFunction
    releaseIndex := h.releaseIndex
    releaseFunction := by rw [hf]; exact h.releaseFunction
    swapIndex := h.swapIndex
    swapFunction := by rw [hf]; exact h.swapFunction
    checkIndex := h.checkIndex
    checkFunction := by rw [hf]; exact h.checkFunction
    memoryIndex := h.memoryIndex
    globalIndex := h.globalIndex
  }

end WNear.Proofs.InterfaceSetState
