import Proofs.InterfaceSetState
import Proofs.InterfaceSetInstallTail
import Proofs.InterfaceBorrowState
import Proofs.ValueReturnThreadLocal

/-! Explicit sequential states of the setter's initialized-thread-local path. -/
namespace WNear.Proofs.InterfaceSetPhases
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid)
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384

def looked (s : Store NearState) (op : Nat) (p : Layout) :=
  ValueReturnThreadLocal.indirectAfter (lookupBefore s op p) op

def arguments (s : Store NearState) (op : Nat) (p : Layout) := paid (paid (looked s op p) op 3) op 5

def acquired (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceBorrow.calledAcquireStore (arguments s op p) op p.globalIndex p.memoryIndex
    (scratch p) (scratch p + 8) 1074904 (savedMemory p)

def acquiredMemory (p : Layout) := InterfaceBorrow.recordMemory
  (writeI32 (savedMemory p) 1074904 4294967295) (scratch p + 8) 1074904

def highMemory (p : Layout) := writeI32 (acquiredMemory p) ((scratch p).toNat + 28)
  (readI32 (acquiredMemory p) ((scratch p).toNat + 12))

def pointer (p : Layout) := readI32 (highMemory p) ((scratch p).toNat + 8)

def lowMemory (p : Layout) := writeI32 (highMemory p) ((scratch p).toNat + 24) (pointer p)

def installed (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceSetInstallTail.after (acquired s op p) op p.memoryIndex (scratch p) p.receiver p.vtable
    (acquiredMemory p) (highMemory p) (lowMemory p)

def installedMemory (p : Layout) := InterfaceInstall.installMemory (lowMemory p) (pointer p).toNat p.receiver p.vtable

def counter (p : Layout) := readI32 (installedMemory p) (((scratch p + 24) ||| 4).toNat)

def released (s : Store NearState) (op : Nat) (p : Layout) :=
  InterfaceBorrow.calledReleaseStore (paid (installed s op p) op 5) op p.memoryIndex (counter p) (installedMemory p)

def branched (s : Store NearState) (op : Nat) (p : Layout) := chargedStore (paid (released s op p) op 2) op

def finalStore (s : Store NearState) (op : Nat) (p : Layout) :=
  setGlobal (paid (ValueReturnOuter.checkAfter (paid (branched s op p) op 1) op p.globalIndex (scratch p)) op 4)
    p.globalIndex (.i32 (scratch p + 32))

def pointerFrame (frame : CallFrame) (p : Layout) :=
  InterfaceSetInstallTail.afterFrame (guardedFrame frame p) (scratch p) (highMemory p)

def finalFrame (frame : CallFrame) (p : Layout) :=
  {pointerFrame frame p with locals := (pointerFrame frame p).locals.set! 1 (.i32 0)}

/-- Conditions for the actual initialized lookup and empty-interface branch.
The lazy first-installation branch requires separate composition. -/
structure Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) : Prop where
  code : Code s p frame.inst
  interfaceLocal : frame.locals[0]? = some (.i32 p.interface)
  receiverLocal : frame.locals[1]? = some (.i32 p.receiver)
  vtableLocal : frame.locals[2]? = some (.i32 p.vtable)
  localSize : 4 ≤ frame.locals.size
  memory : s.mems[p.memoryIndex]? = some p.memory
  global : s.globals[p.globalIndex]? = some p.global
  sp : p.global.value = .i32 p.sp
  memoryWf : p.memory.wf
  saveFirstBound : (scratch p).toNat + 20 + 4 ≤ p.memory.byteSize
  saveSecondBound : (scratch p).toNat + 16 + 4 ≤ (writeI32 p.memory ((scratch p).toNat + 20) p.vtable).byteSize
  interfaceBound : p.interface.toNat + 4 ≤ (savedMemory p).byteSize
  interfaceRead : readI32 (savedMemory p) p.interface.toNat = p.lookupElement
  threadBound : 1074900 + 4 ≤ (savedMemory p).byteSize
  threadStatus : readI32 (savedMemory p) 1074900 = 1
  cellBound : 1074904 + 4 ≤ (savedMemory p).byteSize
  cellEmpty : readI32 (savedMemory p) 1074904 = 0
  acquireOutBound : (scratch p + 8).toNat + 8 ≤ (savedMemory p).byteSize
  highReadBound : (scratch p).toNat + 12 + 4 ≤ (acquiredMemory p).byteSize
  highWriteBound : (scratch p).toNat + 28 + 4 ≤ (acquiredMemory p).byteSize
  lowReadBound : (scratch p).toNat + 8 + 4 ≤ (highMemory p).byteSize
  lowWriteBound : (scratch p).toNat + 24 + 4 ≤ (highMemory p).byteSize
  lowMemoryWf : (lowMemory p).wf
  pointerBound : (pointer p).toNat + 8 ≤ (lowMemory p).byteSize
  existingEmpty : readI32 (lowMemory p) (pointer p).toNat = 0
  releaseRecordBound : ((scratch p + 24) ||| 4).toNat + 4 ≤ (installedMemory p).byteSize
  releaseCounterBound : (counter p).toNat + 4 ≤ (installedMemory p).byteSize
  depth : callers.length + 3 < limits.maxCallDepth

end WNear.Proofs.InterfaceSetPhases
