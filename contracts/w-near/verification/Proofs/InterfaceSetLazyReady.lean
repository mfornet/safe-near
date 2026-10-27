import Proofs.InterfaceSetLazyState
import Proofs.InterfaceSetCore
import Proofs.ValueReturnLazyFrame

/-! Native/data obligations on the exact heap produced by lazy initialization. -/
namespace WNear.Proofs.InterfaceSetLazyState
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.InterfaceSetState
set_option maxRecDepth 16384
set_option maxHeartbeats 200000

/-- Bounds and loaded words of the explicitly computed sequential heap. No
module, function, memory-array or global-array postcondition is assumed. -/
structure Bounds (p : Layout) (initializerAddress : Nat) : Prop where
  memoryWf : (memory p initializerAddress).wf
  cellBound : 1074904 + 4 ≤ (memory p initializerAddress).byteSize
  cellEmpty : readI32 (memory p initializerAddress) 1074904 = 0
  outBound : (scratch p + 8).toNat + 8 ≤ (memory p initializerAddress).byteSize
  highReadBound : (scratch p).toNat + 12 + 4 ≤ (InterfaceSetCore.acquiredMemory p (memory p initializerAddress)).byteSize
  highWriteBound : (scratch p).toNat + 28 + 4 ≤ (InterfaceSetCore.acquiredMemory p (memory p initializerAddress)).byteSize
  lowReadBound : (scratch p).toNat + 8 + 4 ≤ (InterfaceSetCore.highMemory p (memory p initializerAddress)).byteSize
  lowWriteBound : (scratch p).toNat + 24 + 4 ≤ (InterfaceSetCore.highMemory p (memory p initializerAddress)).byteSize
  lowMemoryWf : (InterfaceSetCore.lowMemory p (memory p initializerAddress)).wf
  pointerBound : (InterfaceSetCore.pointer p (memory p initializerAddress)).toNat + 8 ≤ (InterfaceSetCore.lowMemory p (memory p initializerAddress)).byteSize
  existingEmpty : readI32 (InterfaceSetCore.lowMemory p (memory p initializerAddress)) (InterfaceSetCore.pointer p (memory p initializerAddress)).toNat = 0
  recordBound : ((scratch p + 24) ||| 4).toNat + 4 ≤ (InterfaceSetCore.installedMemory p (memory p initializerAddress)).byteSize
  counterBound : (InterfaceSetCore.counter p (memory p initializerAddress)).toNat + 4 ≤ (InterfaceSetCore.installedMemory p (memory p initializerAddress)).byteSize

def finalStore (s : Store NearState) (op : Nat) (p : Layout) (initializerAddress : Nat) :=
  InterfaceSetCore.after (looked s op p initializerAddress) op p (memory p initializerAddress)

def finalFrame (frame : CallFrame) (p : Layout) (initializerAddress : Nat) :=
  InterfaceSetCore.finalFrame (reservedFrame frame p) p (memory p initializerAddress)

/-- All computed array fields needed by the setter core follow from its real
lazy lookup's proved memory and frame equations. -/
theorem coreReady (s : Store NearState) (op : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (initializerAddress : Nat)
    (hr : Setup s limits frame callers p initializerAddress) (hb : Bounds p initializerAddress) :
    InterfaceSetCore.Ready (looked s op p initializerAddress) limits (reservedFrame frame p) callers p
      (memory p initializerAddress) := by
  have codeBefore := InterfaceSetPhases.lookupBefore_code s op p frame.inst hr.code
  have fields := ValueReturnLazyLookup.indirectAfter_fields (lookupBefore s op p) op (lookupLayout p initializerAddress)
  have codeAfter := codeBefore.transport (lookupBefore s op p) (looked s op p initializerAddress) p frame.inst
    fields.1 fields.2.2 fields.2.1
  have hm := ValueReturnLazyLookup.indirectAfter_memory (lookupBefore s op p) op (lookupLayout p initializerAddress)
    (lookupBefore_memory s op p hr.memory)
  have hg := ValueReturnLazyLookup.indirectAfter_globals (lookupBefore s op p) op (lookupLayout p initializerAddress)
    (lookupBefore_global s op p hr.global) rfl
  have hmAfter : (looked s op p initializerAddress).mems[p.memoryIndex]? = some (memory p initializerAddress) := hm
  have hgAfter : (looked s op p initializerAddress).globals[p.globalIndex]? = some {p.global with value := .i32 (scratch p)} := by
    change (ValueReturnLazyLookup.indirectAfter (lookupBefore s op p) op (lookupLayout p initializerAddress)).globals[p.globalIndex]? = _
    rw [hg]
    exact lookupBefore_global s op p hr.global
  have hs : (reservedFrame frame p).locals[3]? = some (.i32 (scratch p)) := by
    simp [reservedFrame, show 3 < frame.locals.size by have h := hr.localSize; omega]
  have hreceiver : (reservedFrame frame p).locals[1]? = some (.i32 p.receiver) := by simpa [reservedFrame] using hr.receiverLocal
  have hvtable : (reservedFrame frame p).locals[2]? = some (.i32 p.vtable) := by simpa [reservedFrame] using hr.vtableLocal
  have hsize : 4 ≤ (reservedFrame frame p).locals.size := by simpa only [reservedFrame, Array.size_set!] using hr.localSize
  exact ⟨codeAfter, hs, hreceiver, hvtable, hsize, hmAfter, hgAfter, hb.memoryWf, hb.cellBound, hb.cellEmpty,
    hb.outBound, hb.highReadBound, hb.highWriteBound, hb.lowReadBound, hb.lowWriteBound, hb.lowMemoryWf,
    hb.pointerBound, hb.existingEmpty, hb.recordBound, hb.counterBound, by have h := hr.depth; omega⟩

end WNear.Proofs.InterfaceSetLazyState
