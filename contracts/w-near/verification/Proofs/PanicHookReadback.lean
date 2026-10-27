import Proofs.PanicHookSetState
import Proofs.PanicAllocateReadback

/-! Exact installed words of the deployed panic-hook replacement writes. -/
namespace WNear.Proofs.PanicHookReadback
open Wasm Wasm.Near MeteredLogic PanicHookSet
open PanicAllocateReadback (read_write_self read_write_frame)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 writeI32

/-- The actual four writes install the supplied hook and release the lock. -/
theorem final_spec (memory : Memory) (receiver vtable : UInt32)
    (hw : memory.wf) (hb : 1074936 ≤ memory.byteSize) :
    (finalMemory memory receiver vtable).wf ∧
    (finalMemory memory receiver vtable).byteSize = memory.byteSize ∧
    (finalMemory memory receiver vtable).max = memory.max ∧
    readI32 (finalMemory memory receiver vtable) 1074920 = 0 ∧
    readI32 (finalMemory memory receiver vtable) 1074924 = receiver ∧
    readI32 (finalMemory memory receiver vtable) 1074928 = vtable ∧
    readI32 (finalMemory memory receiver vtable) 1074932 = readI32 memory 1074932 := by
  have b1 : 1074920 + 4 ≤ memory.byteSize := by omega
  have h1 := writeI32_spec memory 1074920 4294967295 hw b1
  have b2 : 1074928 + 4 ≤ (lockedMemory memory).byteSize := by rw [show (lockedMemory memory).byteSize = memory.byteSize from h1.2.1]; omega
  have h2 := writeI32_spec (lockedMemory memory) 1074928 vtable h1.1 b2
  have b3 : 1074924 + 4 ≤ (vtableMemory memory vtable).byteSize := by
    rw [show (vtableMemory memory vtable).byteSize = (lockedMemory memory).byteSize from h2.2.1,
      show (lockedMemory memory).byteSize = memory.byteSize from h1.2.1]; omega
  have h3 := writeI32_spec (vtableMemory memory vtable) 1074924 receiver h2.1 b3
  have b4 : 1074920 + 4 ≤ (receiverMemory memory receiver vtable).byteSize := by
    rw [show (receiverMemory memory receiver vtable).byteSize = (vtableMemory memory vtable).byteSize from h3.2.1,
      show (vtableMemory memory vtable).byteSize = (lockedMemory memory).byteSize from h2.2.1,
      show (lockedMemory memory).byteSize = memory.byteSize from h1.2.1]; omega
  have h4 := writeI32_spec (receiverMemory memory receiver vtable) 1074920 0 h3.1 b4
  have lock := read_write_self (receiverMemory memory receiver vtable) 1074920 0 h3.1 b4
  have receiverSelf := read_write_self (vtableMemory memory vtable) 1074924 receiver h2.1 b3
  have receiverFrame := read_write_frame (receiverMemory memory receiver vtable) 1074924 1074920 0 h3.1 b4 (by omega)
  have vtableSelf := read_write_self (lockedMemory memory) 1074928 vtable h1.1 b2
  have vtableFrame3 := read_write_frame (vtableMemory memory vtable) 1074928 1074924 receiver h2.1 b3 (by omega)
  have vtableFrame4 := read_write_frame (receiverMemory memory receiver vtable) 1074928 1074920 0 h3.1 b4 (by omega)
  have init1 := read_write_frame memory 1074932 1074920 4294967295 hw b1 (by omega)
  have init2 := read_write_frame (lockedMemory memory) 1074932 1074928 vtable h1.1 b2 (by omega)
  have init3 := read_write_frame (vtableMemory memory vtable) 1074932 1074924 receiver h2.1 b3 (by omega)
  have init4 := read_write_frame (receiverMemory memory receiver vtable) 1074932 1074920 0 h3.1 b4 (by omega)
  refine ⟨h4.1, h4.2.1.trans (h3.2.1.trans (h2.2.1.trans h1.2.1)),
    h4.2.2.1.trans (h3.2.2.1.trans (h2.2.2.1.trans h1.2.2.1)), lock, ?_, ?_, ?_⟩
  · exact receiverFrame.trans receiverSelf
  · exact vtableFrame4.trans (vtableFrame3.trans vtableSelf)
  · exact init4.trans (init3.trans (init2.trans init1))

end WNear.Proofs.PanicHookReadback
