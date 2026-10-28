import Proofs.AllocateFlaggedMemory
import Proofs.AllocationGrowthRemainderStorageFacts

/-! The allocated storage header retains both in-use and next-disabled bits.
These are readbacks of the actual sequential flags-two split. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 writeI32 finalMemory flaggedMemory

theorem final_allocated_header(p:AllocateSearch.Layout)(hn:Native p):
    readI32 (finalMemory p) (header p).toNat=(finish p|||2)|||1:=by
  have b:=intervals p hn
  have cleared:=clearedFlag_shape p hn
  have flagged:=flagged_shape p hn
  have self:=PanicAllocateReadback.read_write_self (clearedFlagMemory p) (header p).toNat
    (readI32 (clearedFlagMemory p) (header p).toNat|||2) cleared.wf (by rw[cleared.size];omega)
  have value:readI32 (flaggedMemory p) (header p).toNat=finish p|||2:=by
    unfold flaggedMemory
    exact self.trans (congrArg (fun x:UInt32=>x|||2) (clearedFlag_header p hn))
  have marked:=PanicAllocateReadback.read_write_self (flaggedMemory p) (header p).toNat
    (readI32 (flaggedMemory p) (header p).toNat|||1) flagged.wf (by rw[flagged.size];omega)
  unfold finalMemory Allocate.markedMemory
  exact marked.trans (congrArg (fun x:UInt32=>x|||1) value)
end WNear.Proofs.AllocateFlagged

namespace WNear.Proofs.AllocationGrowthRemainder
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 AllocateRetry.finalMemory AllocateRetry.searchedMemory

theorem retry_allocated_header(p:AllocateRetry.Layout)(hn:AllocateRetry.Native p):
    readI32 (AllocateRetry.finalMemory p) (AllocateFlagged.header (AllocateRetry.secondLayout p)).toNat=
      (AllocateFlagged.finish (AllocateRetry.secondLayout p)|||2)|||1:=by
  have child:=AllocateRetry.native_second p hn
  have bounds:=AllocateFlagged.intervals (AllocateRetry.secondLayout p) child
  have interval:=retry_interval p hn
  rw [retry_final_word p hn _ (by omega)]
  simpa only [AllocateRetry.searchedMemory] using AllocateFlagged.final_allocated_header (AllocateRetry.secondLayout p) child
end WNear.Proofs.AllocationGrowthRemainder

namespace WNear.Proofs.StateReadStorageOuter
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] readI32 finalMemory actualRegister StateReadRegisterOuter.actualVector
 AllocateVector.result remainderLayout

theorem finalMemory_allocated_header(p:Layout)(hn:Native p)(ha:p.allocator=1074896):
    readI32 (finalMemory p) (AllocateFlagged.header (AllocateRetry.secondLayout (remainderLayout p))).toNat=
      (AllocateFlagged.finish (AllocateRetry.secondLayout (remainderLayout p))|||2)|||1:=by
  have native:=remainder_native p hn ha
  have child:=AllocateRetry.native_second (remainderLayout p) native
  have bounds:=AllocateFlagged.intervals (AllocateRetry.secondLayout (remainderLayout p)) child
  have interval:=remainder_interval p hn ha
  have pointer:AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector=
      AllocateFlagged.pointer (AllocateRetry.secondLayout (remainderLayout p)):=by
    simp only [remainderLayout,AllocateVector.remainderLayout,AllocateVector.layout690,
      AllocateVector.result,AllocateRecord.result,AllocateZeroedRetry.result,AllocateRetry.result]
  have room:=child.split.room
  have ptrNat:=Allocate.split_pointer_toNat (AllocateRetry.secondLayout (remainderLayout p)).memory
    (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p)))
    (AllocateRetry.secondLayout (remainderLayout p)).words child.split
  have hdrNat:=Allocate.split_header_toNat (AllocateRetry.secondLayout (remainderLayout p)).memory
    (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p)))
    (AllocateRetry.secondLayout (remainderLayout p)).words child.split
  have before:(AllocateFlagged.header (AllocateRetry.secondLayout (remainderLayout p))).toNat+4≤
      (AllocateVector.result (StateReadRegisterOuter.actualVector (actualRegister p)).toVector).toNat:=by
    rw [pointer]
    change (Allocate.splitHeader _ _ _).toNat+4≤(Allocate.splitPointer _ _ _).toNat
    exact (by omega : (Allocate.splitHeader (AllocateRetry.secondLayout (remainderLayout p)).memory
      (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))) (AllocateRetry.secondLayout (remainderLayout p)).words).toNat+4≤
      (Allocate.splitPointer (AllocateRetry.secondLayout (remainderLayout p)).memory
      (AllocateFlagged.head (AllocateRetry.secondLayout (remainderLayout p))) (AllocateRetry.secondLayout (remainderLayout p)).words).toNat)
  rw [finalMemory_remainder_word p hn ha _ (by omega) before]
  exact AllocationGrowthRemainder.retry_allocated_header (remainderLayout p) native
end WNear.Proofs.StateReadStorageOuter
