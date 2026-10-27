import Proofs.DeallocateCoreHead
import Proofs.DeallocateCoreUnlink
import Proofs.DeallocateCoreTail

/-! Actual four-block previous-free selection, unlink, and coalescing tail. -/
namespace WNear.Proofs.DeallocateCore
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def neighborsAfter (s : Store NearState) (op : Nat) (p : Layout) :=
  DeallocateCoreTail.after (DeallocateCoreUnlink.unlinkFrom (paid s op 15) op p) op p.memoryIndex
    (unlinkedMemory p) p.allocator (oldHead p)
def neighborsFrame (frame : CallFrame) (p : Layout) :=
  DeallocateCoreTail.restoredFrame (Deallocate.previousFrame frame p.previous) (oldHead p)

theorem neighborsAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (127 * op + rest)) : (neighborsAfter s op p).host.gas.Credits rest := by
  apply DeallocateCoreTail.after_credits _ op p.memoryIndex rest (unlinkedMemory p) p.allocator (oldHead p)
  apply DeallocateCoreUnlink.unlinkFrom_credits _ op (39 * op + rest) p
  exact paid_credits s op 15 _ (hc.mono (by omega))

/-- The complete captured coalescing branch executes the real575and576calls.
All case selection is derived from primitive native reads. -/
theorem wp_neighbors (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post)
    (hcode : Code s frame.inst p) (hm : s.mems[p.memoryIndex]? = some (zeroMemory p))
    (ha : frame.locals[0]? = some (.i32 p.allocator)) (hp : frame.locals[1]? = some (.i32 p.pointer))
    (hh : frame.locals[2]? = some (.i32 p.header)) (ho : frame.locals[4]? = some (.i32 (oldHead p)))
    (hs : 6 ≤ frame.locals.size) (hn : Native p) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (127 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (neighborsAfter s cfg.regularOpCost p) limits base.toArray
      (neighborsFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 119) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.Deallocate.inspectNeighbors ++ WNear.Binary.Deallocate.installHead ++ code)))
      (127 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let first := emptyBlockFrame frame base.toArray.size (WNear.Binary.Deallocate.installHead ++ code)
  let second := emptyBlockFrame first base.toArray.size WNear.Binary.Deallocate.insertHead
  let third := emptyBlockFrame second base.toArray.size WNear.Binary.Deallocate.mergePrevious
  let updated := Deallocate.previousFrame frame p.previous
  let selected := paid s op 15
  let unlinked := DeallocateCoreUnlink.unlinkFrom selected op p
  have c15 : selected.host.gas.Credits (112 * op + rest) := paid_credits s op 15 _ (hc.mono (by dsimp [op]; omega))
  have cUnlink : unlinked.host.gas.Credits (39 * op + rest) :=
    DeallocateCoreUnlink.unlinkFrom_credits selected op _ p (c15.mono (by omega))
  have codeSelected : Code selected frame.inst p := by
    apply Code.transport s selected frame.inst p hcode
    · simp only [selected,paid,chargedStore]
    · simp only [selected,paid,chargedStore]
  have codeUnlink := DeallocateCoreUnlink.unlinkFrom_code selected op frame.inst p codeSelected
  have mSelected : selected.mems[p.memoryIndex]? = some (zeroMemory p) := by simpa only [selected,paid,chargedStore] using hm
  have mUnlink := DeallocateCoreUnlink.unlinkFrom_memory selected op p mSelected
  have h5 : 5 < frame.locals.size := by omega
  have updated0 : updated.locals[0]? = some (.i32 p.allocator) := by
    simpa only [updated,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 5 ≠ 0)] using ha
  have updated2 : updated.locals[2]? = some (.i32 p.header) := by
    simpa only [updated,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 5 ≠ 2)] using hh
  have updated4 : updated.locals[4]? = some (.i32 (oldHead p)) := by
    simpa only [updated,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_ne (by decide : 5 ≠ 4)] using ho
  have updated5 : updated.locals[5]? = some (.i32 p.previous) := by
    simp only [updated,Deallocate.previousFrame,Array.set!_eq_setIfInBounds,Array.getElem?_setIfInBounds_self_of_lt h5]
  have hnTail : WP cfg fuel (.next (atCode (DeallocateCoreTail.after unlinked op p.memoryIndex (unlinkedMemory p)
      p.allocator (oldHead p)) limits base.toArray (DeallocateCoreTail.restoredFrame updated (oldHead p)) callers code)) rest post := by
    simpa only [neighborsAfter,neighborsFrame,selected,unlinked,updated,op] using hnext
  have tail := DeallocateCoreTail.wp_tail cfg fuel rest unlinked limits base updated callers code p (unlinkedMemory p) post
    codeUnlink mUnlink updated0 updated2 updated4 updated5 (by simp only [updated,Deallocate.previousFrame,Array.size_set!]; omega)
    hn.unlinkedHeaderBound hn.unlinkedFlag hn.unlinkedPreviousBound hn.previousSize hn.finalAllocatorBound hd
    (cUnlink.mono (by dsimp [op]; omega)) hnTail
  have hnUnlink : WP cfg (fuel + 32) (.next (atCode (DeallocateCoreUnlink.unlinkFrom selected op p) limits base.toArray
      (Deallocate.previousFrame second p.previous) callers DeallocateCoreTail.tailCode)) (39 * cfg.regularOpCost + rest) post := by
    simpa only [unlinked,updated,second,first,Deallocate.previousFrame,emptyBlockFrame,op] using tail
  have hlocal2 : (Deallocate.previousFrame second p.previous).locals[2]? = some (.i32 p.header) := by
    simpa only [updated,Deallocate.previousFrame,second,first,emptyBlockFrame] using updated2
  have unlink := DeallocateCoreUnlink.wp_unlink cfg (fuel + 32) (39 * cfg.regularOpCost + rest) selected limits base
    (Deallocate.previousFrame second p.previous) callers DeallocateCoreTail.tailCode p post codeSelected mSelected hlocal2 hn hd
    (c15.mono (by dsimp [op]; omega)) hnUnlink
  have hnPrevious : WP cfg (fuel + 100) (.next (atCode (paid s cfg.regularOpCost 15) limits base.toArray
      (Deallocate.previousFrame second p.previous) callers WNear.Binary.Deallocate.mergePrevious)) (112 * cfg.regularOpCost + rest) post := by
    simpa only [selected,op,WNear.Binary.Deallocate.mergePrevious,DeallocateCoreTail.tailCode,
      List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
      show 73 * cfg.regularOpCost + (39 * cfg.regularOpCost + rest) = 112 * cfg.regularOpCost + rest by omega] using unlink
  have previous := Deallocate.wp_previous_guard cfg (fuel + 100) (112 * cfg.regularOpCost + rest) s limits base.toArray second callers
    WNear.Binary.Deallocate.mergePrevious (WNear.Binary.Deallocate.nextGuard ++ WNear.Binary.Deallocate.linkNext)
    p.pointer p.previousAddress p.previous p.mi p.memoryIndex (zeroMemory p) post hp hs hn.previousAddressEq hn.previousRead
    hcode.module hcode.memoryIndex hm hn.previousAddressBound hn.previousNonzero hn.previousBound hn.previousFree
    (hc.mono (by omega)) hnPrevious
  unfold WNear.Binary.Deallocate.inspectNeighbors
  apply wp_block_empty cfg (fuel + 118) _ s limits base.toArray frame callers _ (WNear.Binary.Deallocate.installHead ++ code) post hc
  apply wp_block_empty cfg (fuel + 117) _ s limits base.toArray first callers _ WNear.Binary.Deallocate.insertHead post hc
  apply wp_block_empty cfg (fuel + 116) _ s limits base.toArray second callers _ WNear.Binary.Deallocate.mergePrevious post hc
  apply wp_block_empty cfg (fuel + 115) _ s limits base.toArray third callers _ (WNear.Binary.Deallocate.nextGuard ++ WNear.Binary.Deallocate.linkNext) post hc
  simpa only [third,Nat.add_assoc,Nat.reduceAdd,
    show 15 * cfg.regularOpCost + (112 * cfg.regularOpCost + rest) = 127 * cfg.regularOpCost + rest by omega] using previous

end WNear.Proofs.DeallocateCore
