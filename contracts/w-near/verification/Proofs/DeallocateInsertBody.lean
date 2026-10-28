import Proofs.DeallocateInsertNeighbors
import Proofs.DeallocateInsertGas

/-! Full actual f582 body on the captured nonzero previous-allocated next-disabled insertion path. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode readI32 writeI32

def finalFrame (frame : CallFrame) (p : Layout) := neighborFrame (headFrame frame p) p

/-- All113active steps of deployed f582, including real570,568and576calls,
with the sequential memory result and129charged opcode units. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (129 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits base.toArray
      (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 113) (.next (atCode s limits base.toArray frame callers (WNear.Binary.Deallocate.coreBody ++ code)))
      (129 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let label : Label := {arity := 0,height := base.toArray.size,rest := code,loop := none}
  let blocked := emptyBlockFrame frame base.toArray.size code
  let hf := headFrame blocked p
  have rd : Ready s blocked p :=
    ⟨hr.code,hr.memory,hr.allocator,hr.pointer,hr.length,hr.alignment,hr.locals,hr.native⟩
  have funded := after_credits s op rest p (hc.mono (by dsimp [op]; omega))
  have exitNext : WP cfg fuel (.next (atCode (after s op p) limits base.toArray
      (finalFrame frame p) callers label.rest)) rest post := by simpa only [label,op] using hnext
  have exit := wp_end_label cfg fuel rest (after s op p) limits base.toArray (finalFrame frame p) callers label post funded exitNext
  have next : WP cfg (fuel + 1) (.next (atCode (neighborAfter (zeroed s op p) op p) limits base.toArray
      (neighborFrame hf p) callers [])) rest post := by
    simpa only [after,finalFrame,neighborFrame,headFrame,markedFrame,savedFrame,
      disabledNextFrame,maskedNextFrame,rawNextFrame,Deallocate.previousFrame,hf,blocked,emptyBlockFrame,label] using exit
  have h0 : hf.locals[0]? = some (.i32 p.allocator) := by
    simpa only [hf,headFrame,markedFrame,savedFrame,blocked,emptyBlockFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0),Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 0)] using hr.allocator
  have h1 : hf.locals[1]? = some (.i32 p.pointer) := by
    simpa only [hf,headFrame,markedFrame,savedFrame,blocked,emptyBlockFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 1),Array.getElem?_setIfInBounds_ne (by decide : 4 ≠ 1)] using hr.pointer
  have hn2 : 2 < frame.locals.size := by have h := hr.locals; omega
  have hn4 : 4 < frame.locals.size := by have h := hr.locals; omega
  have hn2saved : 2 < (frame.locals.setIfInBounds 4 (.i32 (oldHead p))).size := by simpa only [Array.size_setIfInBounds] using hn2
  have h2 : hf.locals[2]? = some (.i32 p.header) := by
    simp only [hf,headFrame,markedFrame,savedFrame,blocked,emptyBlockFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_self_of_lt hn2saved]
  have h4 : hf.locals[4]? = some (.i32 (oldHead p)) := by
    simp only [hf,headFrame,markedFrame,savedFrame,blocked,emptyBlockFrame,Array.set!_eq_setIfInBounds,
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 4),Array.getElem?_setIfInBounds_self_of_lt hn4]
  have hsz : 7 ≤ hf.locals.size := by
    simp only [hf,headFrame,markedFrame,savedFrame,blocked,emptyBlockFrame,Array.size_set!]
    have h := hr.locals; omega
  have nc := zeroed_code s op frame.inst p hr.code
  have nm := zeroed_memory s op p hr.memory
  have tail := wp_neighbors cfg (fuel + 1) rest (zeroed s op p) limits base hf callers [] p post nc nm h0 h1 h2 h4 hsz hr.native
    (zeroed_credits s op (38 * op + rest) p (hc.mono (by dsimp [op]; omega))) next
  have headNext : WP cfg (fuel + 45) (.next (atCode (zeroed s cfg.regularOpCost p) limits base.toArray
      (headFrame blocked p) callers (WNear.Binary.Deallocate.inspectNeighbors ++ WNear.Binary.Deallocate.installHead)))
      (38 * cfg.regularOpCost + rest) post := by
    simpa only [hf,op,List.append_nil,Nat.add_assoc,Nat.reduceAdd] using tail
  have head := wp_head cfg (fuel + 45) (38 * cfg.regularOpCost + rest) s limits base blocked callers
    (WNear.Binary.Deallocate.inspectNeighbors ++ WNear.Binary.Deallocate.installHead) p post rd hd (hc.mono (by omega)) headNext
  unfold WNear.Binary.Deallocate.coreBody
  apply wp_block_empty cfg (fuel + 112) _ s limits base.toArray frame callers _ code post hc
  simpa only [headCode,headBeforeCode,headAfterCode,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 91 * cfg.regularOpCost + (38 * cfg.regularOpCost + rest) = 129 * cfg.regularOpCost + rest by omega] using head

end WNear.Proofs.DeallocateInsert
