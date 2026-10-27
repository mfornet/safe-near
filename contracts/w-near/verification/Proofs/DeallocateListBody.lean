import Proofs.DeallocateListFirst
import Proofs.DeallocateListSecond

/-! The deployed f575 complete two-link unlink body. -/
namespace WNear.Proofs.DeallocateListBody
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open DeallocateListState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP firstStore secondStore secondAfter after firstMemory secondMemory readI32 writeI32

/-- Both nonzero-link branches are executed from original native heap data;
all three writes and the final reread have their actual sequential semantics. -/
theorem wp_body (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (post : Post) (hr : Ready s frame p)
    (hc : s.host.gas.Credits (61 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits stack
      (finalFrame frame p) callers code)) rest post) :
    WP cfg (fuel + 65) (.next (atCode s limits stack frame callers
      (WNear.Binary.DeallocateList.unlinkBody ++ code))) (61 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have spec := memory_specs p hr.wf hr.firstBound hr.secondBound
  have hp : (finalFrame frame p).locals[0]? = some (.i32 p.pointer) := by
    simpa [finalFrame, secondFrame, firstFrame, DeallocateListGuards.headerFrame, DeallocateListGuards.selectedFrame,
      Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 1 ≠ 0),
      Array.getElem?_setIfInBounds_ne (by decide : 2 ≠ 0)] using hr.pointer
  have hl : (finalFrame frame p).locals[1]? = some (.i32 (finalRaw p)) := by
    have hn : 1 < (secondFrame frame p).locals.size := by
      simpa only [secondFrame, firstFrame, DeallocateListGuards.headerFrame, DeallocateListGuards.selectedFrame,
        Array.size_set!] using (show 1 < frame.locals.size by have h := hr.locals; omega)
    simpa only [finalFrame, Array.set!_eq_setIfInBounds] using (Array.getElem?_setIfInBounds_self_of_lt (xs := (secondFrame frame p).locals) (a := Value.i32 (finalRaw p)) hn)
  have hm : (secondAfter s op p).modules[(finalFrame frame p).inst]? = some p.mi := by
    rw [(secondAfter_fields s op p).2.1]
    simpa only [finalFrame, secondFrame, firstFrame, DeallocateListGuards.headerFrame, DeallocateListGuards.selectedFrame] using hr.module
  have clear := DeallocateListClear.wp_clear cfg fuel rest (secondAfter s op p) limits stack (finalFrame frame p) callers code
    p.pointer (finalRaw p) p.mi p.memoryIndex (secondMemory p) post hp hl hm hr.memoryIndex
    (secondAfter_memory s op p hr.memory) spec.2.2.1 (by rw [spec.2.2.2]; exact hr.nodeBound)
    ((secondAfter_gas s op (11 * op + rest) p (hc.mono (by dsimp [op]; omega))).2.2)
    (by simpa only [after, op] using hnext)
  have second := DeallocateListSecond.wp_second cfg (fuel + 11) (11 * op + rest) s limits stack frame callers
    (WNear.Binary.DeallocateList.clear ++ code) p post hr (hc.mono (by dsimp [op]; omega)) clear
  have first := DeallocateListFirst.wp_first cfg (fuel + 35) (33 * op + rest) s limits stack frame callers
    (.block .empty WNear.Binary.DeallocateList.next :: WNear.Binary.DeallocateList.clear ++ code) p post hr
    (hc.mono (by dsimp [op]; omega)) ((first_gas s op (33 * op + rest) p (hc.mono (by dsimp [op]; omega))).2.2)
    (by
      have ge : 22 * cfg.regularOpCost + (11 * op + rest) = 33 * op + rest := by dsimp [op]; omega
      rw [ge] at second
      simpa only [List.cons_append, Nat.add_assoc, Nat.reduceAdd] using second)
  have ge : 28 * cfg.regularOpCost + (33 * op + rest) = 61 * cfg.regularOpCost + rest := by dsimp [op]; omega
  rw [ge] at first
  simpa only [WNear.Binary.DeallocateList.unlinkBody, List.cons_append, List.nil_append,
    Nat.add_assoc, Nat.reduceAdd] using first

end WNear.Proofs.DeallocateListBody
