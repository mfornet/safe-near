import Proofs.InterfaceLazyBody

/-! Actual result preparation and old-status-zero branch of lazy f467. -/
namespace WNear.Proofs.InterfaceLazyFinish
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384

/-- The returned pointer uses the deployed wrapping i32 addition. -/
theorem wp_result (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell : UInt32) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits stack
      {frame with locals := frame.locals.set! 0 (.i32 (cell + 4))} callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceLazy.result ++ code))) (4 * cfg.regularOpCost + rest) post := by
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 3) _ s limits stack frame callers _ 0 (.i32 cell) post hcell (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 4 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (1 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_add cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits stack frame callers _ cell 4 post
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  rw [show 1 * cfg.regularOpCost + rest = cfg.regularOpCost + rest by omega]
  apply wp_local_set cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code 0 (.i32 (cell + 4)) post
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  · exact hnext

/-- The actual branch skips destruction only when the saved old status is zero. -/
theorem wp_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (post : Post) (hstatus : frame.locals[1]? = some (.i32 0))
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceLazy.guard ++ code))) (3 * cfg.regularOpCost + rest) post := by
  apply wp_block_empty cfg (fuel + 3) _ s limits stack frame callers _ _ post hc
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack (emptyBlockFrame frame stack.size code) callers _ 1 (.i32 0) post hstatus (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (1 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack (emptyBlockFrame frame stack.size code) callers _ 0 post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 1 * cfg.regularOpCost + rest = cfg.regularOpCost + rest by omega]
  apply wp_br_if_block_nonzero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code
    WNear.Binary.InterfaceLazy.dropOld 1 post (by decide)
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  · exact hnext

/-- Actual final restore48 and pointer return preparation. -/
theorem wp_restore (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (scratch result : UInt32) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (post : Post)
    (hs : frame.locals[2]? = some (.i32 scratch)) (hr : frame.locals[0]? = some (.i32 result))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (paid (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 48))) cfg.regularOpCost 1)
      limits (stack.push (.i32 result)) frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      (WNear.Binary.InterfaceLazy.restore ++ code))) (5 * cfg.regularOpCost + rest) post := by
  have hn := wp_local_get cfg fuel rest
    (setGlobal (paid s cfg.regularOpCost 4) index (.i32 (scratch + 48))) limits stack frame callers code 0 (.i32 result) post hr
    (paid_credits s cfg.regularOpCost 4 _ (hc.mono (by omega))) hnext
  have h := InterfaceStack.wp_restore cfg (fuel + 1) (cfg.regularOpCost + rest) s limits stack frame callers
    (.local_get 0 :: code) mi index global scratch 2 48 post hs hm hi hg
    (hc.mono (by omega)) hn
  have gas : 4 * cfg.regularOpCost + (cfg.regularOpCost + rest) = 5 * cfg.regularOpCost + rest := by omega
  rw [gas] at h
  simpa only [Nat.add_assoc, Nat.reduceAdd, WNear.Binary.InterfaceLazy.restore, List.cons_append, List.nil_append] using h

def finalStore (s : Store NearState) (op index : Nat) (scratch : UInt32) :=
  paid (setGlobal (paid (paid (paid s op 4) op 3) op 4) index (.i32 (scratch + 48))) op 1

/-- Complete actual thirteen-step normal tail: publish cell+4, skip the old
empty state, restore the wrapping shadow stack, and leave the result on stack. -/
theorem wp_finish (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (cell scratch : UInt32) (mi : ModuleInst) (index : Nat)
    (global : GlobalInst) (post : Post)
    (hcell : frame.locals[0]? = some (.i32 cell))
    (hs : frame.locals[2]? = some (.i32 scratch)) (hz : frame.locals[1]? = some (.i32 0))
    (hn : 3 ≤ frame.locals.size)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global)
    (hc : s.host.gas.Credits (12 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore s cfg.regularOpCost index scratch)
      limits (stack.push (.i32 (cell + 4)))
      {frame with locals := frame.locals.set! 0 (.i32 (cell + 4))} callers code)) rest post) :
    WP cfg (fuel + 13) (.next (atCode s limits stack frame callers
      ((WNear.Binary.InterfaceLazy.result ++ WNear.Binary.InterfaceLazy.guard ++
        WNear.Binary.InterfaceLazy.restore) ++ code))) (12 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let updated := {frame with locals := frame.locals.set! 0 (.i32 (cell + 4))}
  let prepared := paid s op 4
  let guarded := paid prepared op 3
  have h0 : 0 < frame.locals.size := by omega
  have hr : updated.locals[0]? = some (.i32 (cell + 4)) := by
    simp only [updated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt h0]
  have hs' : updated.locals[2]? = some (.i32 scratch) := by
    simpa only [updated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 0 ≠ 2)] using hs
  have hz' : updated.locals[1]? = some (.i32 0) := by
    simpa only [updated, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_ne (by decide : 0 ≠ 1)] using hz
  have hm' : guarded.modules[updated.inst]? = some mi := by
    simpa only [guarded, prepared, paid, chargedStore, updated] using hm
  have hg' : guarded.globals[index]? = some global := by
    simpa only [guarded, prepared, paid, chargedStore] using hg
  have cp : prepared.host.gas.Credits (8 * op + rest) := paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  have cg : guarded.host.gas.Credits (5 * op + rest) := paid_credits prepared op 3 _ (cp.mono (by omega))
  have finalNext : WP cfg fuel (.next (atCode
      (paid (setGlobal (paid guarded cfg.regularOpCost 4) index (.i32 (scratch + 48))) cfg.regularOpCost 1)
      limits (stack.push (.i32 (cell + 4))) updated callers code)) rest post := by
    simpa only [finalStore, guarded, prepared, op, updated] using hnext
  have restored := wp_restore cfg fuel rest guarded limits stack updated callers code scratch (cell + 4) mi index global post
    hs' hr hm' hi hg' cg finalNext
  have guardedNext : WP cfg (fuel + 5) (.next (atCode (paid prepared cfg.regularOpCost 3)
      limits stack updated callers (WNear.Binary.InterfaceLazy.restore ++ code))) (5 * cfg.regularOpCost + rest) post := by
    simpa only [guarded, op] using restored
  have guardCredits : prepared.host.gas.Credits (3 * cfg.regularOpCost + (5 * cfg.regularOpCost + rest)) := by
    simpa only [op, show 3 * cfg.regularOpCost + (5 * cfg.regularOpCost + rest) = 8 * cfg.regularOpCost + rest by omega] using cp
  have guardRule := wp_guard cfg (fuel + 5) (5 * cfg.regularOpCost + rest) prepared limits stack updated callers
    (WNear.Binary.InterfaceLazy.restore ++ code) post hz' guardCredits guardedNext
  have resultNext : WP cfg (fuel + 9) (.next (atCode (paid s cfg.regularOpCost 4) limits stack updated callers
      ((WNear.Binary.InterfaceLazy.guard ++ WNear.Binary.InterfaceLazy.restore) ++ code)))
      (8 * cfg.regularOpCost + rest) post := by
    simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_assoc,
      show 3 * cfg.regularOpCost + (5 * cfg.regularOpCost + rest) = 8 * cfg.regularOpCost + rest by omega,
      prepared, op] using guardRule
  have rule := wp_result cfg (fuel + 9) (8 * cfg.regularOpCost + rest) s limits stack frame callers _ cell post hcell
    (hc.mono (by omega)) resultNext
  have gas : 4 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest) = 12 * cfg.regularOpCost + rest := by omega
  rw [gas] at rule
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_assoc] using rule

end WNear.Proofs.InterfaceLazyFinish
