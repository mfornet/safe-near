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

end WNear.Proofs.InterfaceLazyFinish
