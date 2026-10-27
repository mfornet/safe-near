import Binary.Deallocate
import Proofs.StorePairCaller
import NearVM.MeteredLoopRules
import NearVM.MeteredNumericRules

/-! Real argument and nonzero-guard instructions of the deployed deallocator. -/
namespace WNear.Proofs.Deallocate
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode

/-- f237 pushes the fixed allocator cell and its three original arguments. -/
theorem wp_entry_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer length align : UInt32) (post : Post)
    (hp : frame.locals[0]? = some (.i32 pointer)) (hl : frame.locals[1]? = some (.i32 length))
    (ha : frame.locals[2]? = some (.i32 align))
    (hc : s.host.gas.Credits (4 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((((stack.push (.i32 1074896)).push (.i32 pointer)).push (.i32 length)).push (.i32 align))
      frame callers code)) rest post) :
    WP cfg (fuel + 4) (.next (atCode s limits stack frame callers
      ([.i32_const 1074896,.local_get 0,.local_get 1,.local_get 2] ++ code)))
      (4 * cfg.regularOpCost + rest) post := by
  rw [show 4 * cfg.regularOpCost + rest = cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  apply wp_i32_const cfg (fuel + 3) _ s limits stack frame callers _ 1074896 post (hc.mono (by omega))
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s cfg.regularOpCost 1) limits _ frame callers _ 0 (.i32 pointer) post hp
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 1) _ (paid s cfg.regularOpCost 2) limits _ frame callers _ 1 (.i32 length) post hl
  · exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  apply wp_local_get cfg fuel rest (paid s cfg.regularOpCost 3) limits _ frame callers code 2 (.i32 align) post ha
  · exact paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega))
  · exact hnext

/-- The actual zero test falls through when the original local is nonzero. -/
theorem wp_nonzero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (slot depth : Nat) (value : UInt32) (post : Post)
    (hl : frame.locals[slot]? = some (.i32 value)) (hnz : value ≠ 0)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits stack frame callers
      ([.local_get slot,.i32_eqz,.br_if depth] ++ code))) (3 * cfg.regularOpCost + rest) post := by
  have hbool : Numeric.bool (value == 0) = 0 := by simp [Numeric.bool,hnz]
  rw [show 3 * cfg.regularOpCost + rest = cfg.regularOpCost + (2 * cfg.regularOpCost + rest) by omega]
  apply wp_local_get cfg (fuel + 2) _ s limits stack frame callers _ slot (.i32 value) post hl (hc.mono (by omega))
  rw [show 2 * cfg.regularOpCost + rest = cfg.regularOpCost + (cfg.regularOpCost + rest) by omega]
  apply wp_i32_eqz cfg (fuel + 1) _ (paid s cfg.regularOpCost 1) limits stack frame callers _ value post
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  rw [hbool]
  have r := wp_br_if_zero cfg fuel rest (paid s cfg.regularOpCost 2) limits stack frame callers code depth post
    (paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))) hnext
  simpa only [paid,List.append_eq,List.cons_append,List.nil_append] using r

/-- The two actual f582 entry guards reject neither nonzero pointer nor length. -/
theorem wp_core_guards (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (pointer length : UInt32) (post : Post)
    (hp : frame.locals[1]? = some (.i32 pointer)) (hl : frame.locals[2]? = some (.i32 length))
    (hnp : pointer ≠ 0) (hnl : length ≠ 0)
    (hc : s.host.gas.Credits (6 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 6) (.next (atCode s limits stack frame callers (WNear.Binary.Deallocate.guard ++ code)))
      (6 * cfg.regularOpCost + rest) post := by
  rw [show 6 * cfg.regularOpCost + rest = 3 * cfg.regularOpCost + (3 * cfg.regularOpCost + rest) by omega]
  have next := wp_nonzero cfg fuel rest (paid s cfg.regularOpCost 3) limits stack frame callers code 2 0 length post hl hnl
    (paid_credits s cfg.regularOpCost 3 _ (hc.mono (by omega)))
  have hn : WP cfg fuel (.next (atCode (paid (paid s cfg.regularOpCost 3) cfg.regularOpCost 3)
      limits stack frame callers code)) rest post := by simpa only [paid] using hnext
  have r := wp_nonzero cfg (fuel + 3) (3 * cfg.regularOpCost + rest) s limits stack frame callers
    ([.local_get 2,.i32_eqz,.br_if 0] ++ code) 1 0 pointer post hp hnp (hc.mono (by omega)) (next hn)
  simpa only [WNear.Binary.Deallocate.guard,List.append_eq,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd] using r

end WNear.Proofs.Deallocate
