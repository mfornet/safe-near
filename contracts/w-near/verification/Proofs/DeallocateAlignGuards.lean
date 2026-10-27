import Binary.DeallocateAlign
import Proofs.StorePairCallerState
import NearVM.MeteredBitRules
import NearVM.MeteredScalarRules
import NearVM.MeteredLoopRules

/-! Actual checked arithmetic guards of deployed ceiling division. -/
namespace WNear.Proofs.DeallocateAlign
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

def addGuard : Expr := [.local_get 0, .local_get 1, .i32_binop .add, .local_tee 2, .local_get 0, .i32_relop .lt_u, .br_if 0]
def subGuard : Expr := [.local_get 2, .i32_const 4294967295, .i32_binop .add, .local_tee 0, .local_get 2, .i32_relop .gt_u, .br_if 1]
def divideTail : Expr := [.local_get 0, .local_get 1, .i32_binop .div_u, .return]
def sumFrame (frame : CallFrame) (sum : UInt32) := {frame with locals := frame.locals.set! 2 (.i32 sum)}
def adjustedFrame (frame : CallFrame) (value : UInt32) := {frame with locals := frame.locals.set! 0 (.i32 value)}

/-- Actual addition, saved sum, unsigned overflow test and untaken branch. -/
theorem wp_add_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (a b : UInt32) (post : Post)
    (ha : frame.locals[0]? = some (.i32 a)) (hb : frame.locals[1]? = some (.i32 b))
    (hcheck : Numeric.irelop32 .lt_u (a + b) a = false)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack (sumFrame frame (a + b)) callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers (addGuard ++ code)))
      (7 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let updated := sumFrame frame (a + b)
  have ha' : updated.locals[0]? = some (.i32 a) := by simpa [updated, sumFrame] using ha
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 6) _ s limits stack frame callers _ 0 (.i32 a) post ha (hc.mono (by dsimp [op]; omega))
  rw [show 6 * op + rest = cfg.regularOpCost + (5 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 5) _ (paid s op 1) limits _ frame callers _ 1 (.i32 b) post hb
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5 * op + rest = cfg.regularOpCost + (4 * op + rest) by dsimp [op]; omega]
  apply wp_i32_add cfg (fuel + 4) _ (paid s op 2) limits stack frame callers _ a b post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4 * op + rest = cfg.regularOpCost + (3 * op + rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel + 3) _ (paid s op 3) limits stack frame callers _ 2 (.i32 (a + b)) post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3 * op + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s op 4) limits (stack.push (.i32 (a + b))) updated callers _ 0 (.i32 a) post ha'
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_relop cfg (fuel + 1) _ (paid s op 5) limits stack updated callers _ .lt_u (a + b) a post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  simp only [hcheck, Numeric.bool]
  apply wp_br_if_zero cfg fuel rest (paid s op 6) limits stack updated callers code 0 post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

/-- Actual subtract-one-by-wrapping-add, saved numerator, unsigned underflow
check and untaken branch. -/
theorem wp_sub_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (sum : UInt32) (post : Post)
    (hs : frame.locals[2]? = some (.i32 sum))
    (hcheck : Numeric.irelop32 .gt_u (sum + 4294967295) sum = false)
    (hc : s.host.gas.Credits (7 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits stack (adjustedFrame frame (sum + 4294967295)) callers code)) rest post) :
    WP cfg (fuel + 7) (.next (atCode s limits stack frame callers (subGuard ++ code)))
      (7 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let adjusted := sum + 4294967295
  let updated := adjustedFrame frame adjusted
  have hs' : updated.locals[2]? = some (.i32 sum) := by simpa [updated, adjustedFrame] using hs
  rw [show 7 * cfg.regularOpCost + rest = cfg.regularOpCost + (6 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 6) _ s limits stack frame callers _ 2 (.i32 sum) post hs (hc.mono (by dsimp [op]; omega))
  rw [show 6 * op + rest = cfg.regularOpCost + (5 * op + rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel + 5) _ (paid s op 1) limits _ frame callers _ 4294967295 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 5 * op + rest = cfg.regularOpCost + (4 * op + rest) by dsimp [op]; omega]
  apply wp_i32_add cfg (fuel + 4) _ (paid s op 2) limits stack frame callers _ sum 4294967295 post
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 4 * op + rest = cfg.regularOpCost + (3 * op + rest) by dsimp [op]; omega]
  apply wp_local_tee cfg (fuel + 3) _ (paid s op 3) limits stack frame callers _ 0 (.i32 adjusted) post
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3 * op + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 2) _ (paid s op 4) limits (stack.push (.i32 adjusted)) updated callers _ 2 (.i32 sum) post hs'
  · exact paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_relop cfg (fuel + 1) _ (paid s op 5) limits stack updated callers _ .gt_u adjusted sum post
  · exact paid_credits s op 5 _ (hc.mono (by dsimp [op]; omega))
  simp only [adjusted, hcheck, Numeric.bool]
  apply wp_br_if_zero cfg fuel rest (paid s op 6) limits stack updated callers code 1 post
  · exact paid_credits s op 6 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext
end WNear.Proofs.DeallocateAlign
