import Proofs.AllocatePositiveState

/-! Actual positive-size branch of581; zero-size code is skipped by br_if. -/
namespace WNear.Proofs.AllocatePositive
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

theorem wp_positive_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (size : UInt32) (post : Post)
    (hl : frame.locals[1]?=some (.i32 size)) (hn : size≠0)
    (hc : s.host.gas.Credits (2*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.AllocatePositive.positiveGuard++code)))
      (2*cfg.regularOpCost+rest) post := by
  apply wp_block_empty cfg (fuel+2) _ s limits stack frame callers _ code post hc
  rw [show 2*cfg.regularOpCost+rest=cfg.regularOpCost+(cfg.regularOpCost+rest) by omega]
  apply wp_local_get cfg (fuel+1) _ s limits stack (emptyBlockFrame frame stack.size code) callers _ 1 (.i32 size) post hl (hc.mono (by omega))
  apply wp_br_if_block_nonzero cfg fuel rest (chargedStore s cfg.regularOpCost) limits stack frame callers code
    WNear.Binary.AllocatePositive.zeroTail size post hn
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  · exact hnext
end WNear.Proofs.AllocatePositive
