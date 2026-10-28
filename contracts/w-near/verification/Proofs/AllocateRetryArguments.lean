import Proofs.AllocateRetryState
import Binary.AllocateRetry
import Proofs.AllocatePositiveArguments
import NearVM.MeteredLoopRules

/-! Actual scalar argument and miss branches of the growth retry. -/
namespace WNear.Proofs.AllocateRetry
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

/-- Four real argument instructions preceding577. -/
theorem wp_growth_arguments (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (record words : UInt32) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 record)) (h4 : frame.locals[4]?=some (.i32 words))
    (h2 : frame.locals[2]?=some (.i32 1)) (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((((stack.push (.i32 record)).push (.i32 1057464)).push (.i32 words)).push (.i32 1)) frame callers code)) rest post) :
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.AllocateRetry.growthArguments++code)))
      (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  rw [show 4*cfg.regularOpCost+rest=cfg.regularOpCost+(3*op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+3) _ s limits stack frame callers _ 3 (.i32 record) post h3 (hc.mono (by dsimp [op];omega))
  rw [show 3*op+rest=cfg.regularOpCost+(2*op+rest) by dsimp [op];omega]
  apply wp_i32_const cfg (fuel+2) _ (paid s op 1) limits _ frame callers _ 1057464 post
  · exact paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))
  rw [show 2*op+rest=cfg.regularOpCost+(op+rest) by dsimp [op];omega]
  apply wp_local_get cfg (fuel+1) _ (paid s op 2) limits _ frame callers _ 4 (.i32 words) post h4
  · exact paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))
  apply wp_local_get cfg fuel rest (paid s op 3) limits _ frame callers code 2 (.i32 1) post h2
  · exact paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))
  · exact hnext

/-- A failed first search returns zero, stores it, and takes the actual fallthrough. -/
theorem wp_first_miss (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (post : Post) (hc : s.host.gas.Credits (2*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 2) limits stack (missedFrame frame) callers code)) rest post) :
    WP cfg (fuel+2) (.next (atCode s limits (stack.push (.i32 0)) frame callers (.local_tee 1::.br_if 0::code)))
      (2*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have branch := wp_br_if_zero cfg fuel rest (paid s op 1) limits stack (missedFrame frame) callers code 0 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) hnext
  have tee := wp_local_tee cfg (fuel+1) (op+rest) s limits stack frame callers (.br_if 0::code) 1 (.i32 0) post
    (hc.mono (by dsimp [op];omega)) branch
  have cost : cfg.regularOpCost+(op+rest)=2*cfg.regularOpCost+rest := by dsimp [op];omega
  simpa only [cost,Nat.add_assoc,Nat.reduceAdd] using tee
end WNear.Proofs.AllocateRetry
