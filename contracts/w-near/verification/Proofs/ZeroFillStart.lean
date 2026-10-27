import Proofs.ZeroFillLoop
import NearVM.MeteredNumericRules

/-! Actual f952 guard paths and positive-loop pointer initialization. -/
namespace WNear.Proofs.ZeroFill
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def startFrame (frame : CallFrame) (ptr : UInt32) := {frame with locals:=frame.locals.set! 3 (.i32 ptr)}

/-- Nonzero count: the real guard falls through and local3 receives the pointer. -/
theorem wp_start_positive (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr count : UInt32) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 ptr)) (h2 : frame.locals[2]? = some (.i32 count)) (hn : count≠0)
    (hc : s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits stack (startFrame frame ptr) callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers ([.local_get 2,.i32_eqz,.br_if 0,.local_get 0,.local_set 3]++code)))
      (5*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  have sn : WP cfg fuel (.next (atCode (chargedStore (paid s op 4) cfg.regularOpCost) limits stack
      {frame with locals:=frame.locals.set! 3 (.i32 ptr)} callers code)) rest post := by simpa only [startFrame,paid,op] using hnext
  have set := wp_local_set cfg fuel rest (paid s op 4) limits stack frame callers code 3 (.i32 ptr) post (paid_credits s op 4 _ (hc.mono (by dsimp [op];omega))) sn
  have get := wp_local_get cfg (fuel+1) (op+rest) (paid s op 3) limits stack frame callers (.local_set 3::code) 0 (.i32 ptr) post h0
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) (by simpa only [paid,op] using set)
  have branch := wp_br_if_zero cfg (fuel+2) (op+(op+rest)) (paid s op 2) limits stack frame callers (.local_get 0::.local_set 3::code) 0 post
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) (by simpa only [paid,op] using get)
  have eqNext : WP cfg (fuel+3) (.next (atCode (chargedStore (paid s op 1) cfg.regularOpCost) limits (stack.push (.i32 (Numeric.bool (count==0))))
      frame callers (.br_if 0::.local_get 0::.local_set 3::code))) (op+(op+(op+rest))) post := by
    simpa only [show (count==0)=false from by simp [hn],Numeric.bool,Bool.false_eq_true,ite_false,paid,op] using branch
  have eq := wp_i32_eqz cfg (fuel+3) (op+(op+(op+rest))) (paid s op 1) limits stack frame callers (.br_if 0::.local_get 0::.local_set 3::code) count post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) eqNext
  have first := wp_local_get cfg (fuel+4) (op+(op+(op+(op+rest)))) s limits stack frame callers
    (.i32_eqz::.br_if 0::.local_get 0::.local_set 3::code) 2 (.i32 count) post h2 (hc.mono (by dsimp [op];omega)) (by simpa only [paid,op] using eq)
  simpa only [List.append_eq,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+(op+rest))))=5*cfg.regularOpCost+rest by dsimp [op];omega] using first

/-- Count zero exits the real block directly and returns the original pointer. -/
theorem wp_body_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (ptr : UInt32) (post : Post)
    (h0 : frame.locals[0]? = some (.i32 ptr)) (h2 : frame.locals[2]? = some (.i32 0))
    (hc : s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits (stack.push (.i32 ptr)) frame callers code)) rest post) :
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.ZeroFill.body++code))) (4*cfg.regularOpCost+rest) post := by
  let op := cfg.regularOpCost
  let bf := emptyBlockFrame frame stack.size (.local_get 0::code)
  have last := wp_local_get cfg fuel rest (paid s op 3) limits stack frame callers code 0 (.i32 ptr) post h0
    (paid_credits s op 3 _ (hc.mono (by dsimp [op];omega))) (by simpa only [paid,op] using hnext)
  have branch := wp_br_if_block_nonzero cfg (fuel+1) (op+rest) (paid s op 2) limits stack frame callers
    (.local_get 0::code) [.local_get 0,.local_set 3,.loop .empty WNear.Binary.ZeroFill.loopBody] 1 post (by decide)
    (paid_credits s op 2 _ (hc.mono (by dsimp [op];omega))) (by simpa only [paid,op] using last)
  have eqNext : WP cfg (fuel+2) (.next (atCode (chargedStore (paid s op 1) cfg.regularOpCost) limits (stack.push (.i32 (Numeric.bool ((0:UInt32)==0)))) bf callers
      [.br_if 0,.local_get 0,.local_set 3,.loop .empty WNear.Binary.ZeroFill.loopBody])) (op+(op+rest)) post := by
    simpa only [bf,Numeric.bool,BEq.rfl,ite_true,paid,op] using branch
  have eq := wp_i32_eqz cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits stack bf callers
    [.br_if 0,.local_get 0,.local_set 3,.loop .empty WNear.Binary.ZeroFill.loopBody] 0 post
    (paid_credits s op 1 _ (hc.mono (by dsimp [op];omega))) eqNext
  have first := wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack bf callers
    [.i32_eqz,.br_if 0,.local_get 0,.local_set 3,.loop .empty WNear.Binary.ZeroFill.loopBody] 2 (.i32 0) post h2
    (hc.mono (by dsimp [op];omega)) (by simpa only [paid,op] using eq)
  have headNext : WP cfg (fuel+4) (.next (atCode s limits stack bf callers WNear.Binary.ZeroFill.guarded)) (4*op+rest) post := by
    simpa only [WNear.Binary.ZeroFill.guarded,
      show cfg.regularOpCost+(op+(op+(op+rest)))=4*op+rest by dsimp [op];omega] using first
  have result := wp_block_empty cfg (fuel+4) (4*op+rest) s limits stack frame callers WNear.Binary.ZeroFill.guarded (.local_get 0::code) post hc headNext
  simpa only [WNear.Binary.ZeroFill.body,List.append_eq,List.cons_append,List.nil_append,op] using result
end WNear.Proofs.ZeroFill
