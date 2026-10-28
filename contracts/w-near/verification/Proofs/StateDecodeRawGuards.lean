import Binary.StateDecodeRaw
import Proofs.StorePairCallerState
import NearVM.MeteredNumericRules
import NearVM.MeteredControlRules
import NearVM.MeteredLoopRules

/-! Actual f770 guards: a positive length continues and flag zero skips the
zeroing call. Neither guard reads guest memory. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

theorem wp_nonzero_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (size : UInt32) (post : Post)
    (h1 : frame.locals[1]?=some (.i32 size)) (hn : size≠0)
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeRaw.nonzeroGuard++code)))
      (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  have zero : Numeric.bool (size==0)=0 := by simp[Numeric.bool,hn]
  have branch:=wp_br_if_zero cfg fuel rest (paid s op 2) limits stack frame callers code 0 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using hnext)
  have test:=wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 1) limits stack frame callers (.br_if 0::code) size post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) (by simpa only[zero,paid,op] using branch)
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers (.i32_eqz::.br_if 0::code) 1 (.i32 size) post h1
    (hc.mono (by dsimp[op];omega)) test
  simpa only[WNear.Binary.StateDecodeRaw.nonzeroGuard,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get

theorem wp_record_flag_zero (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code discarded : Expr) (post : Post)
    (h3 : frame.locals[3]?=some (.i32 0))
    (hc : s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack frame callers code)) rest post) :
    WP cfg (fuel+3) (.next (atCode s limits stack (emptyBlockFrame frame stack.size code) callers
      (WNear.Binary.StateDecodeRaw.recordFlagGuard++discarded))) (3*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let f:=emptyBlockFrame frame stack.size code
  have branch:=wp_br_if_block_nonzero cfg fuel rest (paid s op 2) limits stack frame callers code discarded 1 post (by decide)
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) (by simpa only[paid,op] using hnext)
  have test:=wp_i32_eqz cfg (fuel+1) (op+rest) (paid s op 1) limits stack f callers (.br_if 0::discarded) 0 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[Numeric.bool,beq_self_eq_true,ite_true,paid,op,f] using branch)
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack f callers (.i32_eqz::.br_if 0::discarded) 3 (.i32 0) post h3
    (hc.mono (by dsimp[op];omega)) test
  simpa only[WNear.Binary.StateDecodeRaw.recordFlagGuard,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,f,
    show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeRaw
