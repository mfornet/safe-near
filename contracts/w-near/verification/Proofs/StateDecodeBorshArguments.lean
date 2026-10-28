import Binary.StateDecodeBorsh
import Proofs.StorePairCallerState
import NearVM.MeteredScalarRules

/-! Actual425 reuses the same four instructions for all three decoder calls. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

theorem arguments_exact : WNear.Binary.StateDecodeBorsh.prefixArguments=WNear.Binary.StateDecodeBorsh.scalarArguments:=rfl

theorem wp_arguments (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(scratch slice:UInt32)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(h1:frame.locals[1]?=some (.i32 slice))
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits ((stack.push (.i32 (scratch+56))).push (.i32 slice)) frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.scalarArguments++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have get1:=wp_local_get cfg fuel rest (paid s op 3) limits (stack.push (.i32 (scratch+56))) frame callers code 1 (.i32 slice) post h1
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hn
  have add:=wp_i32_add cfg (fuel+1) (op+rest) (paid s op 2) limits stack frame callers (.local_get 1::code) scratch 56 post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) get1
  have con:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 1) limits (stack.push (.i32 scratch)) frame callers (.i32_binop .add::.local_get 1::code) 56 post
    (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get2:=wp_local_get cfg (fuel+3) (op+(op+(op+rest))) s limits stack frame callers (.i32_const 56::.i32_binop .add::.local_get 1::code) 2 (.i32 scratch) post h2 (hc.mono (by dsimp[op];omega)) con
  simpa only[WNear.Binary.StateDecodeBorsh.scalarArguments,List.cons_append,List.nil_append,
    show cfg.regularOpCost+(op+(op+(op+rest)))=4*cfg.regularOpCost+rest by dsimp[op];omega] using get2
end WNear.Proofs.StateDecodeBorsh
