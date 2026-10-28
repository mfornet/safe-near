import Proofs.StateDecodeBorshWrapperCode
import NearVM.MeteredScalarRules

/-! Actual162 argument preparation preserves every operand prefix and caller
frame. The first copy uses nested added source(R+48)+12 literally. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem paid_plus(s:Store NearState)(op a b:Nat):paid (paid s op a) op b=paid s op (a+b):=by
  induction b with
  |zero=>rfl
  |succ b ih=>
    change chargedStore (paid (paid s op a) op b) op=chargedStore (paid s op (a+b)) op
    rw[ih]

theorem wp_push_added(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(slot:Nat)(pointer delta:UInt32)(post:Post)
    (hp:frame.locals[slot]?=some (.i32 pointer))(hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits (stack.push (.i32 (pointer+delta))) frame callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get slot::.i32_const delta::.i32_binop .add::code))) (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have add:=wp_i32_add cfg fuel rest (paid s op 2) limits stack frame callers code pointer delta post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have con:=wp_i32_const cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 pointer)) frame callers
    (.i32_binop .add::code) delta post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) add
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers (.i32_const delta::.i32_binop .add::code)
    slot (.i32 pointer) post hp (hc.mono (by dsimp[op];omega)) con
  simpa only[Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get

theorem wp_child_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r slice:UInt32)(post:Post)
    (h2:frame.locals[2]?=some (.i32 r))(h1:frame.locals[1]?=some (.i32 slice))
    (hc:s.host.gas.Credits (4*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 4) limits
      ((stack.push (.i32 (r+48))).push (.i32 slice)) frame callers code)) rest post):
    WP cfg (fuel+4) (.next (atCode s limits stack frame callers (argumentsCode++code))) (4*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have get:=wp_local_get cfg fuel rest (paid s op 3) limits (stack.push (.i32 (r+48))) frame callers code 1 (.i32 slice) post h1
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hn
  have add:=wp_push_added cfg (fuel+1) (op+rest) s limits stack frame callers (.local_get 1::code) 2 r 48 post h2
    (hc.mono (by dsimp[op];omega)) get
  simpa only[argumentsCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(op+rest)=4*cfg.regularOpCost+rest by dsimp[op];omega] using add

theorem wp_second_copy_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out r:UInt32)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h2:frame.locals[2]?=some (.i32 r))
    (hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 (out+12))).push (.i32 (r+12))).push (.i32 36)) frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (secondCopyCode++code))) (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have c:=wp_i32_const cfg fuel rest (paid s op 6) limits ((stack.push (.i32 (out+12))).push (.i32 (r+12))) frame callers code 36 post
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) hn
  have source:=wp_push_added cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (out+12))) frame callers (.i32_const 36::code) 2 r 12 post h2
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[paid_plus,Nat.reduceAdd,op] using c)
  have dest:=wp_push_added cfg (fuel+4) (4*op+rest) s limits stack frame callers
    (.local_get 2::.i32_const 12::.i32_binop .add::.i32_const 36::code) 0 out 12 post h0
    (hc.mono (by dsimp[op];omega))
    (by simpa only[Nat.add_assoc,Nat.reduceAdd,show 3*cfg.regularOpCost+(op+rest)=4*op+rest by dsimp[op];omega] using source)
  simpa only[secondCopyCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(4*op+rest)=7*cfg.regularOpCost+rest by dsimp[op];omega] using dest

theorem wp_first_copy_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)(post:Post)
    (h2:frame.locals[2]?=some (.i32 r))(hc:s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      (((stack.push (.i32 (r+12))).push (.i32 ((r+48)+12))).push (.i32 36)) frame callers code)) rest post):
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers (firstCopyCode++code))) (9*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have c36:=wp_i32_const cfg fuel rest (paid s op 8) limits ((stack.push (.i32 (r+12))).push (.i32 ((r+48)+12))) frame callers code 36 post
    (paid_credits s op 8 _ (hc.mono (by dsimp[op];omega))) hn
  have add:=wp_i32_add cfg (fuel+1) (op+rest) (paid s op 7) limits (stack.push (.i32 (r+12))) frame callers (.i32_const 36::code) (r+48) 12 post
    (paid_credits s op 7 _ (hc.mono (by dsimp[op];omega))) c36
  have c12:=wp_i32_const cfg (fuel+2) (op+(op+rest)) (paid s op 6) limits ((stack.push (.i32 (r+12))).push (.i32 (r+48))) frame callers
    (.i32_binop .add::.i32_const 36::code) 12 post (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) add
  have source:=wp_push_added cfg (fuel+3) (3*op+rest) (paid s op 3) limits (stack.push (.i32 (r+12))) frame callers
    (.i32_const 12::.i32_binop .add::.i32_const 36::code) 2 r 48 post h2
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[paid_plus,Nat.add_assoc,Nat.reduceAdd,op,show cfg.regularOpCost+(cfg.regularOpCost+rest)=2*cfg.regularOpCost+rest by omega,show cfg.regularOpCost+(2*cfg.regularOpCost+rest)=3*cfg.regularOpCost+rest by omega] using c12)
  have dest:=wp_push_added cfg (fuel+6) (6*op+rest) s limits stack frame callers
    (.local_get 2::.i32_const 48::.i32_binop .add::.i32_const 12::.i32_binop .add::.i32_const 36::code) 2 r 12 post h2
    (hc.mono (by dsimp[op];omega))
    (by simpa only[Nat.add_assoc,Nat.reduceAdd,show 3*cfg.regularOpCost+(3*op+rest)=6*op+rest by dsimp[op];omega] using source)
  simpa only[firstCopyCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(6*op+rest)=9*cfg.regularOpCost+rest by dsimp[op];omega] using dest
end WNear.Proofs.StateDecodeBorshWrapper
