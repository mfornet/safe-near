import Proofs.StateDecodeBorshReadPhases
import Proofs.StateDecodeBorshWrapperArguments

/-! Literal161 argument cells, retaining arbitrary operand prefixes and frames. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem paid_plus (s:Store NearState) (op a b:Nat):paid (paid s op a) op b=paid s op (a+b):=by
  induction b with
  |zero=>rfl
  |succ b ih=>
    change chargedStore (paid (paid s op a) op b) op=chargedStore (paid s op (a+b)) op
    rw[ih]

def pairArgumentsCode (slotA slotB:Nat) (da db:UInt32):Expr:=
  [.local_get slotA,.i32_const da,.i32_binop .add,.local_get slotB,.i32_const db,.i32_binop .add]

theorem wp_pair_arguments (cfg:WasmConfig) (fuel rest:Nat) (s:Store NearState) (limits:ExecLimits)
    (stack:Array Value) (frame:CallFrame) (callers:List CallFrame) (code:Expr)
    (slotA slotB:Nat) (a b da db:UInt32) (post:Post)
    (ha:frame.locals[slotA]?=some (.i32 a)) (hb:frame.locals[slotB]?=some (.i32 b))
    (hc:s.host.gas.Credits (6*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 6) limits
      ((stack.push (.i32 (a+da))).push (.i32 (b+db))) frame callers code)) rest post):
    WP cfg (fuel+6) (.next (atCode s limits stack frame callers (pairArgumentsCode slotA slotB da db++code)))
      (6*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have second:=StateDecodeBorshWrapper.wp_push_added cfg fuel rest (paid s op 3) limits
    (stack.push (.i32 (a+da))) frame callers code slotB b db post hb
    (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[paid_plus,Nat.reduceAdd,op] using hn)
  have first:=StateDecodeBorshWrapper.wp_push_added cfg (fuel+3) (3*op+rest) s limits stack frame callers
    (.local_get slotB::.i32_const db::.i32_binop .add::code) slotA a da post ha
    (hc.mono (by dsimp[op];omega)) second
  simpa only[pairArgumentsCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 3*cfg.regularOpCost+(3*op+rest)=6*cfg.regularOpCost+rest by dsimp[op];omega]using first

theorem wp_copy_arguments (cfg:WasmConfig) (fuel rest:Nat) (s:Store NearState) (limits:ExecLimits)
    (stack:Array Value) (frame:CallFrame) (callers:List CallFrame) (code:Expr)
    (slotA slotB:Nat) (a b da db count:UInt32) (post:Post)
    (ha:frame.locals[slotA]?=some (.i32 a)) (hb:frame.locals[slotB]?=some (.i32 b))
    (hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 7) limits
      (((stack.push (.i32 (a+da))).push (.i32 (b+db))).push (.i32 count)) frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers
      (pairArgumentsCode slotA slotB da db++[.i32_const count]++code)))
      (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have c:=wp_i32_const cfg fuel rest (paid s op 6) limits
    ((stack.push (.i32 (a+da))).push (.i32 (b+db))) frame callers code count post
    (paid_credits s op 6 _ (hc.mono (by dsimp[op];omega))) hn
  have pair:=wp_pair_arguments cfg (fuel+1) (op+rest) s limits stack frame callers (.i32_const count::code)
    slotA slotB a b da db post ha hb (hc.mono (by dsimp[op];omega)) c
  simpa only[List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.reduceAdd,
    show 6*cfg.regularOpCost+(op+rest)=7*cfg.regularOpCost+rest by dsimp[op];omega]using pair
end WNear.Proofs.StateDecodeBorshRead
