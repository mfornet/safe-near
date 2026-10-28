import Proofs.StateDecodeBorshReadArguments
import NearVM.MeteredBitRules

/-! Literal161 OR-address copy arguments and the success-tag store. The OR is
retained as a wrapping UInt32 operation; alignment is a separate native fact. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem paid_plus(s:Store NearState)(op a b:Nat):paid (paid s op a) op b=paid s op (a+b):=by
  induction b with
  |zero=>rfl
  |succ b ih=>change chargedStore (paid (paid s op a) op b) op=chargedStore (paid s op (a+b)) op;rw[ih]
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_push_or(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(slot:Nat)(r delta mask:UInt32)(post:Post)
    (hr:frame.locals[slot]?=some (.i32 r))(hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 5) limits (stack.push (.i32 ((r+delta)|||mask))) frame callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers
      (.local_get slot::.i32_const delta::.i32_binop .add::.i32_const mask::.i32_binop .or::code)))
      (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have or:=wp_i32_or cfg fuel rest (paid s op 4) limits stack frame callers code (r+delta) mask post
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hn
  have maskStep:=wp_i32_const cfg (fuel+1) (op+rest) (paid s op 3) limits (stack.push (.i32 (r+delta))) frame callers
    (.i32_binop .or::code) mask post (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) or
  have added:=StateDecodeBorshWrapper.wp_push_added cfg (fuel+2) (2*op+rest) s limits stack frame callers
    (.i32_const mask::.i32_binop .or::code) slot r delta post hr (hc.mono (by dsimp[op];omega))
    (by simpa only[Nat.add_assoc,show op+(op+rest)=2*op+rest by omega,op] using maskStep)
  simpa only[Nat.add_assoc,Nat.reduceAdd,show 3*cfg.regularOpCost+(2*op+rest)=5*cfg.regularOpCost+rest by dsimp[op];omega] using added

def orCopyArgumentsCode:Expr:=
  [.local_get 3,.i32_const 16,.i32_binop .add,.i32_const 4,.i32_binop .or,
   .local_get 3,.i32_const 60,.i32_binop .add,.i32_const 36]

theorem wp_or_copy_arguments(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)(post:Post)
    (hr:frame.locals[3]?=some (.i32 r))(hc:s.host.gas.Credits (9*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 9) limits
      (((stack.push (.i32 ((r+16)|||4))).push (.i32 (r+60))).push (.i32 36)) frame callers code)) rest post):
    WP cfg (fuel+9) (.next (atCode s limits stack frame callers (orCopyArgumentsCode++code)))
      (9*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have count:=wp_i32_const cfg fuel rest (paid s op 8) limits
    ((stack.push (.i32 ((r+16)|||4))).push (.i32 (r+60))) frame callers code 36 post
    (paid_credits s op 8 _ (hc.mono (by dsimp[op];omega))) hn
  have source:=StateDecodeBorshWrapper.wp_push_added cfg (fuel+1) (op+rest) (paid s op 5) limits
    (stack.push (.i32 ((r+16)|||4))) frame callers (.i32_const 36::code) 3 r 60 post hr
    (paid_credits s op 5 _ (hc.mono (by dsimp[op];omega)))
    (by simpa only[paid_plus,Nat.reduceAdd,op] using count)
  have dest:=wp_push_or cfg (fuel+4) (4*op+rest) s limits stack frame callers
    (.local_get 3::.i32_const 60::.i32_binop .add::.i32_const 36::code) 3 r 16 4 post hr
    (hc.mono (by dsimp[op];omega))
    (by simpa only[Nat.add_assoc,show 3*cfg.regularOpCost+(op+rest)=4*op+rest by dsimp[op];omega] using source)
  simpa only[orCopyArgumentsCode,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+(4*op+rest)=9*cfg.regularOpCost+rest by dsimp[op];omega] using dest

theorem wp_tag_success(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out:UInt32)
    (mi:ModuleInst)(index:Nat)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)(hb:out.toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (storeI32 (paid s cfg.regularOpCost 3) index out.toNat memory 0) limits stack frame callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack frame callers
      (.local_get 0::.i32_const 0::.store .i32 none {align:=2,offset:=0}::code)))
      (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have store:=wp_i32_store cfg fuel rest (paid s op 2) limits stack frame callers code {align:=2,offset:=0} out 0 mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hb)
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have zero:=wp_i32_const cfg (fuel+1) (op+rest) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=0}::code) 0 post (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) store
  have get:=wp_local_get cfg (fuel+2) (op+(op+rest)) s limits stack frame callers
    (.i32_const 0::.store .i32 none {align:=2,offset:=0}::code) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) zero
  simpa only[Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(op+(op+rest))=3*cfg.regularOpCost+rest by dsimp[op];omega] using get
end WNear.Proofs.StateDecodeBorshRead
