import Proofs.StateDecodeBorshWrapperControl
import Proofs.InterfaceStack
import NearVM.MeteredSelectionRules

/-! Actual162 accepts through br1, writes the cached zero tag and restores96
shadow-stack bytes. Source/output aliases do not affect its local snapshots. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem modules_store(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl
private theorem globals_store(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl

def finishStore(s:Store NearState)(op index gi:Nat)(memory:Memory)(out r:UInt32):=
  setGlobal (paid (storeI32 (paid s op 3) index out.toNat memory 0) op 4) gi (.i32 (r+96))

theorem wp_finish(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out r:UInt32)
    (mi:ModuleInst)(index gi:Nat)(global:GlobalInst)(memory:Memory)(post:Post)
    (h0:frame.locals[0]?=some (.i32 out))(h1:frame.locals[1]?=some (.i32 0))(h2:frame.locals[2]?=some (.i32 r))
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)(he:s.mems[index]?=some memory)
    (hgi:mi.globalAddrs[0]?=some gi)(hg:s.globals[gi]?=some global)(hb:out.toNat+4≤memory.byteSize)
    (hc:s.host.gas.Credits (7*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (finishStore s cfg.regularOpCost index gi memory out r) limits stack frame callers code)) rest post):
    WP cfg (fuel+7) (.next (atCode s limits stack frame callers (finishCode++code))) (7*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let t:=storeI32 (paid s op 3) index out.toNat memory 0
  have tc:t.host.gas.Credits (4*op+rest):=by
    simpa only[t,storeI32_host] using paid_credits s op 3 (4*op+rest) (hc.mono (by dsimp[op];omega))
  have restore:=InterfaceStack.wp_restore cfg fuel rest t limits stack frame callers code mi gi global r 2 96 post h2
    (by rw[modules_store,modules_paid];exact hm) hgi (by rw[globals_store,globals_paid];exact hg) tc hn
  let suffix:Expr:=[.local_get 2,.i32_const 96,.i32_binop .add,.global_set 0]++code
  have store:=wp_i32_store cfg (fuel+4) (4*op+rest) (paid s op 2) limits stack frame callers suffix {align:=2,offset:=0} out 0 mi index memory post
    (by rw[modules_paid];exact hm) hi (by rw[mems_paid];exact he) (by simpa only[Nat.add_zero] using hb)
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) restore
  have tag:=wp_local_get cfg (fuel+5) (op+(4*op+rest)) (paid s op 1) limits (stack.push (.i32 out)) frame callers
    (.store .i32 none {align:=2,offset:=0}::suffix) 1 (.i32 0) post h1 (paid_credits s op 1 _ (hc.mono (by dsimp[op];omega))) store
  have get:=wp_local_get cfg (fuel+6) (op+(op+(4*op+rest))) s limits stack frame callers
    (.local_get 1::.store .i32 none {align:=2,offset:=0}::suffix) 0 (.i32 out) post h0 (hc.mono (by dsimp[op];omega)) tag
  simpa only[finishCode,suffix,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(op+(op+(4*op+rest)))=7*cfg.regularOpCost+rest by dsimp[op];omega] using get

theorem wp_accept_exit(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code inner discarded:Expr)(post:Post)
    (hc:s.host.gas.Credits (3*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (paid s cfg.regularOpCost 3) limits stack (flagFrame frame 0) callers code)) rest post):
    WP cfg (fuel+3) (.next (atCode s limits stack
      (emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size inner) callers
      (.i32_const 0::.local_set 1::.br 1::discarded))) (3*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let n:=emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size inner
  have branch:=wp_br_two_blocks cfg fuel rest (paid s op 2) limits stack (flagFrame frame 0) callers code inner discarded post
    (paid_credits s op 2 _ (hc.mono (by dsimp[op];omega))) hn
  have flags:=wp_flag cfg (fuel+1) (op+rest) s limits stack n callers (.br 1::discarded) 0 post
    (hc.mono (by dsimp[op];omega))
    (by simpa only[flagFrame,n,emptyBlockFrame,paid,op] using branch)
  simpa only[n,Nat.add_assoc,Nat.reduceAdd,
    show 2*cfg.regularOpCost+(op+rest)=3*cfg.regularOpCost+rest by dsimp[op];omega] using flags
end WNear.Proofs.StateDecodeBorshWrapper
