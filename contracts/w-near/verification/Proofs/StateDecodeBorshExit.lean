import Binary.StateDecodeBorsh
import Proofs.StateDecodePrefixBranch
import Proofs.InterfaceStack

/-! Actual425 reserves96 shadow-stack bytes. Its accepted branch skips all
four labels before restoring96; neither operation reads scratch memory. -/
namespace WNear.Proofs.StateDecodeBorsh
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
private theorem modules_paid(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def setupStore(s:Store NearState)(op index:Nat)(sp:UInt32):=setGlobal (paid s op 5) index (.i32 (sp-96))
def setupResultFrame(frame:CallFrame)(sp:UInt32):={frame with locals:=frame.locals.set! 2 (.i32 (sp-96))}

theorem wp_setup (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)
    (mi:ModuleInst)(index:Nat)(global:GlobalInst)(sp:UInt32)(post:Post)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.globalAddrs[0]?=some index)
    (hg:s.globals[index]?=some global)(hv:global.value=.i32 sp)
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (setupStore s cfg.regularOpCost index sp) limits stack
      (setupResultFrame frame sp) callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack frame callers (WNear.Binary.StateDecodeBorsh.setup++code)))
      (5*cfg.regularOpCost+rest) post:=by
  exact InterfaceStack.wp_reserve cfg fuel rest s limits stack frame callers code mi index global sp 2 96 post hm hi hg hv hc hn

def exitStore(s:Store NearState)(op index:Nat)(scratch:UInt32):=
  setGlobal (paid (chargedStore s op) op 4) index (.i32 (scratch+96))
def exitNested(frame:CallFrame)(height:Nat)(code outer middle inner:Expr):=
  emptyBlockFrame (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame frame height
    (WNear.Binary.StateDecodeBorsh.restore++code)) height outer) height middle) height inner

theorem wp_exit (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code outer middle inner discarded:Expr)
    (mi:ModuleInst)(index:Nat)(global:GlobalInst)(scratch:UInt32)(post:Post)
    (h2:frame.locals[2]?=some (.i32 scratch))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.globalAddrs[0]?=some index)(hg:s.globals[index]?=some global)
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (exitStore s cfg.regularOpCost index scratch) limits stack frame callers code)) rest post):
    WP cfg (fuel+5) (.next (atCode s limits stack (exitNested frame stack.size code outer middle inner) callers
      (.br 3::discarded))) (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have credits:(chargedStore s op).host.gas.Credits (4*op+rest):=by
    simpa only[paid] using paid_credits s op 1 (4*op+rest) (hc.mono (by dsimp[op];omega))
  have restore:=InterfaceStack.wp_restore cfg fuel rest (chargedStore s op) limits stack frame callers code mi index global scratch 2 96 post h2
    (by change (paid s op 1).modules[frame.inst]?=some mi;rw[modules_paid];exact hm) hi
    (by change (paid s op 1).globals[index]?=some global;rw[globals_paid];exact hg) credits hn
  have branch:=wp_br_four_blocks cfg (fuel+4) (4*op+rest) s limits stack frame callers
    (WNear.Binary.StateDecodeBorsh.restore++code) outer middle inner discarded post (hc.mono (by dsimp[op];omega)) restore
  simpa only[exitNested,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(4*op+rest)=5*cfg.regularOpCost+rest by dsimp[op];omega] using branch
end WNear.Proofs.StateDecodeBorsh
