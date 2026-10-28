import Proofs.StateDecodePrefixOutputResult
import Proofs.InterfaceStack

/-! Real316 output branch3 exits all four labels, then restores64 stack bytes.
The concrete final frame retains its cached remainder descriptor. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
attribute [local irreducible] WP atCode Output.after

def exitAfter (s:Store NearState)(op index:Nat)(p:Output.Layout):=
  setGlobal (paid (Output.after s op p) op 4) index (.i32 (p.scratch+64))

theorem wp_exit (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (stack:Array Value)(frame:CallFrame)(callers:List CallFrame)(code outerRest middleRest innerRest discarded:Expr)
    (p:Output.Layout)(mi:ModuleInst)(globalIndex:Nat)(global:GlobalInst)(post:Post)
    (hn:Output.Native p)(h0:frame.locals[0]?=some (.i32 p.out))(h1:frame.locals[1]?=some (.i32 p.slice))
    (h2:frame.locals[2]?=some (.i32 p.scratch))(hs:5≤frame.locals.size)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some p.index)(he:s.mems[p.index]?=some p.memory)
    (hg:mi.globalAddrs[0]?=some globalIndex)(hglobal:s.globals[globalIndex]?=some global)
    (hc:s.host.gas.Credits (24*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (exitAfter s cfg.regularOpCost globalIndex p) limits stack (Output.cachedFrame frame p) callers code)) rest post):
    WP cfg (fuel+24) (.next (atCode s limits stack
      (Output.nested frame stack.size (WNear.Binary.StateDecodePrefix.restore++code) outerRest middleRest innerRest)
      callers (WNear.Binary.StateDecodePrefix.output++discarded))) (24*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have fields:=Output.after_fields s op p
  have restore:=InterfaceStack.wp_restore cfg fuel rest (Output.after s op p) limits stack (Output.cachedFrame frame p) callers code mi globalIndex global p.scratch 2 64 post
    (by simpa[Output.cachedFrame,StateDecodeScalar.loaded64Frame] using h2)
    (by change (Output.after s op p).modules[frame.inst]?=some mi;rw[fields.2.1];exact hm) hg
    (by rw[fields.2.2.2];exact hglobal)
    (Output.after_credits s op (4*op+rest) p (hc.mono (by dsimp[op];omega))) hnext
  have output:=Output.wp_output cfg (fuel+4) (4*op+rest) s limits stack frame callers
    (WNear.Binary.StateDecodePrefix.restore++code) outerRest middleRest innerRest discarded p mi post hn h0 h1 h2 hs hm hi he
    (hc.mono (by dsimp[op];omega))
    (by simpa only[WNear.Binary.StateDecodePrefix.restore] using restore)
  simpa only[Nat.add_assoc,Nat.reduceAdd,
    show 20*cfg.regularOpCost+(4*op+rest)=24*cfg.regularOpCost+rest by dsimp[op];omega] using output
end WNear.Proofs.StateDecodePrefix
