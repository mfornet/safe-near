import Binary.StateReadOuter
import Proofs.InterfaceStack
import Proofs.ValueReturnLazyReturn
import NearVM.MeteredLoopRules

/-! Natural present-block exit, four real SP-restore instructions and explicit
return219: five charged opcodes, six steps, and no normal-leave step. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

def tailAfter(s:Store NearState)(op index:Nat)(r:UInt32):=
  chargedStore (setGlobal (paid s op 4) index (.i32 (r+96))) op

theorem wp_tail(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame caller:CallFrame)(callers:List CallFrame)
    (mi:ModuleInst)(index:Nat)(global:GlobalInst)(r:UInt32)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)
    (hi:mi.globalAddrs[0]?=some index)(hg:s.globals[index]?=some global)
    (ha:frame.arity=0)(hh:frame.height=base.length)
    (hc:s.host.gas.Credits (5*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (tailAfter s cfg.regularOpCost index r) limits
      base.toArray caller callers caller.code)) rest post):
    WP cfg (fuel+6) (.next (atCode s limits base.toArray
      (emptyBlockFrame frame base.length WNear.Binary.StateReadOuter.restoreReturn)
      (caller::callers) [])) (5*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let restored:=setGlobal (paid s op 4) index (.i32 (r+96))
  have credits:restored.host.gas.Credits (op+rest):=
    paid_credits s op 4 (op+rest) (hc.mono (by dsimp[op];omega))
  have returned:=ValueReturnLazyLookup.wp_return_wasm cfg fuel rest restored limits base [] frame caller callers [] post
    (by simpa only[List.length_nil] using ha.symm) hh credits
    (by simpa only[tailAfter,restored,op,List.append_nil] using hnext)
  have next:WP cfg (fuel+1) (.next (atCode restored limits base.toArray frame (caller::callers) [.return]))
      (op+rest) post:=by simpa only[List.append_nil] using returned
  have restore:=InterfaceStack.wp_restore cfg (fuel+1) (op+rest) s limits base.toArray frame (caller::callers)
    [.return] mi index global r 1 96 post h1 hm hi hg
    (hc.mono (by dsimp[op];omega)) next
  have finish:WP cfg (fuel+5) (.next (atCode s limits base.toArray frame (caller::callers)
      WNear.Binary.StateReadOuter.restoreReturn)) (5*cfg.regularOpCost+rest) post:=by
    simpa only[WNear.Binary.StateReadOuter.restore_return,List.cons_append,List.nil_append,
      Nat.add_assoc,Nat.reduceAdd,show 4*cfg.regularOpCost+(op+rest)=5*cfg.regularOpCost+rest by dsimp[op];omega] using restore
  have ended:=wp_end_label cfg (fuel+5) (5*cfg.regularOpCost+rest) s limits base.toArray frame (caller::callers)
    {arity:=0,height:=base.length,rest:=WNear.Binary.StateReadOuter.restoreReturn,loop:=none} post hc finish
  simpa only[emptyBlockFrame,Nat.add_assoc,Nat.reduceAdd] using ended
end WNear.Proofs.StateReadOuter
