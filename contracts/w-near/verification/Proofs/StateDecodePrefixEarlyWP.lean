import Proofs.StateDecodePrefixEarlyTail

/-! The complete concrete accepted316 prefix ends immediately before374.
All five deployed leaf invocations and every intervening branch are executed. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode

theorem wp_early (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (post : Post) (hn : Native p) (hcode : Code s frame.inst p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.global)
    (hv : p.global.value=.i32 p.sp) (h1 : frame.locals[1]?=some (.i32 p.slice)) (hs : 6≤frame.locals.size)
    (hd : callers.length+1<limits.maxCallDepth) (hc : s.host.gas.Credits (183*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (payloadPrefix cfg s p) limits base.toArray
      (enoughPrefixFrame (prefixLabels frame base.toArray.size code) p) callers payloadRest)) rest post) :
    WP cfg (fuel+149) (.next (atCode s limits base.toArray frame callers (WNear.Binary.StateDecodePrefix.body++code)))
      (183*cfg.regularOpCost+rest) post := by
  have tail:=wp_early_tail cfg fuel rest s limits base frame callers code p post hn hcode hm h1 hs hd hc hnext
  have head:=wp_early_head cfg (fuel+82) (106*cfg.regularOpCost+rest) s limits base frame callers code p post
    hn hcode hm hg hv h1 hs hd
    (hc.mono (by omega)) tail
  simpa only[Nat.add_assoc,Nat.reduceAdd,
    show 77*cfg.regularOpCost+(106*cfg.regularOpCost+rest)=183*cfg.regularOpCost+rest by omega] using head
end WNear.Proofs.StateDecodePrefix
