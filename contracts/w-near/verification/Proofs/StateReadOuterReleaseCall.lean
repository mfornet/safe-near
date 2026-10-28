import Proofs.StateReadOuterArguments

/-! The real219 release arguments followed by the complete checked insertion
branch of the deployed vector-drop chain. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode VectorDropInsert.callAfter

theorem wp_release_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (p:VectorDropPositive.Layout)(q:DeallocateCore.Layout)(address68 address237 address582:Nat)(post:Post)
    (hr:VectorDropInsert.Resources s frame.inst p q address68 address237 address582)(hv:p.vector=r+24)
    (h1:frame.locals[1]?=some (.i32 r))(hd:callers.length+8<limits.maxCallDepth)
    (hc:s.host.gas.Credits (233*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (VectorDropInsert.callAfter (paid s cfg.regularOpCost 3) cfg.regularOpCost q)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+158) (.next (atCode s limits base.toArray frame callers (releaseArgumentsCode++[.call 68]++code)))
      (233*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have ready(n:Nat):VectorDropInsert.Resources (paid s op n) frame.inst p q address68 address237 address582:=by
    induction n with
    |zero=>exact hr
    |succ n ih=>exact ih.charge (paid s op n) frame.inst op p q address68 address237 address582
  have call:=VectorDropInsert.wp_call cfg fuel rest (paid s op 3) limits base frame callers code p q address68 address237 address582 post
    (ready 3) hd (paid_credits s op 3 _ (hc.mono (by dsimp[op];omega))) hnext
  have arr:(base++[Value.i32 p.vector]).toArray=base.toArray.push (.i32 (r+24)):=by rw[hv];apply Array.toList_inj.mp;simp
  have next:WP cfg (fuel+155) (.next (atCode (paid s op 3) limits (base.toArray.push (.i32 (r+24))) frame callers (.call 68::code)))
      (230*op+rest) post:=by simpa only[arr,op] using call
  have args:=wp_release_arguments cfg (fuel+155) (230*op+rest) s limits base.toArray frame callers (.call 68::code) r 0 post h1
    (hc.mono (by dsimp[op];omega)) next
  have ce:3*cfg.regularOpCost+(230*op+rest)=233*cfg.regularOpCost+rest:=by dsimp[op];omega
  rw[ce] at args
  simpa only[List.singleton_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.StateReadOuter
