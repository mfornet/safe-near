import Proofs.StateReadOuterArguments

/-! The actual219 pair-packing call includes its four argument instructions. -/
namespace WNear.Proofs.StateReadOuter
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode PackWordsCall.callAfter
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

theorem wp_pack_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(r:UInt32)
    (mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (h1:frame.locals[1]?=some (.i32 r))(hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)
    (he:s.mems[index]?=some memory)(hw:memory.wf)(hs:(r+24).toNat+12≤memory.byteSize)(ho:r.toNat+8≤memory.byteSize)
    (hfi:mi.funcAddrs[779]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.PackWords.signature frame.inst WNear.Binary.PackWords.function))
    (hd:callers.length+1<limits.maxCallDepth)(hc:s.host.gas.Credits (22*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (PackWordsCall.callAfter (paid s cfg.regularOpCost 4) cfg.regularOpCost index r (r+24) memory)
      limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+14) (.next (atCode s limits base.toArray frame callers (packArgumentsCode++[.call 779]++code)))
      (22*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have call:=PackWordsCall.wp_call cfg fuel rest (paid s op 4) limits base frame callers code r (r+24) mi index address memory post
    (by rw[paid_modules];exact hm) hi (by rw[paid_mems];exact he) hw hs ho hfi (by rw[paid_funcs];exact hf) hd
    (paid_credits s op 4 _ (hc.mono (by dsimp[op];omega))) hnext
  have arr:(base++[Value.i32 r,.i32 (r+24)]).toArray=(base.toArray.push (.i32 r)).push (.i32 (r+24)):=by apply Array.toList_inj.mp;simp
  have next:WP cfg (fuel+10) (.next (atCode (paid s op 4) limits ((base.toArray.push (.i32 r)).push (.i32 (r+24))) frame callers (.call 779::code)))
      (18*op+rest) post:=by simpa only[arr,op] using call
  have args:=wp_pack_arguments cfg (fuel+10) (18*op+rest) s limits base.toArray frame callers (.call 779::code) r 0 post h1
    (hc.mono (by dsimp[op];omega)) next
  have ce:4*cfg.regularOpCost+(18*op+rest)=22*cfg.regularOpCost+rest:=by dsimp[op];omega
  rw[ce] at args
  simpa only[List.singleton_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd] using args
end WNear.Proofs.StateReadOuter
