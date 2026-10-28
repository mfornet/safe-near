import Proofs.StateDecodeBorshReadCode
import Proofs.StateDecodeBorshReadArguments
import Proofs.StateDecodeBorshReadResources

/-! The actual prepared162 call made by161, from original code/native facts. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode sliceSaved wrapperArguments wrapped setupMemory

theorem wp_child_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (ha:q.allocator=1074896)(hm:s.mems[p.memoryIndex]?=some p.memory)
    (hg:s.globals[p.globalIndex]?=some p.global161)(h3:frame.locals[3]?=some (.i32 (scratch p)))
    (hdepth:callers.length+14<limits.maxCallDepth)
    (hc:(sliceSaved s cfg.regularOpCost p).host.gas.Credits ((18*(count p).toNat+2853)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (wrapped cfg s p q) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*(count p).toNat+2486)) (.next (atCode (sliceSaved s cfg.regularOpCost p) limits base.toArray frame callers
      (pairArgumentsCode 3 3 96 8++[.call 162]++code)))
      ((18*(count p).toNat+2853)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let t:=wrapperArguments s op p
  have fields:=wrapperArguments_fields s op p
  have actual:=hcode.child_actual s frame.inst p q a581 a236 hn hd.toAllocationDomain
  have cc:StateDecodeBorshWrapper.Code t frame.inst (actualWrapper p) (actualAllocation p q) a581 a236:=by
    have bc:=actual.child.transport s t frame.inst (actualWrapper p).toBorsh (actualAllocation p q) a581 a236 fields.1 fields.2.1 fields.2.2
    refine ⟨bc,actual.index425,?_,actual.index951,?_⟩
    · rw[fields.1];exact actual.function425
    · rw[fields.1];exact actual.function951
  have cb:=callback_bound p q hn hd.toAllocationDomain
  have gv:(actualWrapper p).global162.value=.i32 (actualWrapper p).sp162:=by
    change p.global162.value=.i32 p.sp162
    rw[hn.wrapperGlobal,hn.wrapperSP]
  have cr:t.host.gas.Credits ((18*(count p).toNat+2847)*op+rest):=by
    unfold t wrapperArguments
    exact paid_credits _ op 6 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have call:=StateDecodeBorshWrapper.wp_call cfg fuel rest t limits base frame callers code
    (actualWrapper p) (actualAllocation p q) a581 a236 p.address162 post
    (wrapper_native p hn) (accepted_domain p q hn hd) cc ha cb.1 cb.2
    (wrapperArguments_memory s op p hm) (wrapperArguments_global s op p hn hg) gv
    hcode.index162 (by rw[fields.1];exact hcode.function162) hdepth
    (by rw[wrapper_count p hn];exact cr) (by simpa only[wrapped,t,op] using hnext)
  have arr:(base++[Value.i32 (actualWrapper p).out162,.i32 (actualWrapper p).slice]).toArray=
      (base.toArray.push (.i32 (scratch p+96))).push (.i32 (scratch p+8)):=by
    change (base++[Value.i32 p.out162,.i32 p.slice]).toArray=_
    rw[hn.wrapperOut,hn.slice]
    apply Array.toList_inj.mp;simp
  have args:=wp_pair_arguments cfg (fuel+(17*(count p).toNat+2480)) ((18*(count p).toNat+2847)*op+rest)
    (sliceSaved s op p) limits base.toArray frame callers (.call 162::code) 3 3 (scratch p) (scratch p) 96 8 post h3 h3
    (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[arr,wrapper_count p hn,t,wrapperArguments,op] using call)
  simpa only[List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.reduceAdd,
    show 6*cfg.regularOpCost+((18*(count p).toNat+2847)*op+rest)=
      (18*(count p).toNat+2853)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using args
end WNear.Proofs.StateDecodeBorshRead
