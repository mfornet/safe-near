import Proofs.StateDecodeBorshArguments
import Proofs.StateDecodeBorshCode

/-! Actual425's four argument instructions and the entire real315 invocation.
All data/domain premises describe the original prefix layout. -/
namespace WNear.Proofs.StateDecodeBorsh.PrefixCall
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode StateDecodePrefixWrapper.callAfter
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def after(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodePrefixWrapper.callAfter cfg (paid s cfg.regularOpCost 4) p.toPrefixWrapper q

theorem wp_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (ha:q.allocator=1074896)(hcallback:p.sp.toNat≤1057464+16)
    (hsep:1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.wrapperGlobal)
    (h1:frame.locals[1]?=some (.i32 p.slice))(h2:frame.locals[2]?=some (.i32 (scratch p)))
    (hdepth:callers.length+12<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*(count p).toNat+976)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*(count p).toNat+775)) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeBorsh.prefixArguments++[.call 315]++code)))
      ((18*(count p).toNat+976)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let t:=paid s op 4
  have cc:=hcode.paid s op 4 frame.inst p q a581 a236
  have cr:t.host.gas.Credits ((18*(count p).toNat+972)*op+rest):=
    paid_credits s op 4 _ (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have hv:p.wrapperGlobal.value=.i32 p.wrapperSP:=by rw[hn.childGlobal,hn.childSP]
  have call:=StateDecodePrefixWrapper.wp_call cfg fuel rest t limits base frame callers code p.toPrefixWrapper q
    a581 a236 p.address315 post hn.prefixNative hd.toAcceptedDomain cc.prefixCode cc.allocation ha hcallback hsep hd.tagSeparation
    (by rw[mems_paid];exact hm) (by rw[globals_paid];exact hg) hv cc.index315 cc.function315 hdepth cr hnext
  have arr:(base++[Value.i32 p.wrapperOut,.i32 p.slice]).toArray=
      (base.toArray.push (.i32 (scratch p+56))).push (.i32 p.slice):=by
    rw[hn.childOut];apply Array.toList_inj.mp;simp
  have args:=wp_arguments cfg (fuel+(17*(count p).toNat+771))
    ((18*(count p).toNat+972)*op+rest) s limits base.toArray frame callers (.call 315::code) (scratch p) p.slice post h2 h1
    (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[arr,count,t,op,after] using call)
  simpa only[arguments_exact,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4*cfg.regularOpCost+((18*(count p).toNat+972)*op+rest)=(18*(count p).toNat+976)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using args
end WNear.Proofs.StateDecodeBorsh.PrefixCall
