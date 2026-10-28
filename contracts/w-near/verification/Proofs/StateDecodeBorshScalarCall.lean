import Proofs.StateDecodeBorshArguments
import Proofs.StateDecodeBorshCode
import Proofs.StateDecodeBorshWideNative
import Proofs.StateDecodeBorshNarrowNative

/-! Actual425's shared four-argument preparation followed by the complete
accepted372/371 reader. Native domains come from original425 resources. -/
namespace WNear.Proofs.StateDecodeBorsh.ScalarCall
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode StateDecodeScalar.callAfter
private theorem mems_paid(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem globals_paid(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih

def layout(wide:Bool)(p:Layout)(q:StateDecodeVectorCopy.Layout):=if wide then wideLayout p q else narrowLayout p q
def after(wide:Bool)(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodeScalar.callAfter wide cfg (paid s cfg.regularOpCost 4) (layout wide p q)

theorem wp_call(wide:Bool)(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (hm:s.mems[p.memoryIndex]?=some (layout wide p q).memory)
    (hg:s.globals[p.globalIndex]?=some {p.global425 with value:=.i32 (scratch p)})
    (h1:frame.locals[1]?=some (.i32 p.slice))(h2:frame.locals[2]?=some (.i32 (scratch p)))
    (hdepth:callers.length+2<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((if wide then 172 else 155)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after wide cfg s p q) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(if wide then 138 else 122)) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeBorsh.scalarArguments++[.call (if wide then 372 else 371)]++code)))
      ((if wide then 172 else 155)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let t:=paid s op 4
  let child:=layout wide p q
  have cc:=hcode.paid s op 4 frame.inst p q a581 a236
  have nc:StateDecodeScalar.Native wide child:=by
    cases wide
    · exact narrow_native p q hn hd
    · exact wide_native p q hn hd
  have sc:StateDecodeScalar.Code wide t frame.inst child:=by
    cases wide
    · exact cc.narrow t frame.inst p q a581 a236
    · exact cc.wide t frame.inst p q a581 a236
  have mi:child.memoryIndex=p.memoryIndex:=by cases wide <;> rfl
  have gi:child.globalIndex=p.globalIndex:=by cases wide <;> rfl
  have gv:child.global={p.global425 with value:=.i32 (scratch p)}:=by cases wide <;> rfl
  have sp:child.global.value=.i32 child.sp:=by cases wide <;> rfl
  have index:child.mi.funcAddrs[if wide then 372 else 371]?=some (if wide then p.address372 else p.address371):=by
    cases wide
    · exact cc.index371
    · exact cc.index372
  have function:t.funcs[if wide then p.address372 else p.address371]?=some (.wasm WNear.Binary.StateDecodeScalar.signature frame.inst (WNear.Binary.StateDecodeScalar.function wide)):=by
    cases wide
    · exact cc.function371
    · exact cc.function372
  have budget:(if wide then 172 else 155)=4+(StateDecodeScalar.bodyCost wide+StateDecodeScalar.activationUnits wide+1):=by cases wide <;> rfl
  have cr:t.host.gas.Credits ((StateDecodeScalar.bodyCost wide+StateDecodeScalar.activationUnits wide+1)*op+rest):=
    paid_credits s op 4 _ (hc.mono (by rw[budget];dsimp[op];simp only[Nat.add_mul];omega))
  have call:=StateDecodeScalar.wp_call wide cfg fuel rest t limits base frame callers code child
    (if wide then p.address372 else p.address371) post nc sc
    (by rw[mi,mems_paid];exact hm) (by rw[gi,gv,globals_paid];exact hg) sp index function hdepth cr hnext
  have arr:(base++[Value.i32 child.out,.i32 child.slice]).toArray=
      (base.toArray.push (.i32 (scratch p+56))).push (.i32 p.slice):=by
    have out:child.out=scratch p+56:=by cases wide <;> rfl
    have slice:child.slice=p.slice:=by cases wide <;> rfl
    rw[out,slice];apply Array.toList_inj.mp;simp
  have args:=wp_arguments cfg (fuel+StateDecodeScalar.bodySteps wide+1)
    ((StateDecodeScalar.bodyCost wide+StateDecodeScalar.activationUnits wide+1)*op+rest)
    s limits base.toArray frame callers (.call (if wide then 372 else 371)::code) (scratch p) p.slice post h2 h1
    (hc.mono (by rw[budget];dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[arr,t,op,after,child] using call)
  cases wide <;> simpa only[WNear.Binary.StateDecodeBorsh.scalarArguments,StateDecodeScalar.bodySteps,StateDecodeScalar.bodyCost,
    StateDecodeScalar.activationUnits,Bool.false_eq_true,ite_false,ite_true,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 4*cfg.regularOpCost+((138+12+1)*op+rest)=155*cfg.regularOpCost+rest by dsimp[op];omega,
    show 4*cfg.regularOpCost+((154+13+1)*op+rest)=172*cfg.regularOpCost+rest by dsimp[op];omega] using args
end WNear.Proofs.StateDecodeBorsh.ScalarCall
