import Proofs.StateDecodePrefixWrapperControl
import Proofs.StateDecodePrefixCall
import Proofs.ValueReturnBorrow

/-! Actual315 stack reservation, arguments, and the full real316 invocation. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reserved arguments StateDecodePrefix.callAfter
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem global_host(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).host=s.host:=rfl
private theorem global_funcs(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).funcs=s.funcs:=rfl
private theorem global_modules(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).modules=s.modules:=rfl
private theorem global_tables(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).tables=s.tables:=rfl
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl

def decoded(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=
  StateDecodePrefix.callAfter cfg (arguments s cfg.regularOpCost p) p.toPrefix q

theorem wp_prefix (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)
    (hcode:Code s frame.inst p)(hqcode:StateDecodeVectorCopy.Code s frame.inst q a581 a236)(ha:q.allocator=1074896)
    (hcallback:p.sp.toNat≤1057464+16)(hsep:1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.wrapperGlobal)(hv:p.wrapperGlobal.value=.i32 p.wrapperSP)
    (h1:frame.locals[1]?=some (.i32 p.slice))(hs:3≤frame.locals.size)
    (hdepth:callers.length+11<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*(StateDecodePrefix.count p.toPrefix).toNat+927)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (decoded cfg s p q) limits base.toArray (reservedFrame frame p) callers code)) rest post):
    WP cfg (fuel+(17*(StateDecodePrefix.count p.toPrefix).toNat+734)) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodePrefixWrapper.setup++WNear.Binary.StateDecodePrefixWrapper.arguments++[.call 316]++code)))
      ((18*(StateDecodePrefix.count p.toPrefix).toNat+927)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=arguments s op p
  let f:=reservedFrame frame p
  let childCost:=(18*(StateDecodePrefix.count p.toPrefix).toNat+920)*op
  have fs:active.funcs=s.funcs:=by simp only[active,arguments,reserved,paid_funcs,global_funcs]
  have ms:active.modules=s.modules:=by simp only[active,arguments,reserved,paid_modules,global_modules]
  have ts:active.tables=s.tables:=by simp only[active,arguments,reserved,paid_tables,global_tables]
  have cm:StateDecodePrefix.Code active f.inst p.toPrefix:=hcode.child.transport s active frame.inst p.toPrefix fs ms
  have cq:StateDecodeVectorCopy.Code active f.inst q a581 a236:=StateDecodePrefix.allocation_copy_code_transport s active frame.inst q a581 a236 hqcode fs ms ts
  have mm:active.mems[p.memoryIndex]?=some p.memory:=by simpa only[active,arguments,reserved,paid_mems,global_mems] using hm
  have gg:active.globals[p.globalIndex]?=some p.global:=by
    rw[hn.childGlobal]
    simp only[active,arguments,reserved,paid_globals,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]
  have cv:p.global.value=.i32 p.sp:=by rw[hn.childGlobal,hn.childSP]
  have cr:(reserved s op p).host.gas.Credits (2*op+(childCost+rest)):=by
    simpa only[reserved,global_host] using paid_credits s op 5 (2*op+(childCost+rest)) (hc.mono (by dsimp[childCost,op];simp only[Nat.add_mul];omega))
  have ca:active.host.gas.Credits (childCost+rest):=by
    unfold active arguments
    exact paid_credits (reserved s op p) op 2 _ cr
  have call:=StateDecodePrefix.wp_call cfg fuel rest active limits base f callers code p.toPrefix q a581 a236 p.address316 post
    hn.child hd cm cq ha hcallback hsep mm gg cv hcode.childAddress (by rw[fs];exact hcode.childFunction) hdepth ca hnext
  have arr:(base++[Value.i32 p.out,.i32 p.slice]).toArray=(base.toArray.push (.i32 (scratch p))).push (.i32 p.slice):=by
    rw[hn.childOut];apply Array.toList_inj.mp;simp
  have cn:WP cfg (fuel+(17*(StateDecodePrefix.count p.toPrefix).toNat+727)) (.next (atCode active limits
    ((base.toArray.push (.i32 (scratch p))).push (.i32 p.slice)) f callers (.call 316::code))) (childCost+rest) post:=by
    simpa only[arr,childCost,op] using call
  have get1:=wp_local_get cfg (fuel+(17*(StateDecodePrefix.count p.toPrefix).toNat+727)) (childCost+rest) (paid (reserved s op p) op 1) limits
    (base.toArray.push (.i32 (scratch p))) f callers (.call 316::code) 1 (.i32 p.slice) post
    (by simp[f,reservedFrame,h1]) (paid_credits (reserved s op p) op 1 _ (cr.mono (by omega))) (by simpa only[active,arguments,paid,op] using cn)
  have get2:=wp_local_get cfg (fuel+(17*(StateDecodePrefix.count p.toPrefix).toNat+728)) (op+(childCost+rest)) (reserved s op p) limits base.toArray f callers
    (.local_get 1::.call 316::code) 2 (.i32 (scratch p)) post
    (by simp[f,reservedFrame,show 2<frame.locals.size by omega]) (cr.mono (by omega))
    (by simpa only[paid,op,Nat.add_assoc,Nat.reduceAdd] using get1)
  have reserve:=ValueReturnBorrow.wp_reserve cfg (fuel+(17*(StateDecodePrefix.count p.toPrefix).toNat+729)) (2*op+(childCost+rest)) s limits base.toArray frame callers
    (.local_get 2::.local_get 1::.call 316::code) p.mi p.globalIndex p.wrapperGlobal p.wrapperSP 2 post
    hcode.child.module hcode.child.globalIndex hg hv (hc.mono (by dsimp[childCost,op];simp only[Nat.add_mul];omega))
    (by simpa only[reserved,f,reservedFrame,scratch,Nat.add_assoc,Nat.reduceAdd,
      show cfg.regularOpCost+(op+(childCost+rest))=2*op+(childCost+rest) by dsimp[op];omega] using get2)
  simpa only[WNear.Binary.StateDecodePrefixWrapper.setup,WNear.Binary.StateDecodePrefixWrapper.arguments,List.cons_append,List.nil_append,List.append_assoc,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+(2*op+(childCost+rest))=(18*(StateDecodePrefix.count p.toPrefix).toNat+927)*cfg.regularOpCost+rest by dsimp[childCost,op];simp only[Nat.add_mul];omega] using reserve
end WNear.Proofs.StateDecodePrefixWrapper
