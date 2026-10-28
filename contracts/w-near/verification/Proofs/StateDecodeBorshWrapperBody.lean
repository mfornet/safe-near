import Proofs.StateDecodeBorshWrapperSuffix
import Proofs.InterfaceStack

/-! Complete accepted162 body: actual425, two actual951 calls and all deployed
scalar/control instructions. No callee-execution or post-state domain is assumed. -/
namespace WNear.Proofs.StateDecodeBorshWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode reserved arguments decoded packedCached tagCached after
  decodedMemory packedValue tagValue reservedFrame tagFrame finalFrame readI32 readI64 writeI32 writeI64
private theorem paid_plus(s:Store NearState)(op a b:Nat):paid (paid s op a) op b=paid s op (a+b):=by
  induction b with
  |zero=>rfl
  |succ b ih=>change chargedStore (paid (paid s op a) op b) op=chargedStore (paid s op (a+b)) op;rw[ih]
private theorem body_parts:WNear.Binary.StateDecodeBorshWrapper.body=
    setupCode++argumentsCode++[.call 425]++cacheValueCode++cacheTagCode++suffixCode:=by
  simp only[body_code,bodyCode,suffixCode,List.append_assoc]

theorem wp_body(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236:Nat)(post:Post)(hn:Native p)(hd:StateDecodeBorsh.AcceptedDomain p.toBorsh q)(hcode:Code s frame.inst p q a581 a236)
    (ha:q.allocator=1074896)(hcallback:p.sp.toNat≤1057464+16)
    (hsep:1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global162)(hv:p.global162.value=.i32 p.sp162)
    (h0:frame.locals[0]?=some (.i32 p.out162))(h1:frame.locals[1]?=some (.i32 p.slice))(hs:5≤frame.locals.size)
    (hdepth:callers.length+13<limits.maxCallDepth)(hc:s.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (after cfg s p q) limits base.toArray (finalFrame frame p q) callers code)) rest post):
    WP cfg (fuel+bodySteps p) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.StateDecodeBorshWrapper.body++code))) (bodyCost p*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  have suffix:=wp_suffix cfg fuel rest s limits base frame callers code p q a581 a236 post hn hd hcode hm hg h0 h1 hs (by omega) hc hnext
  have rl:=reserved_locals frame p hs h0 h1
  have shape:=decodedMemory_spec p q hn hd
  have n:=scratch_numbers p hn
  let endCode:=suffixCode++code
  have cache:=wp_cache cfg (fuel+1291) (1371*op+rest) (decoded cfg s p q) limits base.toArray (reservedFrame frame p) callers endCode
    (scratch p) p.mi p.memoryIndex (decodedMemory p q) post rl.2.2.1
    (by rw[reservedFrame_inst,(decoded_fields cfg s p q).2.1];exact hcode.child.prefixCode.child.module)
    hcode.child.prefixCode.child.memoryIndex (decoded_memory cfg s p q hn hd hm) (by rw[shape.2.1];omega)
    ((decoded_credits cfg s p q hn hd (1377*op+rest) (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by dsimp[op];omega))
    (by rw[loadedTagFrame_eq];simpa only[tagCached,packedCached,paid_plus,Nat.reduceAdd,op,endCode] using suffix)
  let t:=arguments s op p
  have fields:=arguments_fields s op p
  have cc:StateDecodeBorsh.Code t (reservedFrame frame p).inst p.toBorsh q a581 a236:=by
    rw[reservedFrame_inst]
    exact hcode.child.transport s t frame.inst p.toBorsh q a581 a236 fields.1 fields.2.1 fields.2.2
  have cg:=arguments_global s op p hn hg
  have cv:p.global425.value=.i32 p.sp425:=by rw[hn.childGlobal,hn.childSP]
  have cost:t.host.gas.Credits ((18*(count p).toNat+2826)*op+rest):=
    arguments_credits cfg s p _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
  let afterCall:=cacheValueCode++cacheTagCode++endCode
  have child:=StateDecodeBorsh.wp_call cfg (fuel+1297) (1377*op+rest) t limits base (reservedFrame frame p) callers afterCall
    p.toBorsh q a581 a236 p.address425 post hn.child hd cc ha hcallback hsep
    (arguments_memory s op p hm) cg cv hcode.index425
    (by rw[reservedFrame_inst,fields.1];exact hcode.function425) hdepth
    (cost.mono (by unfold count;dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[decoded,t,afterCall,op,Nat.add_assoc,Nat.reduceAdd,
      show 6*cfg.regularOpCost+(1371*op+rest)=1377*op+rest by dsimp[op];omega] using cache)
  have arr:(base++[Value.i32 p.out425,.i32 p.slice]).toArray=
      (base.toArray.push (.i32 (scratch p+48))).push (.i32 p.slice):=by
    rw[hn.childOut];apply Array.toList_inj.mp;simp
  have args:=wp_child_arguments cfg (fuel+(17*(count p).toNat+2469)) ((18*(count p).toNat+2826)*op+rest)
    (reserved s op p) limits base.toArray (reservedFrame frame p) callers (.call 425::afterCall) (scratch p) p.slice post rl.2.2.1 rl.2.1
    ((reserved_credits cfg s p ((18*(count p).toNat+2830)*op+rest)
      (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))).mono (by dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[arr,t,arguments,op,count,Nat.add_assoc,Nat.reduceAdd,
      show 1297+(17*(StateDecodeBorsh.count p.toBorsh).toNat+1172)=17*(StateDecodeBorsh.count p.toBorsh).toNat+2469 by omega,
      show (18*(StateDecodeBorsh.count p.toBorsh).toNat+1449)*cfg.regularOpCost+(1377*cfg.regularOpCost+rest)=
        (18*(StateDecodeBorsh.count p.toBorsh).toNat+2826)*cfg.regularOpCost+rest by simp only[Nat.add_mul];omega] using child)
  have reserve:=InterfaceStack.wp_reserve cfg (fuel+(17*(count p).toNat+2473)) ((18*(count p).toNat+2830)*op+rest)
    s limits base.toArray frame callers (argumentsCode++.call 425::afterCall) p.mi p.globalIndex p.global162 p.sp162 2 96 post
    hcode.child.prefixCode.child.module hcode.child.prefixCode.child.globalIndex hg hv
    (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
    (by simpa only[reserved,reservedFrame,scratch,op,Nat.add_assoc,Nat.reduceAdd,
      show 4*cfg.regularOpCost+((18*(count p).toNat+2826)*op+rest)=(18*(count p).toNat+2830)*op+rest by dsimp[op];simp only[Nat.add_mul];omega] using args)
  simpa only[body_parts,setupCode,afterCall,endCode,bodyCost,bodySteps,List.append_assoc,List.cons_append,List.nil_append,Nat.add_assoc,Nat.reduceAdd,
    show 5*cfg.regularOpCost+((18*(count p).toNat+2830)*op+rest)=(18*(count p).toNat+2835)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using reserve
end WNear.Proofs.StateDecodeBorshWrapper
