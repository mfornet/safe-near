import Proofs.StateDecodePrefixWrapperBody

/-! Complete accepted315 typed call, including the real316 call and normal
caller resumption. All execution is justified by deployed code contracts. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic
attribute [local irreducible] WP atCode after StateDecodePrefix.finalMemory readI64

def entered(s:Store NearState)(op:Nat):=chargedStore (chargedStore s op) (11*op)
def callAfter(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=after cfg (entered s cfg.regularOpCost) p q
def leaf(inst height:Nat)(out slice:UInt32):CallFrame:=
  {locals:=#[.i32 out,.i32 slice,.i32 0,.i64 0],inst,arity:=0,height,labels:=[],code:=[]}
private theorem charged_mems(s:Store NearState)(n:Nat):(chargedStore s n).mems=s.mems:=rfl
private theorem charged_globals(s:Store NearState)(n:Nat):(chargedStore s n).globals=s.globals:=rfl
private theorem final_shapes(frame:CallFrame)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (finalFrame frame p q).arity=frame.arity ∧(finalFrame frame p q).height=frame.height ∧(finalFrame frame p q).labels=frame.labels:=by
  simp only[finalFrame,Tail.finalFrame,cacheFrame,reservedFrame,and_self]

theorem callAfter_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (rest:Nat)(hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)
    (hc:s.host.gas.Credits ((18*(StateDecodePrefix.count p.toPrefix).toNat+972)*cfg.regularOpCost+rest)):
    (callAfter cfg s p q).host.gas.Credits rest:=by
  let op:=cfg.regularOpCost
  have first:=StorePair.charged_credits s op (11*op+(bodyCost p*op+rest)) (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega))
  have active:(entered s op).host.gas.Credits (bodyCost p*op+rest):=StorePair.charged_credits (chargedStore s op) (11*op) _ first
  exact after_credits cfg (entered s op) p q rest hn hd active

theorem wp_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236 address:Nat)(post:Post)(hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)
    (hcode:Code s frame.inst p)(hqcode:StateDecodeVectorCopy.Code s frame.inst q a581 a236)(ha:q.allocator=1074896)
    (hcallback:p.sp.toNat≤1057464+16)(hsep:1057464+20≤p.slice.toNat ∨p.slice.toNat+8≤1057464+16)
    (htagsep:p.out.toNat+4≤p.slice.toNat ∨p.slice.toNat+8≤p.out.toNat)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.wrapperGlobal)(hv:p.wrapperGlobal.value=.i32 p.wrapperSP)
    (hi:p.mi.funcAddrs[315]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodePrefixWrapper.signature frame.inst WNear.Binary.StateDecodePrefixWrapper.function))
    (hdepth:callers.length+12<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*(StateDecodePrefix.count p.toPrefix).toNat+972)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (callAfter cfg s p q) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*(StateDecodePrefix.count p.toPrefix).toNat+771)) (.next (atCode s limits (base++[Value.i32 p.wrapperOut,.i32 p.slice]).toArray frame callers (.call 315::code)))
      ((18*(StateDecodePrefix.count p.toPrefix).toNat+972)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=entered s op
  let f:=leaf frame.inst base.length p.wrapperOut p.slice
  let saved:={frame with code}
  have ca0:=StorePair.charged_credits s op (11*op+(bodyCost p*op+rest)) (hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega))
  have ca:active.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest):=StorePair.charged_credits (chargedStore s op) (11*op) _ ca0
  have cf:=callAfter_credits cfg s p q rest hn hd hc
  have shape:=final_shapes f p q
  have leave:=wp_leave_wasm cfg fuel rest (callAfter cfg s p q) limits base [] (finalFrame f p q) saved callers post
    shape.1 shape.2.1 shape.2.2 cf (by simpa only[saved,atCode,List.append_nil] using hnext)
  have next:WP cfg (fuel+1) (.next (atCode (after cfg active p q) limits base.toArray (finalFrame f p q) (saved::callers) [])) rest post:=by
    simpa only[callAfter,active,op,List.append_nil] using leave
  have ac:Code active frame.inst p:=⟨hcode.child.transport s active frame.inst p.toPrefix rfl rfl,hcode.childAddress,hcode.childFunction⟩
  have qc:StateDecodeVectorCopy.Code active frame.inst q a581 a236:=StateDecodePrefix.allocation_copy_code_transport s active frame.inst q a581 a236 hqcode rfl rfl rfl
  have am:active.mems[p.memoryIndex]?=some p.memory:=by simpa only[active,entered,charged_mems] using hm
  have ag:active.globals[p.globalIndex]?=some p.wrapperGlobal:=by simpa only[active,entered,charged_globals] using hg
  have body:=wp_body cfg (fuel+1) rest active limits base f (saved::callers) [] p q a581 a236 post hn hd ac qc ha hcallback hsep htagsep am ag hv
    rfl rfl (by simp[f,leaf]) (by simp only[List.length_cons];omega) ca next
  have ae:=WNear.Binary.StateDecodePrefixWrapper.activation_cost op p.wrapperOut p.slice
  have cc:s.host.gas.Credits (cfg.regularOpCost+(activationGas cfg.regularOpCost (wasmLocals WNear.Binary.StateDecodePrefixWrapper.function [.i32 p.wrapperOut,.i32 p.slice])+(bodyCost p*op+rest))):=by
    rw[ae];exact hc.mono (by dsimp[bodyCost,op];simp only[Nat.add_mul];omega)
  have call:=wp_call_wasm cfg (fuel+(bodySteps p+1)) (bodyCost p*op+rest) s limits base [.i32 p.wrapperOut,.i32 p.slice] frame callers code 315 address p.mi
    WNear.Binary.StateDecodePrefixWrapper.signature frame.inst WNear.Binary.StateDecodePrefixWrapper.function post hcode.child.module hi hf rfl (by omega) cc
  rw[ae] at call
  have actual:WP cfg (fuel+(bodySteps p+1)) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDecodePrefixWrapper.signature frame.inst WNear.Binary.StateDecodePrefixWrapper.function [.i32 p.wrapperOut,.i32 p.slice])) (bodyCost p*op+rest) post:=by
    simpa [WNear.Binary.StateDecodePrefixWrapper.function,WNear.Binary.StateDecodePrefixWrapper.signature,wasmCallee,wasmLocals,ValType.default,f,leaf,saved,atCode,op,List.append_nil,
      show fuel+1+bodySteps p=fuel+(bodySteps p+1) by omega] using body
  have result:=call actual
  simpa only[bodyCost,bodySteps,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(11*op+((18*(StateDecodePrefix.count p.toPrefix).toNat+960)*op+rest))=(18*(StateDecodePrefix.count p.toPrefix).toNat+972)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using result
end WNear.Proofs.StateDecodePrefixWrapper
