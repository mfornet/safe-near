import Proofs.StateDecodeVectorBody

/-! Actual373 typed normal call. No allocator execution premise is required. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

def leaf (inst height:Nat)(out size:UInt32):CallFrame:=
  {locals:=#[.i32 out,.i32 size,.i32 0,.i64 0],inst,arity:=0,height,labels:=[],code:=[]}

private theorem charged_fields (s:Store NearState)(n:Nat):
    (chargedStore s n).funcs=s.funcs ∧ (chargedStore s n).modules=s.modules ∧ (chargedStore s n).tables=s.tables:=by exact ⟨rfl,rfl,rfl⟩
private theorem charged_mems (s:Store NearState)(n:Nat):(chargedStore s n).mems=s.mems:=rfl
private theorem charged_globals (s:Store NearState)(n:Nat):(chargedStore s n).globals=s.globals:=rfl
private theorem code_transport (s t:Store NearState)(inst:Nat)(p:Layout)(a b:Nat)(hc:Code s inst p a b)
    (hf:t.funcs=s.funcs)(hm:t.modules=s.modules)(ht:t.tables=s.tables):Code t inst p a b:=by
  have allocation:=hc.raw.record.allocation.transport s t inst p.toRaw.toPositive hf hm ht
  have record:StateDecodeRaw.Code t inst p.toRaw a b:=by
    refine {hc.raw with record:=?_,function751:=?_,function752:=?_,function769:=?_,function770:=?_}
    · refine {hc.raw.record with allocation:=allocation,function581:=?_,function236:=?_,function310:=?_}
      · rw[hf];exact hc.raw.record.function581
      · rw[hf];exact hc.raw.record.function236
      · rw[hf];exact hc.raw.record.function310
    · rw[hf];exact hc.raw.function751
    · rw[hf];exact hc.raw.function752
    · rw[hf];exact hc.raw.function769
    · rw[hf];exact hc.raw.function770
  refine {hc with raw:=record,function767:=?_}
  rw[hf];exact hc.function767

theorem after_credits (cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (608*cfg.regularOpCost+rest)):
    (after cfg s p).host.gas.Credits rest:=by
  let op:=cfg.regularOpCost
  have cr:(reserved s op p).host.gas.Credits (603*op+rest):=paid_credits s op 5 _ (hc.mono (by dsimp[op];omega))
  have ca:(arguments s op p).host.gas.Credits (585*op+(13*op+rest)):=paid_credits (reserved s op p) op 5 _ (cr.mono (by omega))
  have cc:=StateDecodeRaw.callAfterRaw_credits cfg (arguments s op p) p.toRaw (13*op+rest) ca
  have cAllocated:(allocated cfg s p).host.gas.Credits (13*op+rest):=by
    simpa only[allocated,op] using cc
  rw[after_eq]
  exact tailAfter_credits (allocated cfg s p) op p.memoryIndex p.globalIndex rest (memoryAllocated p) p.outVector (scratch p) cAllocated

theorem callAfter_credits (cfg:WasmConfig)(s:Store NearState)(p:Layout)(rest:Nat)
    (hc:s.host.gas.Credits (620*cfg.regularOpCost+rest)):
    (callAfter cfg s p).host.gas.Credits rest:=by
  let op:=cfg.regularOpCost
  have c0:=StorePair.charged_credits s op (11*op+(608*op+rest)) (hc.mono (by dsimp[op];omega))
  have c1:=StorePair.charged_credits (chargedStore s op) (11*op) (608*op+rest) c0
  have cActive:(entered s op).host.gas.Credits (608*cfg.regularOpCost+rest):=by
    simpa only[entered,op] using c1
  simpa only[callAfter,op] using after_credits cfg (entered s op) p rest cActive

theorem wp_call (cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(a581 a236 address:Nat)(post:Post)
    (hn:Native p)(hcode:Code s frame.inst p a581 a236)(ha:p.allocator=1074896)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.globalVector)(hv:p.globalVector.value=.i32 p.spVector)
    (hi:p.mi.funcAddrs[373]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeVector.signature frame.inst WNear.Binary.StateDecodeVector.function))
    (hd:callers.length+9<limits.maxCallDepth)(hc:s.host.gas.Credits (620*cfg.regularOpCost+rest))
    (hnxt:WP cfg fuel (.next (atCode (callAfter cfg s p) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+495) (.next (atCode s limits (base++[Value.i32 p.outVector,.i32 p.size]).toArray frame callers (.call 373::code)))
      (620*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=entered s op
  let f:=leaf frame.inst base.length p.outVector p.size
  let saved:={frame with code}
  have c0:=StorePair.charged_credits s op (11*op+(608*op+rest)) (hc.mono (by dsimp[op];omega))
  have ca:=StorePair.charged_credits (chargedStore s op) (11*op) (608*op+rest) c0
  have cf:=callAfter_credits cfg s p rest hc
  have ln:WP cfg fuel (.next (atCode (callAfter cfg s p) limits (base++[]).toArray saved callers saved.code)) rest post:=by
    simpa only[saved,atCode,List.append_nil] using hnxt
  have leave:=wp_leave_wasm cfg fuel rest (callAfter cfg s p) limits base [] (cachedFrame f p) saved callers post rfl rfl rfl cf ln
  have bn:WP cfg (fuel+1) (.next (atCode (after cfg active p) limits base.toArray (cachedFrame f p) (saved::callers) [])) rest post:=by
    simpa only[callAfter,active,op,List.append_nil] using leave
  have ac:Code active frame.inst p a581 a236:=code_transport s active frame.inst p a581 a236 hcode rfl rfl rfl
  have am:active.mems[p.memoryIndex]?=some p.memory:=by simpa only[active,entered,charged_mems] using hm
  have ag:active.globals[p.globalIndex]?=some p.globalVector:=by simpa only[active,entered,charged_globals] using hg
  have depth:(saved::callers).length+8<limits.maxCallDepth:=by simp only[List.length_cons];omega
  have body:=wp_body cfg (fuel+1) rest active limits base f (saved::callers) [] p a581 a236 post hn ac ha rfl rfl (by simp[f,leaf]) am ag hv depth ca bn
  have ae:activationGas op (wasmLocals WNear.Binary.StateDecodeVector.function [.i32 p.outVector,.i32 p.size])=11*op:=
    WNear.Binary.StateDecodeVector.activation373 op p.outVector p.size
  have cc:s.host.gas.Credits (cfg.regularOpCost+(activationGas cfg.regularOpCost (wasmLocals WNear.Binary.StateDecodeVector.function [.i32 p.outVector,.i32 p.size])+(608*op+rest))):=by
    rw[ae];exact hc.mono (by dsimp[op];omega)
  have call:=wp_call_wasm cfg (fuel+494) (608*op+rest) s limits base [.i32 p.outVector,.i32 p.size] frame callers code 373 address p.mi
    WNear.Binary.StateDecodeVector.signature frame.inst WNear.Binary.StateDecodeVector.function post hcode.raw.record.allocation.search.module hi hf rfl (by omega) cc
  rw[ae] at call
  have actual:WP cfg (fuel+494) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDecodeVector.signature frame.inst WNear.Binary.StateDecodeVector.function [.i32 p.outVector,.i32 p.size])) (608*op+rest) post:=by
    simpa [WNear.Binary.StateDecodeVector.function,WNear.Binary.StateDecodeVector.signature,wasmCallee,wasmLocals,ValType.default,
      f,leaf,saved,atCode,op,show fuel+1+493=fuel+494 by omega] using body
  have result:=call actual
  simpa only[show fuel+494+1=fuel+495 by omega,show cfg.regularOpCost+(11*op+(608*op+rest))=620*cfg.regularOpCost+rest by dsimp[op];omega] using result
end WNear.Proofs.StateDecodeVector
