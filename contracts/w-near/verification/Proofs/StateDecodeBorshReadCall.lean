import Proofs.StateDecodeBorshReadBody

/-! Complete accepted typed161 invocation, including caller opcode, real
activation, the proved deployed body and the normal void-function leave. -/
namespace WNear.Proofs.StateDecodeBorshRead
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_charge)
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after wrappedMemory scratchMemory upperMemory acceptedMemory resultMemory readI32 readI64

def entered(s:Store NearState)(op:Nat):=chargedStore (chargedStore s op) (11*op)
def callAfter(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):=after cfg (entered s cfg.regularOpCost) p q
def leafFrame(inst height:Nat)(out pointer length:UInt32):CallFrame:=
  {locals:=#[.i32 out,.i32 pointer,.i32 length,.i32 0,.i64 0],inst,arity:=0,height,labels:=[],code:=[]}
private theorem charged_mems(s:Store NearState)(n:Nat):(chargedStore s n).mems=s.mems:=rfl
private theorem charged_globals(s:Store NearState)(n:Nat):(chargedStore s n).globals=s.globals:=rfl

theorem entered_credits(s:Store NearState)(op rest:Nat)(hc:s.host.gas.Credits (12*op+rest)):
    (entered s op).host.gas.Credits rest:=by
  have one:=StorePair.charged_credits s op (11*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (11*op) rest one

theorem callAfter_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(rest:Nat)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4996)*cfg.regularOpCost+rest)):
    (callAfter cfg s p q).host.gas.Credits rest:=by
  have c: (entered s cfg.regularOpCost).host.gas.Credits (bodyCost p*cfg.regularOpCost+rest):=
    entered_credits s cfg.regularOpCost _ (hc.mono (by unfold bodyCost;simp only[Nat.add_mul];omega))
  exact after_credits cfg (entered s cfg.regularOpCost) p q hn hd rest c

theorem wp_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (a581 a236 address:Nat)(post:Post)(hn:Native p)(hd:AcceptedDomain p q)(hcode:Code s frame.inst p q a581 a236)
    (ha:q.allocator=1074896)
    (hm:s.mems[p.memoryIndex]?=some p.memory)(hg:s.globals[p.globalIndex]?=some p.global161)(hv:p.global161.value=.i32 p.sp161)
    (state:WNear.State)(hw:state.WF)(hheader:StateReadHeaderBytes.At p.memory p.pointer.toNat state)(hl:p.length=29)
    (hi:p.mi.funcAddrs[161]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeBorshRead.signature frame.inst WNear.Binary.StateDecodeBorshRead.function))
    (hdepth:callers.length+15<limits.maxCallDepth)
    (hc:s.host.gas.Credits ((18*(count p).toNat+4996)*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (callAfter cfg s p q) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+(17*(count p).toNat+4495)) (.next (atCode s limits
      (base++[Value.i32 p.out161,.i32 p.pointer,.i32 p.length]).toArray frame callers (.call 161::code)))
      ((18*(count p).toNat+4996)*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=entered s op
  let f:=leafFrame frame.inst base.length p.out161 p.pointer p.length
  let saved:={frame with code}
  have ca:active.host.gas.Credits (bodyCost p*cfg.regularOpCost+rest):=
    entered_credits s op _ (hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega))
  have cf:=callAfter_credits cfg s p q hn hd rest hc
  have arity:(finalFrame f p q).arity=0:=by rw[finalFrame_arity];rfl
  have height:(finalFrame f p q).height=base.length:=by rw[finalFrame_height];rfl
  have labels:(finalFrame f p q).labels=[]:=by rw[finalFrame_labels];rfl
  have leave:=wp_leave_wasm cfg fuel rest (callAfter cfg s p q) limits base [] (finalFrame f p q) saved callers post
    arity height labels cf (by simpa only[saved,atCode,List.append_nil] using hnext)
  have next:WP cfg (fuel+1) (.next (atCode (after cfg active p q) limits base.toArray (finalFrame f p q) (saved::callers) [])) rest post:=by
    simpa only[callAfter,active,op,List.append_nil] using leave
  have ac:Code active f.inst p q a581 a236:=hcode.transport s active frame.inst p q a581 a236 rfl rfl rfl
  have am:active.mems[p.memoryIndex]?=some p.memory:=by simpa only[active,entered,charged_mems] using hm
  have ag:active.globals[p.globalIndex]?=some p.global161:=by simpa only[active,entered,charged_globals] using hg
  have body:=wp_body cfg (fuel+1) rest active limits base f (saved::callers) [] p q a581 a236 post hn hd ac ha am ag hv
    rfl rfl rfl (by simp[f,leafFrame]) state hw hheader hl (by simp only[List.length_cons];omega) ca next
  have ae:=WNear.Binary.StateDecodeBorshRead.activation_cost op p.out161 p.pointer p.length
  have cc:s.host.gas.Credits (cfg.regularOpCost+(activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.StateDecodeBorshRead.function [.i32 p.out161,.i32 p.pointer,.i32 p.length])+(bodyCost p*op+rest))):=by
    rw[ae];exact hc.mono (by unfold bodyCost;dsimp[op];simp only[Nat.add_mul];omega)
  have call:=wp_call_wasm cfg (fuel+(bodySteps p+1)) (bodyCost p*op+rest) s limits base [.i32 p.out161,.i32 p.pointer,.i32 p.length]
    frame callers code 161 address p.mi WNear.Binary.StateDecodeBorshRead.signature frame.inst WNear.Binary.StateDecodeBorshRead.function post
    hcode.child.child.prefixCode.child.module hi hf rfl (by omega) cc
  rw[ae] at call
  have actual:WP cfg (fuel+(bodySteps p+1)) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateDecodeBorshRead.signature frame.inst WNear.Binary.StateDecodeBorshRead.function [.i32 p.out161,.i32 p.pointer,.i32 p.length]))
      (bodyCost p*op+rest) post:=by
    simpa [WNear.Binary.StateDecodeBorshRead.body,WNear.Binary.StateDecodeBorshRead.function,WNear.Binary.StateDecodeBorshRead.signature,wasmCallee,wasmLocals,
      ValType.default,f,leafFrame,saved,atCode,op,List.append_nil,
      show fuel+1+bodySteps p=fuel+(bodySteps p+1) by omega] using body
  have result:=call actual
  simpa only[bodyCost,bodySteps,Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost+(11*op+((18*(count p).toNat+4984)*op+rest))=(18*(count p).toNat+4996)*cfg.regularOpCost+rest by dsimp[op];simp only[Nat.add_mul];omega] using result
end WNear.Proofs.StateDecodeBorshRead
