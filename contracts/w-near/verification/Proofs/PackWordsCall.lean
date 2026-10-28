import Proofs.PackWordsEntry
import NearVM.MeteredWasmCall

/-! Actual typed779 invocation with arbitrary caller operand prefix and frames.
The two memory writes retain their original sequential alias semantics. -/
namespace WNear.Proofs.PackWordsCall
open Wasm Wasm.Near MeteredLogic

def entered(s:Store NearState)(op:Nat):=chargedStore (chargedStore s op) (9*op)
def callAfter(s:Store NearState)(op index:Nat)(out source:UInt32)(memory:Memory):=
  PackWords.packedStore (entered s op) op index out.toNat source.toNat memory
def leafFrame(inst height:Nat)(out source:UInt32):CallFrame:=
  {locals:=#[.i32 out,.i32 source],inst,arity:=0,height,labels:=[],code:=[]}
private theorem charged_mems(s:Store NearState)(n:Nat):(chargedStore s n).mems=s.mems:=rfl
private theorem charged_modules(s:Store NearState)(n:Nat):(chargedStore s n).modules=s.modules:=rfl

/-- Exact entry-inclusive gas and residual credits: one call opcode, nine
activation units and the eight actual memory instructions. -/
theorem callAfter_gas(s:Store NearState)(op index:Nat)(out source:UInt32)(memory:Memory)(rest:Nat)
    (hc:s.host.gas.Credits (18*op+rest)):
    (callAfter s op index out source memory).host.gas.burnt=s.host.gas.burnt+18*op ∧
    (callAfter s op index out source memory).host.gas.promises=s.host.gas.promises ∧
    (callAfter s op index out source memory).host.gas.Credits rest:=by
  have first:=GasCounter.burn_credits s.host.gas op (17*op+rest) (hc.mono (by omega))
  have tail:=PackWordsEntry.finalStore_gas (chargedStore s op) op index out.toNat source.toNat rest memory first.2.2.2
  have eq:PackWordsEntry.finalStore (chargedStore s op) op index out.toNat source.toNat memory=
      callAfter s op index out source memory:=rfl
  rw[eq] at tail
  have burn:(chargedStore s op).host.gas.burnt=s.host.gas.burnt+op:=first.2.1
  exact ⟨by rw[tail.1,burn];omega,tail.2.1.trans first.2.2.1,tail.2.2⟩

theorem callAfter_memory(s:Store NearState)(op index:Nat)(out source:UInt32)(memory:Memory)
    (hm:s.mems[index]?=some memory):
    (callAfter s op index out source memory).mems[index]?=some (PackWords.packedMemory memory out.toNat source.toNat):=by
  unfold callAfter
  apply PackWords.packedStore_memory
  simpa only[entered,charged_mems] using hm

theorem callAfter_frame(s:Store NearState)(op index:Nat)(out source:UInt32)(memory:Memory):
    (callAfter s op index out source memory).modules=s.modules ∧
    (callAfter s op index out source memory).funcs=s.funcs ∧
    (callAfter s op index out source memory).globals=s.globals ∧
    (callAfter s op index out source memory).tables=s.tables ∧
    {(callAfter s op index out source memory).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  simp only[callAfter,entered,PackWords.packedStore,PackWords.copyWord,storeI32,PackWords.charge4,chargedStore,chargeHost]
  exact ⟨trivial,trivial,trivial,trivial,trivial⟩

attribute [local irreducible] WP atCode entered callAfter PackWords.packedStore

theorem wp_call(cfg:WasmConfig)(fuel rest:Nat)(s:Store NearState)(limits:ExecLimits)
    (base:List Value)(frame:CallFrame)(callers:List CallFrame)(code:Expr)(out source:UInt32)
    (mi:ModuleInst)(index address:Nat)(memory:Memory)(post:Post)
    (hm:s.modules[frame.inst]?=some mi)(hi:mi.memAddrs[0]?=some index)
    (hmem:s.mems[index]?=some memory)(hw:memory.wf)
    (hr:source.toNat+12≤memory.byteSize)(hb:out.toNat+8≤memory.byteSize)
    (hindex:mi.funcAddrs[779]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.PackWords.signature frame.inst WNear.Binary.PackWords.function))
    (hd:callers.length+1<limits.maxCallDepth)(hc:s.host.gas.Credits (18*cfg.regularOpCost+rest))
    (hnext:WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index out source memory) limits base.toArray frame callers code)) rest post):
    WP cfg (fuel+10) (.next (atCode s limits (base++[Value.i32 out,.i32 source]).toArray frame callers (.call 779::code)))
      (18*cfg.regularOpCost+rest) post:=by
  let op:=cfg.regularOpCost
  let active:=entered s op
  let f:=leafFrame frame.inst base.length out source
  let saved:={frame with code}
  have c1:=StorePair.charged_credits s op (17*op+rest) (hc.mono (by dsimp[op];omega))
  have cb:active.host.gas.Credits (8*op+rest):=by
    simpa only[active,entered] using StorePair.charged_credits (chargedStore s op) (9*op) (8*op+rest) (c1.mono (by omega))
  have cf:=(callAfter_gas s op index out source memory rest hc).2.2
  have leave:=wp_leave_wasm cfg fuel rest (callAfter s op index out source memory) limits base [] f saved callers post
    rfl rfl rfl cf (by simpa only[saved,atCode,List.append_nil,op] using hnext)
  have am:active.modules[f.inst]?=some mi:=by simpa only[active,entered,charged_modules,f,leafFrame] using hm
  have ae:active.mems[index]?=some memory:=by simpa only[active,entered,charged_mems] using hmem
  have body:=PackWords.wp_body cfg (fuel+1) rest active limits base.toArray f (saved::callers) [] out source mi index memory post
    rfl rfl am hi ae hw hr hb cb
    (by simpa only[callAfter,active,op,List.append_nil] using leave)
  have activation:activationGas cfg.regularOpCost (wasmLocals WNear.Binary.PackWords.function [.i32 out,.i32 source])=9*op:=by
    simp[activationGas,wasmLocals,WNear.Binary.PackWords.function,op]
  have cc:s.host.gas.Credits (cfg.regularOpCost+(activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.PackWords.function [.i32 out,.i32 source])+(8*op+rest))):=by
    rw[activation];exact hc.mono (by dsimp[op];omega)
  have call:=wp_call_wasm cfg (fuel+9) (8*op+rest) s limits base [.i32 out,.i32 source] frame callers code 779 address mi
    WNear.Binary.PackWords.signature frame.inst WNear.Binary.PackWords.function post hm hindex hf rfl (by omega) cc
  rw[activation] at call
  have actual:WP cfg (fuel+9) (.next (wasmCallee active limits base frame callers code WNear.Binary.PackWords.signature
      frame.inst WNear.Binary.PackWords.function [.i32 out,.i32 source])) (8*op+rest) post:=by
    simpa [WNear.Binary.PackWords.body,WNear.Binary.PackWords.function,WNear.Binary.PackWords.signature,
      wasmCallee,wasmLocals,ValType.default,PackWords.body,atCode,f,leafFrame,saved,op,Nat.add_assoc] using body
  have result:=call (by simpa only[active,entered,op] using actual)
  simpa only[op,Nat.add_assoc,show cfg.regularOpCost+(9*cfg.regularOpCost+(8*cfg.regularOpCost+rest))=18*cfg.regularOpCost+rest by omega] using result
end WNear.Proofs.PackWordsCall
