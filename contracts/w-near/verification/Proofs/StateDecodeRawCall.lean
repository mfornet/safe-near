import Proofs.StateDecodeRawBody
import Proofs.StateDecodeRawResult

/-! Complete typed f767 call on its positive, flag-zero, directly-fitting path.
The actual body returns explicitly, without a further free callee exit. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode afterRaw

def rawLeafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals:=#[.i32 p.outRaw,.i32 p.size,.i32 p.flag,.i32 0,.i32 0,.i32 0],inst,arity:=0,height,labels:=[],code:=[]}

theorem enteredRaw_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (12*op+rest)) :
    (enteredRaw s op).host.gas.Credits rest := by
  have h:=StorePair.charged_credits s op (11*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (11*op) rest h

/-- All actual nested calls execute from original heap and installed-code data.
No future allocation success, pointer read or execution premise is required. -/
theorem wp_callRaw (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (a581 a236 address : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p a581 a236) (haRoot : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (hg : s.globals[p.globalIndex]?=some p.globalRaw)
    (hv : p.globalRaw.value=.i32 p.spRaw)
    (hi : p.mi.funcAddrs[767]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeRaw.signature frame.inst WNear.Binary.StateDecodeRaw.function767))
    (hd : callers.length+8<limits.maxCallDepth) (hc : s.host.gas.Credits (585*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfterRaw cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+470) (.next (atCode s limits (base++[Value.i32 p.outRaw,.i32 p.size,.i32 p.flag]).toArray frame callers (.call 767::code)))
      (585*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let active:=enteredRaw s op
  let leaf:=rawLeafFrame frame.inst base.length p
  let saved:={frame with code}
  have ca:=enteredRaw_credits s op (573*op+rest) (hc.mono (by dsimp[op];omega))
  have ac:Code active leaf.inst p a581 a236:=hcode.of_fields s active frame.inst p a581 a236 rfl rfl rfl
  have bn : WP cfg fuel (.next (atCode (afterRaw cfg active p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only[callAfterRaw,active,op,saved,atCode] using hnext
  have body:=wp_raw_body cfg fuel rest active limits base leaf saved callers [] p a581 a236 post hn ac haRoot hm hg hv
    rfl rfl rfl (by simp[leaf,rawLeafFrame]) rfl rfl hd ca bn
  have ae : activationGas cfg.regularOpCost (wasmLocals WNear.Binary.StateDecodeRaw.function767 [.i32 p.outRaw,.i32 p.size,.i32 p.flag])=11*op := by
    simp[activationGas,wasmLocals,WNear.Binary.StateDecodeRaw.function767,ValType.default,op]
  have call:=wp_call_wasm cfg (fuel+469) (573*op+rest) s limits base [.i32 p.outRaw,.i32 p.size,.i32 p.flag] frame callers code 767 address p.mi
    WNear.Binary.StateDecodeRaw.signature frame.inst WNear.Binary.StateDecodeRaw.function767 post hcode.record.allocation.search.module hi hf rfl (by omega)
  rw[ae] at call
  have actual : WP cfg (fuel+469) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDecodeRaw.signature frame.inst
      WNear.Binary.StateDecodeRaw.function767 [.i32 p.outRaw,.i32 p.size,.i32 p.flag])) (573*op+rest) post := by
    simpa[leaf,rawLeafFrame,saved,atCode,wasmCallee,wasmLocals,WNear.Binary.StateDecodeRaw.signature,WNear.Binary.StateDecodeRaw.function767,ValType.default,op] using body
  have result:=call (hc.mono (by dsimp[op];omega)) actual
  simpa only[Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(11*op+(573*op+rest))=585*cfg.regularOpCost+rest by dsimp[op];omega] using result
end WNear.Proofs.StateDecodeRaw
