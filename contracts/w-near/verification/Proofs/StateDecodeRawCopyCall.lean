import Proofs.StateDecodeRawCopyBody
import Proofs.StateDecodeRawCopyGas

/-! Actual typed f769 entry and normal void exit, with complete nested770/310
execution and sequential record copies. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode after769

theorem entered769_credits (s : Store NearState) (op rest : Nat) (hc : s.host.gas.Credits (11*op+rest)) :
    (entered769 s op).host.gas.Credits rest := by
  have c:=StorePair.charged_credits s op (10*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10*op) rest c

theorem wp_copy_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (p : Layout) (a581 a236 : Nat) (post : Post)
    (hn : Native p) (hcode : Code s frame.inst p a581 a236) (ha : p.allocator=1074896)
    (hm : s.mems[p.memoryIndex]?=some (laidOutMemory p))
    (hg : s.globals[p.globalIndex]?=some {p.globalRaw with value:=.i32 (scratch p)})
    (hd : callers.length+7<limits.maxCallDepth) (hc : s.host.gas.Credits (447*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter769 cfg s p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+355) (.next (atCode s limits (base++[Value.i32 (scratch p+16),.i32 p.size,.i32 1]).toArray frame callers (.call 769::code)))
      (447*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let active:=entered769 s op
  let leaf:CallFrame:={locals:=#[.i32 (scratch p+16),.i32 p.size,.i32 1,.i32 0],inst:=frame.inst,arity:=0,height:=base.length,labels:=[],code:=[]}
  let saved:={frame with code}
  have ca:=entered769_credits s op (436*op+rest) (hc.mono (by dsimp[op];omega))
  have ac:Code active leaf.inst p a581 a236:=by
    refine {hcode with record:={hcode.record with allocation:=hcode.record.allocation.transport s active frame.inst p.toPositive rfl rfl rfl}}
  have ln : WP cfg fuel (.next (atCode (callAfter769 cfg s p) limits (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only[saved,atCode,List.append_nil] using hnext
  have cf: (callAfter769 cfg s p).host.gas.Credits rest:=(callAfter769_gas cfg s p rest hc).2.2
  have leave:=wp_leave_wasm cfg fuel rest (callAfter769 cfg s p) limits base [] (reserved769Frame leaf p) saved callers post rfl rfl rfl cf ln
  have bn : WP cfg (fuel+1) (.next (atCode (after769 cfg active p) limits base.toArray (reserved769Frame leaf p) (saved::callers) [])) rest post:=by
    simpa only[callAfter769,active,op,List.append_nil] using leave
  have body:=wp_copy_body cfg (fuel+1) rest active limits base leaf (saved::callers) [] p a581 a236 post hn ac ha rfl rfl rfl (by simp[leaf]) hm hg
    (by simpa only[List.length_cons] using hd) ca bn
  have call:=wp_call_wasm cfg (fuel+354) (436*op+rest) s limits base [.i32 (scratch p+16),.i32 p.size,.i32 1] frame callers code 769 p.address769 p.mi
    WNear.Binary.StateDecodeRaw.signature frame.inst WNear.Binary.StateDecodeRaw.function769 post hcode.record.allocation.search.module hcode.index769 hcode.function769 rfl (by omega)
  have ae : activationGas cfg.regularOpCost (wasmLocals WNear.Binary.StateDecodeRaw.function769 [.i32 (scratch p+16),.i32 p.size,.i32 1])=10*op := by
    simp[wasmLocals,WNear.Binary.StateDecodeRaw.function769,activationGas,ValType.default,op]
  rw[ae] at call
  have actual : WP cfg (fuel+354) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDecodeRaw.signature frame.inst
      WNear.Binary.StateDecodeRaw.function769 [.i32 (scratch p+16),.i32 p.size,.i32 1])) (436*op+rest) post:=by
    simpa [wasmCallee,wasmLocals,WNear.Binary.StateDecodeRaw.function769,WNear.Binary.StateDecodeRaw.signature,ValType.default,leaf,saved,atCode,op] using body
  have result:=call (hc.mono (by dsimp[op];omega)) actual
  simpa only[Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(10*op+(436*op+rest))=447*cfg.regularOpCost+rest by dsimp[op];omega] using result
end WNear.Proofs.StateDecodeRaw
