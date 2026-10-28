import Proofs.StateDecodeRawRecordBody
import NearVM.MeteredWasmCall

/-! Actual f770 typed entry and normal void return on its nonzero flag-zero path. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
attribute [local irreducible] WP atCode recordAfter

def recordEntered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10*op)
def recordCallAfter (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32) :=
  recordAfter cfg (recordEntered s cfg.regularOpCost) q out

theorem recordEntered_credits (s : Store NearState) (op rest : Nat)
    (hc : s.host.gas.Credits (11*op+rest)) : (recordEntered s op).host.gas.Credits rest := by
  have h:=StorePair.charged_credits s op (10*op+rest) (hc.mono (by omega))
  exact StorePair.charged_credits (chargedStore s op) (10*op) rest h

theorem recordCallAfter_credits (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32) (rest : Nat)
    (hc : s.host.gas.Credits (413*cfg.regularOpCost+rest)) :
    (recordCallAfter cfg s q out).host.gas.Credits rest :=
  (recordAfter_gas cfg (recordEntered s cfg.regularOpCost) q out rest
    (recordEntered_credits s cfg.regularOpCost _ (hc.mono (by omega)))).2.2

theorem wp_record_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : Expr) (q : AllocatePositive.Layout) (out : UInt32) (a581 a236 a310 address : Nat) (post : Post)
    (hn : AllocatePositive.Native q) (hcode : RecordCode s frame.inst q a581 a236 a310)
    (ha : q.allocator=1074896)
    (hm : s.mems[q.memoryIndex]?=some q.memory) (hg : s.globals[q.globalIndex]?=some q.global)
    (hv : q.global.value=.i32 q.sp) (hb : out.toNat+8≤q.memory.byteSize)
    (hi : q.mi.funcAddrs[770]?=some address)
    (hf : s.funcs[address]?=some (.wasm WNear.Binary.StateDecodeRaw.recordSignature frame.inst WNear.Binary.StateDecodeRaw.function770))
    (hd : callers.length+6<limits.maxCallDepth) (hc : s.host.gas.Credits (413*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (recordCallAfter cfg s q out) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+330) (.next (atCode s limits (base++[Value.i32 out,.i32 q.size,.i32 1,.i32 0]).toArray frame callers (.call 770::code)))
      (413*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let active:=recordEntered s op
  let leaf:CallFrame:={locals:=#[.i32 out,.i32 q.size,.i32 1,.i32 0],inst:=frame.inst,arity:=0,height:=base.length,labels:=[],code:=[]}
  let saved:={frame with code}
  have ca:=recordEntered_credits s op (402*op+rest) (hc.mono (by dsimp[op];omega))
  have cc : RecordCode active leaf.inst q a581 a236 a310 := by
    refine {hcode with allocation:=hcode.allocation.transport s active frame.inst q rfl rfl rfl}
  have leaveNext : WP cfg fuel (.next (atCode (recordCallAfter cfg s q out) limits (base++[]).toArray saved callers saved.code)) rest post := by
    simpa only[saved,atCode,List.append_nil] using hnext
  have leave:=wp_leave_wasm cfg fuel rest (recordCallAfter cfg s q out) limits base [] (allocationFrame leaf q) saved callers post
    rfl rfl rfl (recordCallAfter_credits cfg s q out rest hc) leaveNext
  have bn : WP cfg (fuel+1) (.next (atCode (recordAfter cfg active q out) limits base.toArray (allocationFrame leaf q) (saved::callers) [])) rest post := by
    simpa only[recordCallAfter,active,op,List.append_nil] using leave
  have body:=wp_record_body cfg (fuel+1) rest active limits base leaf (saved::callers) [] q out a581 a236 a310 post hn cc ha
    rfl rfl rfl rfl (by simp[leaf]) hm hg hv hb (by simpa only[List.length_cons] using hd) ca bn
  have call:=wp_call_wasm cfg (fuel+329) (402*op+rest) s limits base [.i32 out,.i32 q.size,.i32 1,.i32 0] frame callers code 770 address q.mi
    WNear.Binary.StateDecodeRaw.recordSignature frame.inst WNear.Binary.StateDecodeRaw.function770 post hcode.allocation.search.module hi hf rfl (by omega)
  have ae : activationGas cfg.regularOpCost (wasmLocals WNear.Binary.StateDecodeRaw.function770 [.i32 out,.i32 q.size,.i32 1,.i32 0])=10*op := by
    simp[wasmLocals,WNear.Binary.StateDecodeRaw.function770,activationGas,op]
  rw[ae] at call
  have actual : WP cfg (fuel+329) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDecodeRaw.recordSignature frame.inst
      WNear.Binary.StateDecodeRaw.function770 [.i32 out,.i32 q.size,.i32 1,.i32 0])) (402*op+rest) post := by
    simpa only[leaf,saved,wasmCallee,wasmLocals,WNear.Binary.StateDecodeRaw.recordSignature,WNear.Binary.StateDecodeRaw.function770,
      List.map_nil,List.append_nil,Array.append_empty,List.length_cons,List.length_nil,Nat.reduceAdd,atCode,Nat.add_assoc] using body
  have result:=call (hc.mono (by dsimp[op];omega)) actual
  simpa only[Nat.add_assoc,Nat.reduceAdd,show cfg.regularOpCost+(10*op+(402*op+rest))=413*cfg.regularOpCost+rest by dsimp[op];omega] using result
end WNear.Proofs.StateDecodeRaw
