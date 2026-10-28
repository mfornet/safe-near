import Proofs.StateDecodePrefixLeavesRecord

/-! Complete typed normal call of deployed764. -/
namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode

def recordEntered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (9*op)
def recordCallAfter (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory) (out len : UInt32) :=
  recordAfter (recordEntered s cfg.regularOpCost) cfg.regularOpCost i m out len
def recordLeaf (inst height : Nat) (out len : UInt32) : CallFrame :=
  {locals:=#[.i32 out,.i32 len],inst,arity:=0,height,labels:=[],code:=[]}

theorem recordAfter_credits (s : Store NearState) (op i rest : Nat) (m : Memory) (out len : UInt32)
    (hc:s.host.gas.Credits (6*op+rest)) : (recordAfter s op i m out len).host.gas.Credits rest := by
  simpa only[recordAfter,recordHigh,storeI32_host,paid,chargedStore] using paid_credits s op 6 rest hc

theorem recordCallAfter_credits (cfg : WasmConfig) (s : Store NearState) (i rest : Nat) (m : Memory) (out len : UInt32)
    (hc:s.host.gas.Credits (16*cfg.regularOpCost+rest)) : (recordCallAfter cfg s i m out len).host.gas.Credits rest := by
  let op:=cfg.regularOpCost
  have c0:=StorePair.charged_credits s op (9*op+(6*op+rest)) (hc.mono (by dsimp[op];omega))
  have c1:=StorePair.charged_credits (chargedStore s op) (9*op) (6*op+rest) c0
  exact recordAfter_credits (recordEntered s op) op i rest m out len c1

theorem wp_call_record (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame) (code : Expr)
    (out len : UInt32) (mi : ModuleInst) (i address : Nat) (m : Memory) (post : Post)
    (hm:s.modules[frame.inst]?=some mi) (hfi:mi.funcAddrs[764]?=some address)
    (hf:s.funcs[address]?=some (.wasm WNear.Binary.StateDecodePrefixLeaves.recordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.recordFunction))
    (hi:mi.memAddrs[0]?=some i) (he:s.mems[i]?=some m) (hw:m.wf) (hb:out.toNat+8≤m.byteSize)
    (hd:callers.length+1<limits.maxCallDepth) (hc:s.host.gas.Credits (16*cfg.regularOpCost+rest))
    (hn:WP cfg fuel (.next (atCode (recordCallAfter cfg s i m out len) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel+8) (.next (atCode s limits (base++[Value.i32 out,.i32 len]).toArray frame callers (.call 764::code)))
      (16*cfg.regularOpCost+rest) post := by
  let op:=cfg.regularOpCost
  let active:=recordEntered s op
  let leaf:=recordLeaf frame.inst base.length out len
  let saved:={frame with code}
  have c0:=StorePair.charged_credits s op (9*op+(6*op+rest)) (hc.mono (by dsimp[op];omega))
  have ca:=StorePair.charged_credits (chargedStore s op) (9*op) (6*op+rest) c0
  have cf:=recordCallAfter_credits cfg s i rest m out len hc
  have leaveNext:WP cfg fuel (.next (atCode (recordCallAfter cfg s i m out len) limits (base++[]).toArray saved callers saved.code)) rest post:=by
    simpa only[saved,atCode,List.append_nil] using hn
  have leave:=wp_leave_wasm cfg fuel rest (recordCallAfter cfg s i m out len) limits base [] leaf saved callers post rfl rfl rfl cf leaveNext
  have bn:WP cfg (fuel+1) (.next (atCode (recordAfter active op i m out len) limits base.toArray leaf (saved::callers) [])) rest post:=by
    simpa only[recordCallAfter,active,op,List.append_nil] using leave
  have body:=wp_record_body cfg (fuel+1) rest active limits base.toArray leaf (saved::callers) [] out len mi i m post rfl rfl hm hi he hw hb ca bn
  have activationEq:activationGas cfg.regularOpCost (wasmLocals WNear.Binary.StateDecodePrefixLeaves.recordFunction [.i32 out,.i32 len])=9*op:=
    WNear.Binary.StateDecodePrefixLeaves.activation764 cfg out len
  have cc:s.host.gas.Credits (cfg.regularOpCost+(activationGas cfg.regularOpCost
      (wasmLocals WNear.Binary.StateDecodePrefixLeaves.recordFunction [.i32 out,.i32 len])+(6*op+rest))):=by
    rw[activationEq]
    exact hc.mono (by dsimp[op];omega)
  have call:=wp_call_wasm cfg (fuel+7) (6*op+rest) s limits base [.i32 out,.i32 len] frame callers code 764 address mi
    WNear.Binary.StateDecodePrefixLeaves.recordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.recordFunction post hm hfi hf rfl hd cc
  rw[activationEq] at call
  have actual:WP cfg (fuel+7) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.StateDecodePrefixLeaves.recordSignature frame.inst WNear.Binary.StateDecodePrefixLeaves.recordFunction [.i32 out,.i32 len])) (6*op+rest) post:=by
    simpa [WNear.Binary.StateDecodePrefixLeaves.recordFunction,WNear.Binary.StateDecodePrefixLeaves.recordSignature,leaf,recordLeaf,
      wasmCallee,wasmLocals,atCode,saved,op] using body
  have result:=call actual
  simpa only[show fuel+7+1=fuel+8 by omega,show cfg.regularOpCost+(9*op+(6*op+rest))=16*cfg.regularOpCost+rest by dsimp[op];omega] using result
end WNear.Proofs.StateDecodePrefixLeaves
