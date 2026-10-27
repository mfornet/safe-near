import Proofs.StateDispatchReturn
import NearVM.MeteredWasmCall

/-! Complete accepted f432 call with typed activation and normal i64 return. -/
namespace WNear.Proofs.StateDispatchReturn
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
attribute [local irreducible] WP atCode
set_option maxRecDepth 16384

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11 * op)
def callAfter (s : Store NearState) (op index : Nat) (sp : UInt32) := after (entered s op) op index sp

theorem after_credits (s : Store NearState) (op index rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (14 * op + rest)) :
    (after s op index sp).host.gas.Credits rest := by
  have c0 : (reserved s op index sp).host.gas.Credits (9 * op + rest) := paid_credits s op 5 _ (hc.mono (by omega))
  have c1 := paid_credits (reserved s op index sp) op 4 (5 * op + rest) (c0.mono (by omega))
  have c2 := paid_credits (paid (reserved s op index sp) op 4) op 4 (op + rest) (c1.mono (by omega))
  exact paid_credits (setGlobal (paid (paid (reserved s op index sp) op 4) op 4) index (.i32 ((sp - 16) + 16))) op 1 rest (by simpa only [setGlobal,Nat.one_mul] using c2)

theorem callAfter_credits (s : Store NearState) (op index rest : Nat) (sp : UInt32)
    (hc : s.host.gas.Credits (26 * op + rest)) :
    (callAfter s op index sp).host.gas.Credits rest := by
  have h0 := (GasCounter.burn_credits s.host.gas op (11 * op + (14 * op + rest)) (hc.mono (by omega))).2.2.2
  have h1 := (GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (14 * op + rest) h0).2.2.2
  exact after_credits (entered s op) op index rest sp h1

/-- Actual f432 call: accepted low-word status, unchanged value, restored caller. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (mi : ModuleInst) (index address : Nat) (global : GlobalInst)
    (sp : UInt32) (status value : UInt64) (post : Post)
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.globalAddrs[0]? = some index)
    (hg : s.globals[index]? = some global) (hsp : global.value = .i32 sp)
    (hfi : mi.funcAddrs[432]? = some address)
    (hfn : s.funcs[address]? = some (.wasm WNear.Binary.StateDispatch.returnSignature frame.inst WNear.Binary.StateDispatch.returnFunction))
    (hz : status.toUInt32 = 0) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (26 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (callAfter s cfg.regularOpCost index sp) limits
      (base ++ [Value.i64 value]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 17) (.next (atCode s limits (base ++ [Value.i64 status,.i64 value]).toArray frame callers (.call 432 :: code)))
      (26 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {
    locals := #[.i64 status,.i64 value,.i32 0],inst := frame.inst,arity := 1,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have c0 := (GasCounter.burn_credits s.host.gas op (11 * op + (14 * op + rest)) (hc.mono (by dsimp [op]; omega))).2.2.2
  have c1 := (GasCounter.burn_credits (chargedStore s op).host.gas (11 * op) (14 * op + rest) c0).2.2.2
  have cf := callAfter_credits s op index rest sp hc
  have ln : WP cfg fuel (.next (atCode (callAfter s op index sp) limits (base ++ [Value.i64 value]).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,op] using hnext
  have left := wp_leave_wasm cfg fuel rest (callAfter s op index sp) limits base [.i64 value] (reservedFrame leaf sp) saved callers post rfl rfl rfl cf ln
  have stackEq : (base ++ [Value.i64 value]).toArray = base.toArray.push (.i64 value) := by apply Array.toList_inj.mp; simp
  have bn : WP cfg (fuel + 1) (.next (atCode (after active op index sp) limits (base.toArray.push (.i64 value))
      (reservedFrame leaf sp) (saved :: callers) [])) rest post := by
    simpa only [callAfter,active,stackEq] using left
  have body := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] mi index global sp status value post
    rfl rfl (by simp [leaf]) hm hi hg hsp hz c1 bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 15) (14 * op + rest) s limits base [.i64 status,.i64 value]
    frame callers code 432 address mi WNear.Binary.StateDispatch.returnSignature frame.inst WNear.Binary.StateDispatch.returnFunction post hm hfi hfn rfl hd
  have ac : activationGas op (wasmLocals WNear.Binary.StateDispatch.returnFunction [.i64 status,.i64 value]) = 11 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.StateDispatch.returnFunction,ValType.default]
  rw [ac] at cr
  have arrays : #[Value.i64 status,Value.i64 value] ++ #[Value.i32 0] = #[Value.i64 status,Value.i64 value,Value.i32 0] := by
    apply Array.toList_inj.mp; simp
  have next : WP cfg ((fuel + 1) + 15) (.next (wasmCallee active limits base frame callers code WNear.Binary.StateDispatch.returnSignature frame.inst
      WNear.Binary.StateDispatch.returnFunction [.i64 status,.i64 value])) (14 * op + rest) post := by
    simpa only [op,wasmCallee,wasmLocals,WNear.Binary.StateDispatch.returnFunction,WNear.Binary.StateDispatch.returnSignature,
      leaf,saved,atCode,List.map_cons,List.map_nil,List.length_cons,List.length_nil,List.append_nil,ValType.default,arrays] using body
  have result := cr (hc.mono (by dsimp [op]; omega)) next
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (11 * op + (14 * op + rest)) = 26 * cfg.regularOpCost + rest by dsimp [op]; omega] using result
end WNear.Proofs.StateDispatchReturn
