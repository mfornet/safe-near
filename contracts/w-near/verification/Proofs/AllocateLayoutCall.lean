import Proofs.AllocateLayoutBody
import NearVM.MeteredWasmCall

/-! Actual typed alignment-one layout calls, shared by f751 and f684. -/
namespace WNear.Proofs.AllocateLayout
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP readI32 writeI32 after

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def called (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p

theorem called_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (44 * op + rest)) : (called s op p).host.gas.Credits rest := by
  have co := StorePair.charged_credits s op (10 * op + (33 * op + rest)) (hc.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore s op) (10 * op) (33 * op + rest) co
  exact (after_gas (entered s op) op rest p ca).2.2

/-- Both deployed normal layout copies are actual typed calls. Only their
panic-site constants and installed index differ; neither panic executes. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (message location previous : UInt32) (p : Layout) (functionIndex address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some p.mi) (hgi : p.mi.globalAddrs[0]? = some p.globalIndex)
    (hg : s.globals[p.globalIndex]? = some p.global) (hsp : p.global.value = .i32 p.sp)
    (hmi : p.mi.memAddrs[0]? = some p.memoryIndex) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hfi : p.mi.funcAddrs[functionIndex]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.AllocateLayout.signature frame.inst
      (WNear.Binary.AllocateLayout.function message location previous)))
    (hw : p.memory.wf) (hib : p.input.toNat + 8 ≤ p.memory.byteSize) (hob : p.out.toNat + 8 ≤ p.memory.byteSize)
    (ha : readI32 p.memory (p.input.toNat + 4) = 1) (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (44 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (called s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 36) (.next (atCode s limits (base ++ [Value.i32 p.out,.i32 p.input]).toArray frame callers
      (.call functionIndex :: code))) (44 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[.i32 p.out,.i32 p.input,.i32 0,.i32 0],inst := frame.inst,arity := 0,height := base.length,labels := [],code := []}
  let saved := {frame with code}
  have co := StorePair.charged_credits s op (10 * op + (33 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (33 * op + rest) := StorePair.charged_credits (chargedStore s op) (10 * op) (33 * op + rest) co
  have hr : Ready active leaf p := by
    constructor
    · simpa only [active,entered,chargedStore,leaf] using hm
    · exact hgi
    · simpa only [active,entered,chargedStore] using hg
    · exact hsp
    · exact hmi
    · simpa only [active,entered,chargedStore] using hmem
    · rfl
    · rfl
    · simp [leaf]
    · exact hw
    · exact hib
    · exact hob
    · exact ha
  have ln : WP cfg fuel (.next (atCode (called s op p) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil,op] using hnext
  have left := wp_leave_wasm cfg fuel rest (called s op p) limits base [] (finalFrame leaf p) saved callers post rfl rfl rfl
    (called_credits s op rest p hc) ln
  have bn : WP cfg (fuel + 1) (.next (atCode (after active op p) limits base.toArray (finalFrame leaf p) (saved :: callers) [])) rest post := by
    simpa only [called,active,List.append_nil] using left
  have b := wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] message location previous p post hr ca bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 34) (33 * op + rest) s limits base [.i32 p.out,.i32 p.input] frame callers code functionIndex address p.mi
    WNear.Binary.AllocateLayout.signature frame.inst (WNear.Binary.AllocateLayout.function message location previous) post hm hfi hf rfl hd
  have ac : activationGas op (wasmLocals (WNear.Binary.AllocateLayout.function message location previous) [.i32 p.out,.i32 p.input]) = 10 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.AllocateLayout.function,ValType.default]
  rw [ac] at cr
  have arrays : #[Value.i32 p.out,Value.i32 p.input] ++ #[Value.i32 0,Value.i32 0] = #[Value.i32 p.out,Value.i32 p.input,Value.i32 0,Value.i32 0] := by
    apply Array.toList_inj.mp; simp
  have bc : WP cfg ((fuel + 1) + 34) (.next (wasmCallee active limits base frame callers code WNear.Binary.AllocateLayout.signature frame.inst
      (WNear.Binary.AllocateLayout.function message location previous) [.i32 p.out,.i32 p.input])) (33 * op + rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateLayout.function,WNear.Binary.AllocateLayout.signature,leaf,saved,atCode,
      List.map_cons,List.map_nil,ValType.default,arrays,List.append_nil,List.length_nil] using b
  have r := cr (hc.mono (by dsimp [op]; omega)) bc
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (10 * op + (33 * op + rest)) = 44 * cfg.regularOpCost + rest by dsimp [op]; omega] using r

end WNear.Proofs.AllocateLayout
