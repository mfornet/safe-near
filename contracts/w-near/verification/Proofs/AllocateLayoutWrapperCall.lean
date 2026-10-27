import Proofs.AllocateLayoutWrapperBody

/-! Actual typed normal calls to the alignment-one layout wrappers f752/f685. -/
namespace WNear.Proofs.AllocateLayoutWrapper
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384
set_option maxHeartbeats 400000
attribute [local irreducible] WP readI32 writeI32 after

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def called (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p
def leafFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.out,.i32 p.size,.i32 0],inst,arity := 0,height,labels := [],code := []}

theorem ready_entered (s : Store NearState) (op : Nat) (frame : CallFrame) (p : Layout) (hr : Ready s frame p) :
    Ready (entered s op) frame p := by
  exact {hr with module := hr.module,global := hr.global,memory := hr.memory,function := hr.function}

theorem called_credits (s : Store NearState) (op rest : Nat) (p : Layout) (hc : s.host.gas.Credits (78 * op + rest)) :
    (called s op p).host.gas.Credits rest := by
  have co := StorePair.charged_credits s op (10 * op + (67 * op + rest)) (hc.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore s op) (10 * op) (67 * op + rest) co
  exact after_credits (entered s op) op rest p ca

/-- Installed wrapper and leaf descriptors, original native stack/output
spans and credits suffice for the complete local call. Both helpers execute. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (functionIndex address : Nat) (post : Post)
    (hr : Ready s (leafFrame frame.inst base.length p) p)
    (hfi : p.mi.funcAddrs[functionIndex]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.AllocateLayout.signature frame.inst (WNear.Binary.AllocateLayout.wrapper p.calleeIndex)))
    (hd : callers.length + 2 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (78 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (called s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 61) (.next (atCode s limits (base ++ [Value.i32 p.out,.i32 p.size]).toArray frame callers
      (.call functionIndex :: code))) (78 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := leafFrame frame.inst base.length p
  let saved := {frame with code}
  have co := StorePair.charged_credits s op (10 * op + (67 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (67 * op + rest) := StorePair.charged_credits (chargedStore s op) (10 * op) (67 * op + rest) co
  have r := ready_entered s op leaf p hr
  have ln : WP cfg fuel (.next (atCode (called s op p) limits (base ++ []).toArray saved callers saved.code)) rest post := by
    simpa only [saved,atCode,List.append_nil,op] using hnext
  have left := wp_leave_wasm cfg fuel rest (called s op p) limits base [] (afterFrame leaf p) saved callers post rfl rfl rfl
    (called_credits s op rest p hc) ln
  have bn : WP cfg (fuel + 1) (.next (atCode (after active op p) limits base.toArray (afterFrame leaf p) (saved :: callers) [])) rest post := by
    simpa only [called,active,List.append_nil] using left
  have b := wp_body cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] p post r (by simpa only [List.length_cons] using hd) ca bn
  have cr := wp_call_wasm cfg ((fuel + 1) + 59) (67 * op + rest) s limits base [.i32 p.out,.i32 p.size] frame callers code functionIndex address p.mi
    WNear.Binary.AllocateLayout.signature frame.inst (WNear.Binary.AllocateLayout.wrapper p.calleeIndex) post hr.module hfi hf rfl (by omega)
  have ac : activationGas op (wasmLocals (WNear.Binary.AllocateLayout.wrapper p.calleeIndex) [.i32 p.out,.i32 p.size]) = 10 * op := by
    simp [activationGas,wasmLocals,WNear.Binary.AllocateLayout.wrapper,ValType.default]
  rw [ac] at cr
  have arrays : #[Value.i32 p.out,Value.i32 p.size] ++ #[Value.i32 0] = #[Value.i32 p.out,Value.i32 p.size,Value.i32 0] := by
    apply Array.toList_inj.mp; simp
  have bc : WP cfg ((fuel + 1) + 59) (.next (wasmCallee active limits base frame callers code WNear.Binary.AllocateLayout.signature frame.inst
      (WNear.Binary.AllocateLayout.wrapper p.calleeIndex) [.i32 p.out,.i32 p.size])) (67 * op + rest) post := by
    simpa only [wasmCallee,wasmLocals,WNear.Binary.AllocateLayout.wrapper,WNear.Binary.AllocateLayout.signature,leaf,leafFrame,saved,atCode,
      List.map_cons,List.map_nil,ValType.default,arrays,List.append_nil,List.length_nil] using b
  have result := cr (hc.mono (by dsimp [op]; omega)) bc
  simpa only [Nat.add_assoc,Nat.reduceAdd,
    show cfg.regularOpCost + (10 * op + (67 * op + rest)) = 78 * cfg.regularOpCost + rest by dsimp [op]; omega] using result

end WNear.Proofs.AllocateLayoutWrapper
