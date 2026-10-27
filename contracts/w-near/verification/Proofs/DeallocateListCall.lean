import Proofs.DeallocateListBody
import NearVM.MeteredWasmCall

/-! Actual typed call to f575 on its captured two-link path. -/
namespace WNear.Proofs.DeallocateListCall
open Wasm Wasm.Near MeteredLogic
open DeallocateListState
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP after firstStore secondStore secondAfter readI32 writeI32

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (10 * op)
def called (s : Store NearState) (op : Nat) (p : Layout) := after (entered s op) op p

theorem called_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (72 * op + rest)) : (called s op p).host.gas.Credits rest := by
  have co := StorePair.charged_credits s op (10 * op + (61 * op + rest)) (hc.mono (by omega))
  have ca := StorePair.charged_credits (chargedStore s op) (10 * op) (61 * op + rest) co
  exact after_credits (entered s op) op rest p ca

/-- Original native heap data, typed linkage and call depth suffice. No
successful invocation or post-memory equality is assumed. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hm : s.modules[frame.inst]? = some p.mi) (hfi : p.mi.funcAddrs[575]? = some address)
    (hf : s.funcs[address]? = some (.wasm WNear.Binary.DeallocateList.unlinkSignature frame.inst WNear.Binary.DeallocateList.unlinkFunction))
    (hi : p.mi.memAddrs[0]? = some p.memoryIndex) (hmem : s.mems[p.memoryIndex]? = some p.memory)
    (hw : p.memory.wf) (hb : p.pointer.toNat + 8 ≤ p.memory.byteSize)
    (hfn : firstLink p ≠ 0) (hflag : firstRaw p &&& 2 = 0)
    (hfb : (firstLink p).toNat + 8 ≤ p.memory.byteSize)
    (hsn : secondLink p ≠ 0) (hsb : (secondLink p).toNat + 4 ≤ (firstMemory p).byteSize)
    (hd : callers.length + 1 < limits.maxCallDepth)
    (hc : s.host.gas.Credits (72 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (called s cfg.regularOpCost p) limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 67) (.next (atCode s limits (base ++ [Value.i32 p.pointer]).toArray frame callers (.call 575 :: code)))
      (72 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf : CallFrame := {locals := #[.i32 p.pointer, .i32 0, .i32 0], inst := frame.inst, arity := 0, height := base.length, labels := [], code := []}
  let saved := {frame with code}
  have co := StorePair.charged_credits s op (10 * op + (61 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (61 * op + rest) := StorePair.charged_credits (chargedStore s op) (10 * op) (61 * op + rest) co
  have hr : Ready active leaf p := by
    constructor
    · simpa only [active, entered, chargedStore, leaf] using hm
    · exact hi
    · simpa only [active, entered, chargedStore] using hmem
    · rfl
    · simp [leaf]
    · exact hw
    · exact hb
    · exact hfn
    · exact hflag
    · exact hfb
    · exact hsn
    · exact hsb
  have resume : WP cfg fuel (.next (atCode (after active op p) limits base.toArray saved callers saved.code)) rest post := by
    simpa only [called, active, saved, op, atCode] using hnext
  have leave := wp_leave_wasm cfg fuel rest (after active op p) limits base [] (finalFrame leaf p) saved callers post
    rfl rfl rfl (after_credits active op rest p ca) (by simpa only [List.append_nil] using resume)
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (after active op p) limits base.toArray (finalFrame leaf p) (saved :: callers) [])) rest post := by
    simpa only [List.append_nil] using leave
  have body := DeallocateListBody.wp_body cfg (fuel + 1) rest active limits base.toArray leaf (saved :: callers) [] p post hr ca bodyNext
  have callRule := wp_call_wasm cfg (fuel + 66) (61 * op + rest) s limits base [.i32 p.pointer] frame callers code 575 address p.mi
    WNear.Binary.DeallocateList.unlinkSignature frame.inst WNear.Binary.DeallocateList.unlinkFunction post hm hfi hf rfl hd
  have ha : activationGas op (wasmLocals WNear.Binary.DeallocateList.unlinkFunction [.i32 p.pointer]) = 10 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.DeallocateList.unlinkFunction, ValType.default]
  rw [ha] at callRule
  have castBody : WP cfg (fuel + 66) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.DeallocateList.unlinkSignature frame.inst WNear.Binary.DeallocateList.unlinkFunction [.i32 p.pointer])) (61 * op + rest) post := by
    simpa [wasmCallee, wasmLocals, WNear.Binary.DeallocateList.unlinkSignature, WNear.Binary.DeallocateList.unlinkFunction,
      atCode, leaf, saved, ValType.default] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) castBody
  have ge : cfg.regularOpCost + (10 * op + (61 * op + rest)) = 72 * cfg.regularOpCost + rest := by dsimp [op]; omega
  exact ValueReturnOuterBody.cast_phase cfg _ _ _ _ s limits (base ++ [Value.i32 p.pointer]).toArray frame callers _ _ post rfl ge rfl result

end WNear.Proofs.DeallocateListCall
