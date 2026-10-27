import Proofs.InterfaceLazyComplete
import NearVM.MeteredWasmCall

/-! Typed local invocation of the deployed lazy initializer f467. -/
namespace WNear.Proofs.InterfaceLazyCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
open InterfaceLazyComplete (Layout)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000

/-- The final scalar phases charge twelve units; changing the global leaves
both gas-credit bounds intact. -/
theorem finish_credits (s : Store NearState) (op rest : Nat) (p : InterfaceLazyState.Layout)
    (hc : s.host.gas.Credits (12 * op + rest)) :
    (InterfaceLazyState.finalStore s op p).host.gas.Credits rest := by
  have c4 := paid_credits s op 4 (8 * op + rest) (hc.mono (by omega))
  have c3 := paid_credits (paid s op 4) op 3 (5 * op + rest) (c4.mono (by omega))
  have c4' := paid_credits (paid (paid s op 4) op 3) op 4 (op + rest) (c3.mono (by omega))
  have cg : (setGlobal (paid (paid (paid s op 4) op 3) op 4) p.globalIndex (.i32 (p.scratch + 48))).host.gas.Credits (op + rest) := by
    simpa only [setGlobal] using c4'
  have c1 := paid_credits (setGlobal (paid (paid (paid s op 4) op 3) op 4) p.globalIndex (.i32 (p.scratch + 48))) op 1 rest (cg.mono (by omega))
  simpa only [InterfaceLazyState.finalStore, InterfaceLazyFinish.finalStore] using c1

theorem tail_credits (s : Store NearState) (op rest : Nat) (p : InterfaceLazyState.Layout)
    (hc : s.host.gas.Credits (50 * op + rest)) :
    (InterfaceLazyTail.after s op p).host.gas.Credits rest := by
  have high := InterfaceLazyState.high_credits s op (43 * op + rest) p (hc.mono (by omega))
  have word := InterfaceLazyState.word_credits (InterfaceLazyState.high s op p) op (31 * op + rest) p (high.mono (by omega))
  have status := InterfaceLazyState.status_credits (InterfaceLazyState.word (InterfaceLazyState.high s op p) op p) op (25 * op + rest) p (word.mono (by omega))
  have saved := InterfaceLazyState.saved_credits (InterfaceLazyState.status (InterfaceLazyState.word (InterfaceLazyState.high s op p) op p) op p) op (12 * op + rest) p (status.mono (by omega))
  have finished := finish_credits (InterfaceLazyState.saved (InterfaceLazyState.status (InterfaceLazyState.word (InterfaceLazyState.high s op p) op p) op p) op p) op rest p saved
  simpa only [InterfaceLazyTail.after, InterfaceLazyTail.wordAfter, InterfaceLazyTail.statusAfter, InterfaceLazySavedTail.after] using finished

theorem after_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (70 * op + rest)) :
    (InterfaceLazyComplete.after s op p).host.gas.Credits rest := by
  have reserve : (InterfaceLazyComplete.reserved s op p).host.gas.Credits (65 * op + rest) := by
    simpa only [InterfaceLazyComplete.reserved, setGlobal] using paid_credits s op 5 (65 * op + rest) (hc.mono (show 5 * op + (65 * op + rest) ≤ 70 * op + rest by omega))
  have init := InterfaceLazyPrefix.after_credits (InterfaceLazyComplete.reserved s op p) op p.memoryIndex (50 * op + rest)
    (InterfaceLazyComplete.scratch p) p.memory (reserve.mono (by omega))
  exact tail_credits (InterfaceLazyComplete.initialized s op p) op rest (InterfaceLazyComplete.tailLayout p) init

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (11 * op)
def after (s : Store NearState) (op : Nat) (p : Layout) := InterfaceLazyComplete.after (entered s op) op p

def calleeFrame (inst height : Nat) (p : Layout) : CallFrame :=
  {locals := #[.i32 p.cell, .i32 p.location, .i32 0, .i64 0, .i32 0]
   inst
   arity := 1
   height
   labels := []
   code := []}

/-- Structural initialization obligations at a typed f467 entry. They describe
actual tables, code, memory and bounds rather than a callee execution result. -/
def Ready (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (base : List Value) (code : List Instr) (p : Layout) : Prop :=
  InterfaceLazyComplete.Ready s limits (calleeFrame frame.inst base.length p) ({frame with code} :: callers) p

theorem entered_ready (s : Store NearState) (op : Nat) (limits : ExecLimits) (frame : CallFrame)
    (callers : List CallFrame) (p : Layout) (hr : InterfaceLazyComplete.Ready s limits frame callers p) :
    InterfaceLazyComplete.Ready (entered s op) limits frame callers p := by
  rcases hr with ⟨hm, hi, hg, hsp, hmi, hmem, hti, ht, he, hty, hf, hcell, hlocation, hn, hb, hd, htail⟩
  exact ⟨hm, hi, hg, hsp, hmi, hmem, hti, ht, he, hty, hf, hcell, hlocation, hn, hb, hd, htail⟩

theorem after_credits_call (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (82 * op + rest)) : (after s op p).host.gas.Credits rest := by
  have hop := WNear.Proofs.StorePair.charged_credits s op (11 * op + (70 * op + rest)) (hc.mono (by omega))
  have activation := WNear.Proofs.StorePair.charged_credits (chargedStore s op) (11 * op) (70 * op + rest) hop
  exact after_credits (entered s op) op rest p activation

/-- Actual f467 direct call, its initializer table call, and the typed return. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (p : Layout) (address : Nat) (post : Post)
    (hr : Ready s limits frame callers base code p)
    (haddress : p.mi.funcAddrs[467]? = some address)
    (hfunction : s.funcs[address]? = some (.wasm WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function))
    (hc : s.host.gas.Credits (82 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (after s cfg.regularOpCost p) limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 65) (.next (atCode s limits (base ++ [Value.i32 p.cell, .i32 p.location]).toArray
      frame callers (.call 467 :: code))) (82 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let leaf := calleeFrame frame.inst base.length p
  let saved := {frame with code}
  have r : InterfaceLazyComplete.Ready active limits leaf (saved :: callers) p := entered_ready s op limits leaf (saved :: callers) p hr
  have cp : active.host.gas.Credits (70 * op + rest) := by
    have hop := WNear.Proofs.StorePair.charged_credits s op (11 * op + (70 * op + rest)) (hc.mono (by dsimp [op]; omega))
    exact WNear.Proofs.StorePair.charged_credits (chargedStore s op) (11 * op) (70 * op + rest) hop
  have cf := after_credits_call s op rest p hc
  have hArity : [Value.i32 (p.cell + 4)].length = (InterfaceLazyComplete.afterFrame leaf p).arity := rfl
  have hHeight : (InterfaceLazyComplete.afterFrame leaf p).height = base.length := rfl
  have hLabels : (InterfaceLazyComplete.afterFrame leaf p).labels = [] := rfl
  have leaveRule := wp_leave_wasm cfg fuel rest (after s op p) limits base [.i32 (p.cell + 4)]
    (InterfaceLazyComplete.afterFrame leaf p) saved callers post hArity hHeight hLabels cf
  have leaveNext : WP cfg fuel (.next (atCode (after s op p) limits
      (base ++ [Value.i32 (p.cell + 4)]).toArray saved callers saved.code)) rest post := by
    simpa only [saved, atCode] using hnext
  have leave := leaveRule leaveNext
  have array : (base ++ [Value.i32 (p.cell + 4)]).toArray = base.toArray.push (.i32 (p.cell + 4)) := by
    apply Array.toList_inj.mp; simp
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (InterfaceLazyComplete.after active op p) limits
      (base.toArray.push (.i32 (p.cell + 4))) (InterfaceLazyComplete.afterFrame leaf p) (saved :: callers) [])) rest post := by
    simpa only [after, active, array] using leave
  have bodyRule := InterfaceLazyComplete.wp_body cfg (fuel + 1) rest active limits base leaf (saved :: callers) [] p post r cp
  have body := bodyRule bodyNext
  have activation : activationGas op (wasmLocals WNear.Binary.InterfaceLazy.function [.i32 p.cell, .i32 p.location]) = 11 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.InterfaceLazy.function, ValType.default]
  have depth : callers.length + 1 < limits.maxCallDepth := by have hd := r.depth; simp only [List.length_cons] at hd; omega
  have hm : s.modules[frame.inst]? = some p.mi := by simpa only [Ready, calleeFrame] using hr.module
  have callRule := wp_call_wasm cfg ((fuel + 1) + 63) (70 * op + rest) s limits base [.i32 p.cell, .i32 p.location]
    frame callers code 467 address p.mi WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function post hm haddress hfunction rfl depth
  rw [activation] at callRule
  have localsArray : #[Value.i32 p.cell, .i32 p.location] ++ #[Value.i32 0, .i64 0, .i32 0] = #[Value.i32 p.cell, .i32 p.location, .i32 0, .i64 0, .i32 0] := rfl
  have next : WP cfg ((fuel + 1) + 63) (.next (wasmCallee active limits base frame callers code
      WNear.Binary.InterfaceLazy.signature frame.inst WNear.Binary.InterfaceLazy.function [.i32 p.cell, .i32 p.location])) (70 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.InterfaceLazy.function, WNear.Binary.InterfaceLazy.signature,
      atCode, leaf, calleeFrame, saved, List.map_cons, List.map_nil, ValType.default, List.append_cons, List.append_nil,
      Array.toArray_toList, List.length_cons, List.length_nil, localsArray, Nat.reduceAdd, op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  rw [show cfg.regularOpCost + (11 * op + (70 * op + rest)) = 82 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd] using result

end WNear.Proofs.InterfaceLazyCall
