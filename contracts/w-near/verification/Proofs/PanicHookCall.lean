import Proofs.PanicHookState
import Proofs.PanicHookBody
import Proofs.TotalSupply

/-! Actual panic-hook local call and the total-supply callee contract. -/
namespace WNear.Proofs.PanicHookCall
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas)
open PanicHookState (Layout)
set_option maxRecDepth 16384
set_option maxHeartbeats 300000
attribute [local irreducible] WP

/-- Actual original-store code/native facts; no callee result is assumed. -/
structure Resources (s : Store NearState) (limits : ExecLimits) (frame : CallFrame) (p : Layout) : Prop where
  native : PanicHookState.Ready s limits frame.inst 2 p
  function : ∃ address, p.mi.funcAddrs[522]? = some address ∧ s.funcs[address]? = some
    (.wasm WNear.Binary.PanicHook.signature frame.inst WNear.Binary.PanicHook.function)

def entered (s : Store NearState) (op : Nat) := chargedStore (chargedStore s op) (8 * op)
def calledAfter (s : Store NearState) (op : Nat) (p : Layout) := PanicHookState.after (entered s op) op p

theorem calledAfter_credits (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (140 * op + rest)) : (calledAfter s op p).host.gas.Credits rest := by
  have hop := StorePair.charged_credits s op (8 * op + (131 * op + rest)) (hc.mono (by omega))
  have activation := StorePair.charged_credits (chargedStore s op) (8 * op) (131 * op + rest) hop
  exact PanicHookState.after_credits (entered s op) op rest p activation

private theorem charge_burnt (s : Store NearState) (cost : Nat) :
    (chargedStore s cost).host.gas.burnt = (s.host.gas.burn cost).1.burnt := rfl

private theorem allocated_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (88 * op + rest)) :
    (PanicHookState.allocated s op p).host.gas.burnt = s.host.gas.burnt + 88 * op ∧
    (PanicHookState.allocated s op p).host.gas.promises = s.host.gas.promises := by
  have c2 := paid_credits s op 2 (86 * op + rest) (hc.mono (by omega))
  have p2 := paid_gas s op 2 (86 * op + rest) (hc.mono (by omega))
  have hop := GasCounter.burn_credits (paid s op 2).host.gas op (85 * op + rest) (c2.mono (by omega))
  have activation := GasCounter.burn_credits (chargedStore (paid s op 2) op).host.gas (10 * op) (75 * op + rest) (hop.2.2.2.mono (by omega))
  have body := PanicAllocatePointerState.after_gas (PanicHookState.allocationEntry (paid s op 2) op) op rest p activation.2.2.2
  refine ⟨?_, body.2.1.trans (activation.2.2.1.trans (hop.2.2.1.trans p2.2))⟩
  change (PanicAllocatePointerState.after (PanicHookState.allocationEntry (paid s op 2) op) op p).host.gas.burnt = _
  rw [body.1]
  change (chargedStore (chargedStore (paid s op 2) op) (10 * op)).host.gas.burnt + 75 * op = _
  rw [charge_burnt, activation.2.1, charge_burnt, hop.2.1, p2.1]; omega

theorem bodyAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (131 * op + rest)) :
    (PanicHookState.after s op p).host.gas.burnt = s.host.gas.burnt + 131 * op ∧
    (PanicHookState.after s op p).host.gas.promises = s.host.gas.promises := by
  have allocation := allocated_gas s op (43 * op + rest) p (hc.mono (by omega))
  have ca := PanicHookState.allocated_credits s op (43 * op + rest) p (hc.mono (by omega))
  have arg := paid_gas (PanicHookState.allocated s op p) op 1 (42 * op + rest) (ca.mono (by omega))
  have carg : (PanicHookState.hookArguments s op p).host.gas.Credits (42 * op + rest) :=
    paid_credits (PanicHookState.allocated s op p) op 1 (42 * op + rest) (ca.mono (by omega))
  have hop := GasCounter.burn_credits (PanicHookState.hookArguments s op p).host.gas op (41 * op + rest) (carg.mono (by omega))
  have activation := GasCounter.burn_credits (chargedStore (PanicHookState.hookArguments s op p) op).host.gas (10 * op) (31 * op + rest) (hop.2.2.2.mono (by omega))
  have hook := paid_gas (PanicHookState.hookEntry (PanicHookState.hookArguments s op p) op) op 31 rest activation.2.2.2
  have result : (PanicHookState.after s op p).host =
      (paid (PanicHookState.hookEntry (PanicHookState.hookArguments s op p) op) op 31).host := by
    exact PanicHookSet.after_host _ op p.memoryIndex (PanicAllocatePointerState.finalMemory p) 1 1055136
  have gas := congrArg (fun h => h.gas) result
  rw [gas]
  refine ⟨?_, hook.2.trans (activation.2.2.1.trans (hop.2.2.1.trans (arg.2.trans allocation.2)))⟩
  rw [hook.1]
  change (chargedStore (chargedStore (PanicHookState.hookArguments s op p) op) (10 * op)).host.gas.burnt + 31 * op = _
  rw [charge_burnt, activation.2.1, charge_burnt, hop.2.1]
  change (paid (PanicHookState.allocated s op p) op 1).host.gas.burnt + op + 10 * op + 31 * op = _
  rw [arg.1, allocation.1]; omega

theorem calledAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (140 * op + rest)) :
    (calledAfter s op p).host.gas.burnt = s.host.gas.burnt + 140 * op ∧
    (calledAfter s op p).host.gas.promises = s.host.gas.promises := by
  have hop := GasCounter.burn_credits s.host.gas op (139 * op + rest) (hc.mono (by omega))
  have activation := GasCounter.burn_credits (chargedStore s op).host.gas (8 * op) (131 * op + rest) (hop.2.2.2.mono (by omega))
  have body := bodyAfter_gas (entered s op) op rest p activation.2.2.2
  refine ⟨?_, body.2.trans (activation.2.2.1.trans hop.2.2.1)⟩
  change (PanicHookState.after (entered s op) op p).host.gas.burnt = _
  rw [body.1]
  change (chargedStore (chargedStore s op) (8 * op)).host.gas.burnt + 131 * op = _
  rw [charge_burnt, activation.2.1, charge_burnt, hop.2.1]; omega

/-- The complete actual522 local call, including activation and its free
normal return, resumes the original caller at the untouched suffix. -/
theorem wp_call (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (frame : CallFrame) (code : List Instr) (p : Layout) (post : Post)
    (hr : Resources s limits frame p)
    (hc : s.host.gas.Credits (140 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (calledAfter s cfg.regularOpCost p) limits #[] frame [] code)) rest post) :
    WP cfg (fuel + 104) (.next (atCode s limits #[] frame [] (.call 522 :: code))) (140 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  let active := entered s op
  let callee : CallFrame := {locals := #[], inst := frame.inst, arity := 0, height := 0, labels := [], code := []}
  let saved := {frame with code}
  have r0 := hr.native.charge s op limits frame.inst 2 p
  have r1 := r0.charge (chargedStore s op) (8 * op) limits frame.inst 2 p
  have ready : PanicHookState.Ready active limits callee.inst ([saved].length + 1) p := by
    simpa only [active, entered, callee, List.length_cons, List.length_nil, Nat.reduceAdd] using r1
  have hop := StorePair.charged_credits s op (8 * op + (131 * op + rest)) (hc.mono (by dsimp [op]; omega))
  have ca : active.host.gas.Credits (131 * op + rest) := StorePair.charged_credits (chargedStore s op) (8 * op) (131 * op + rest) hop
  have cf := calledAfter_credits s op rest p hc
  have leaveRule := wp_leave_wasm cfg fuel rest (calledAfter s op p) limits [] [] callee saved [] post rfl rfl rfl cf
  have leaveNext : WP cfg fuel (.next (atCode (calledAfter s op p) limits #[] saved [] saved.code)) rest post := by
    simpa only [saved, atCode, op] using hnext
  have leaving := leaveRule leaveNext
  have bodyRule := PanicHookBody.wp_body cfg (fuel + 1) rest active limits [] callee [saved] [] p post ready ca
  have bodyNext : WP cfg (fuel + 1) (.next (atCode (PanicHookState.after active op p) limits #[] callee [saved] [])) rest post := by
    simpa only [calledAfter, active, List.append_nil] using leaving
  have body := bodyRule bodyNext
  rcases hr.function with ⟨address, hi, hf⟩
  have depth : 1 < limits.maxCallDepth := by have hd := hr.native.depth; omega
  have callRule := wp_call_wasm cfg ((fuel + 1) + 102) (131 * op + rest) s limits [] [] frame [] code 522 address p.mi
    WNear.Binary.PanicHook.signature frame.inst WNear.Binary.PanicHook.function post hr.native.module hi hf rfl depth
  have activation : activationGas op (wasmLocals WNear.Binary.PanicHook.function []) = 8 * op := by
    simp [activationGas, wasmLocals, WNear.Binary.PanicHook.function]
  rw [activation] at callRule
  have next : WP cfg ((fuel + 1) + 102) (.next (wasmCallee active limits [] frame [] code WNear.Binary.PanicHook.signature frame.inst WNear.Binary.PanicHook.function []))
      (131 * op + rest) post := by
    simpa only [wasmCallee, wasmLocals, WNear.Binary.PanicHook.function, WNear.Binary.PanicHook.signature, atCode, callee, saved,
      List.map_nil, List.append_nil, Array.append_empty, List.length_nil, op] using body
  have result := callRule (hc.mono (by dsimp [op]; omega)) next
  rw [show cfg.regularOpCost + (8 * op + (131 * op + rest)) = 140 * cfg.regularOpCost + rest by dsimp [op]; omega] at result
  simpa only [Nat.add_assoc, Nat.reduceAdd, List.append_nil] using result

/-- Actual panic-hook setup discharges its local total-supply callee contract.
All component calls are proved from the original resource record. -/
theorem calleeContract (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits) (frame : CallFrame)
    (p : Layout) (hr : Resources s limits frame p) :
    TotalSupply.CalleeContract cfg limits frame 522 [] s (calledAfter s cfg.regularOpCost p) (140 * cfg.regularOpCost) 104 := by
  constructor
  · intro rest hc
    exact calledAfter_credits s cfg.regularOpCost rest p hc
  · intro fuel rest code post hc hnext
    exact wp_call cfg fuel rest s limits frame code p post hr hc hnext

end WNear.Proofs.PanicHookCall
