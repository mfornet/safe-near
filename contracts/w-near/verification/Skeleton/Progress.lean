import Skeleton.BudgetSimulation

/-!
# Structural termination of the actual walking body

Each continuing, error-free transition consumes one instruction. Host traps
terminate immediately; no correctness or gas-sufficiency premise about a host
is needed for the body to finish within sixteen transitions.
-/
namespace WNear.Skeleton.Progress
open Wasm Wasm.Near MeteredLogic MeteredPrefix MeteredPureBudget MeteredHostBudget
open BudgetSimulation

/-- Remaining instructions plus the administrative leave transition. -/
def rank : Machine → Nat
  | .next c => match c.thread.frames with | [] => 0 | frame :: _ => frame.code.length + 1
  | .done _ _ | .trap _ _ => 0

@[simp] theorem rank_atCode (store : Store NearState) (limits : ExecLimits)
    (stack : Array Value) (code : List Instr) :
    rank (.next (atCode store limits stack saveFrame [] code)) = code.length + 1 := rfl

private theorem pure_progress (cfg : WasmConfig) (op : PureOp) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (code : List Instr)
    (h : (advance cfg (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).2 = none) :
    rank (advance cfg (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1 <
      rank (.next (atCode store limits stack saveFrame [] (op.instr :: code))) := by
  rw [advance_pure] at h ⊢
  cases he : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => simp [he] at h
  | none => simp [chargeWasm, chargeConfig, rank, atCode]

private theorem call_progress (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (index addr : Nat) (fn : NearHostFn NearState)
    (input : List Value) (code : List Instr)
    (haddr : moduleInstance.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn)) (hargs : input.length = fn.params.length)
    (h : (advance cfg.wasm (.next (atCode store limits input.toArray saveFrame [] (.call index :: code)))).2 = none) :
    rank (advance cfg.wasm (.next (atCode store limits input.toArray saveFrame [] (.call index :: code)))).1 <
      rank (.next (atCode store limits input.toArray saveFrame [] (.call index :: code))) := by
  have ha := advance_host cfg.wasm store moduleInstance limits [] input saveFrame [] code
    index addr fn hi.module haddr hfn hargs
  simp only [List.nil_append] at ha
  rw [ha] at h ⊢
  cases he : (chargeHost store.host cfg.wasm.regularOpCost).2 with
  | some error => simp [he] at h
  | none =>
    simp only [he] at h ⊢
    cases hr : fn.invoke (hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) input <;>
      simp [callResult, chargeWasm, chargeConfig, rank, atCode]

/-- A successful runner transition strictly decreases the actual control rank,
even if the raw host itself rejects the call or the trie is malformed. -/
theorem phase_progress (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64)
    (h : (advance cfg.wasm (phaseMachine store limits pc.val written)).2 = none) :
    rank (advance cfg.wasm (phaseMachine store limits pc.val written)).1 <
      rank (phaseMachine store limits pc.val written) := by
  fin_cases pc
  all_goals simp only [phaseMachine] at h ⊢
  · exact pure_progress cfg.wasm (.i64const 0) store limits _ _ h
  · exact call_progress cfg store hi limits 0 0 _ [.i64 0] _ rfl hi.input rfl h
  · exact pure_progress cfg.wasm (.i64const 1) store limits _ _ h
  · exact pure_progress cfg.wasm (.i64const 0) store limits _ _ h
  · exact pure_progress cfg.wasm (.i64const u64Max) store limits _ _ h
  · exact pure_progress cfg.wasm (.i64const 0) store limits _ _ h
  · exact pure_progress cfg.wasm (.i64const u64Max) store limits _ _ h
  · exact call_progress cfg store hi limits 1 1 _ (MeteredHosts.StorageMetered.args 1 0 u64Max 0) _ rfl hi.storage rfl h
  · exact pure_progress cfg.wasm .drop store limits _ _ h
  · exact pure_progress cfg.wasm (.i64const 5) store limits _ _ h
  · exact pure_progress cfg.wasm (.i64const 1) store limits _ _ h
  · exact call_progress cfg store hi limits 2 2 _ [.i64 5, .i64 1] _ rfl hi.log rfl h
  · exact pure_progress cfg.wasm (.i64const u64Max) store limits _ _ h
  · exact pure_progress cfg.wasm (.i64const 0) store limits _ _ h
  · exact call_progress cfg store hi limits 3 3 _ [.i64 u64Max, .i64 0] _ rfl hi.returned rfl h
  · change rank (advance cfg.wasm (.next (atCode store limits #[] saveFrame [] []))).1 < 1
    change (advance cfg.wasm (.next (atCode store limits #[] saveFrame [] []))).2 = none at h
    simp only [advance, show nextInstructionGas cfg.wasm (atCode store limits #[] saveFrame [] []) = 0 from rfl] at h ⊢
    cases he : (chargeHost store.host 0).2 with
    | some error => simp [chargeConfig, atCode, he] at h
    | none => simp [chargeConfig, he, Exec.step, Exec.leave, atCode, saveFrame, chargeWasm, rank]

/-- The runner's own error channel contains only host gas errors. Host issues
are classified separately from the terminal trap's stored marker. -/
theorem advance_not_fuel (cfg : WasmConfig) (m : Machine) :
    (advance cfg m).2 ≠ some (.executionIssue .fuelExhausted) := by
  cases m with
  | done values store => simp [advance]
  | trap reason store => simp [advance]
  | next c =>
    simp only [advance]
    cases he : (chargeConfig c (nextInstructionGas cfg c)).2 with
    | some error => simp
    | none =>
      simp only
      cases (chargeWasm (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1)
        (frameTransitionGas cfg (chargeConfig c (nextInstructionGas cfg c)).1
          (Exec.step (chargeConfig c (nextInstructionGas cfg c)).1))).2 <;> simp

/-- Enough structural fuel excludes fuel exhaustion for every gas amount,
including gas stops and host rejections; no funded execution is assumed. -/
theorem run_not_fuel (cfg : RuntimeConfig) (limits : ExecLimits) (fuel : Nat) (m : Machine)
    (hm : Shape cfg limits m) (hbound : rank m ≤ fuel) :
    (runMetered cfg.wasm fuel m).2 ≠ some (.executionIssue .fuelExhausted) := by
  induction fuel generalizing m with
  | zero =>
    cases m with
    | done values store => simp [runMetered_done]
    | trap reason store => simp [runMetered_trapped]
    | next c =>
      obtain ⟨pc, written, store, rfl, _⟩ := hm
      simp [rank, atCode] at hbound
  | succ fuel ih =>
    cases m with
    | done values store => simp [runMetered_done]
    | trap reason store => simp [runMetered_trapped]
    | next c =>
      rw [run_succ]
      cases he : (advance cfg.wasm (.next c)).2 with
      | some error =>
        simpa only [he] using advance_not_fuel cfg.wasm (.next c)
      | none =>
        have hclosed := shape_advanceInvariant cfg limits (.next c) hm
        have hprogress : rank (advance cfg.wasm (.next c)).1 < rank (.next c) := by
          obtain ⟨pc, written, store, rfl, hi⟩ := hm
          exact phase_progress cfg store hi limits pc written he
        exact ih _ hclosed (by omega)

/-- The actual body always has sufficient fuel after at most sixteen steps. -/
theorem run_phase_not_fuel (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (fuel : Nat)
    (hbound : 16 - pc.val ≤ fuel) :
    (runMetered cfg.wasm fuel (phaseMachine store limits pc.val written)).2 ≠
      some (.executionIssue .fuelExhausted) := by
  apply run_not_fuel cfg limits fuel _
  · exact ⟨pc, written, store, rfl, hi⟩
  · simp only [phaseMachine, rank, atCode, phaseCode, List.length_drop]
    change 15 - pc.val + 1 ≤ fuel
    have hp := pc.isLt
    omega

end WNear.Skeleton.Progress
