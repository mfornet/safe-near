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

/-- Terminal outcomes need no next suffix; continuing frames have this exact code. -/
def CodeAfter (code : List Instr) : Machine → Prop
  | .next c => c.thread.frames = [{ saveFrame with code }]
  | .done _ _ | .trap _ _ => True

private theorem pure_code_after (cfg : WasmConfig) (op : PureOp) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (code : List Instr)
    (h : (advance cfg (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).2 = none) :
    CodeAfter code (advance cfg (.next (atCode store limits stack saveFrame [] (op.instr :: code)))).1 := by
  rw [advance_pure] at h ⊢
  cases he : (chargeHost store.host cfg.regularOpCost).2 with
  | some error => simp [he] at h
  | none => simp [chargeWasm, chargeConfig, CodeAfter, atCode]

private theorem call_code_after (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (index addr : Nat) (fn : NearHostFn NearState)
    (input : List Value) (code : List Instr)
    (haddr : moduleInstance.funcAddrs[index]? = some addr)
    (hfn : store.funcs[addr]? = some (.host fn.toHostFn)) (hargs : input.length = fn.params.length)
    (h : (advance cfg.wasm (.next (atCode store limits input.toArray saveFrame [] (.call index :: code)))).2 = none) :
    CodeAfter code (advance cfg.wasm (.next (atCode store limits input.toArray saveFrame [] (.call index :: code)))).1 := by
  have ha := advance_host cfg.wasm store moduleInstance limits [] input saveFrame [] code
    index addr fn hi.module haddr hfn hargs
  simp only [List.nil_append] at ha
  rw [ha] at h ⊢
  cases he : (chargeHost store.host cfg.wasm.regularOpCost).2 with
  | some error => simp [he] at h
  | none =>
    simp only [he] at h ⊢
    cases hr : fn.invoke (hostView (chargedStore store cfg.wasm.regularOpCost) moduleInstance) input <;>
      simp [callResult, chargeWasm, chargeConfig, CodeAfter, atCode]

/-- Every continuing transition has the exact next source-code suffix.
Same-phase charge failures are excluded by the actual error-channel premise. -/
theorem phase_code_after (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64)
    (h : (advance cfg.wasm (phaseMachine store limits pc.val written)).2 = none) :
    CodeAfter (phaseCode (pc.val + 1)) (advance cfg.wasm (phaseMachine store limits pc.val written)).1 := by
  fin_cases pc
  all_goals simp only [phaseMachine] at h ⊢
  · exact pure_code_after cfg.wasm (.i64const 0) store limits _ _ h
  · exact call_code_after cfg store hi limits 0 0 _ [.i64 0] _ rfl hi.input rfl h
  · exact pure_code_after cfg.wasm (.i64const 1) store limits _ _ h
  · exact pure_code_after cfg.wasm (.i64const 0) store limits _ _ h
  · exact pure_code_after cfg.wasm (.i64const u64Max) store limits _ _ h
  · exact pure_code_after cfg.wasm (.i64const 0) store limits _ _ h
  · exact pure_code_after cfg.wasm (.i64const u64Max) store limits _ _ h
  · exact call_code_after cfg store hi limits 1 1 _ (MeteredHosts.StorageMetered.args 1 0 u64Max 0) _ rfl hi.storage rfl h
  · exact pure_code_after cfg.wasm .drop store limits _ _ h
  · exact pure_code_after cfg.wasm (.i64const 5) store limits _ _ h
  · exact pure_code_after cfg.wasm (.i64const 1) store limits _ _ h
  · exact call_code_after cfg store hi limits 2 2 _ [.i64 5, .i64 1] _ rfl hi.log rfl h
  · exact pure_code_after cfg.wasm (.i64const u64Max) store limits _ _ h
  · exact pure_code_after cfg.wasm (.i64const 0) store limits _ _ h
  · exact call_code_after cfg store hi limits 3 3 _ [.i64 u64Max, .i64 0] _ rfl hi.returned rfl h
  · change CodeAfter [] (advance cfg.wasm (.next (atCode store limits #[] saveFrame [] []))).1
    change (advance cfg.wasm (.next (atCode store limits #[] saveFrame [] []))).2 = none at h
    simp only [advance, show nextInstructionGas cfg.wasm (atCode store limits #[] saveFrame [] []) = 0 from rfl] at h ⊢
    cases he : (chargeHost store.host 0).2 with
    | some error => simp [chargeConfig, atCode, he] at h
    | none => simp [chargeConfig, he, Exec.step, Exec.leave, atCode, saveFrame, chargeWasm, CodeAfter]

/-- Exact next phase, including the input/storage crossing points needed by
functional invariants. A continuing error-free step cannot skip or repeat code. -/
theorem phase_next (cfg : RuntimeConfig) (store : Store NearState) (hi : Installed cfg store)
    (limits : ExecLimits) (pc : Fin 16) (written : UInt64) (next : Config NearState)
    (herror : (advance cfg.wasm (phaseMachine store limits pc.val written)).2 = none)
    (hnext : (advance cfg.wasm (phaseMachine store limits pc.val written)).1 = .next next) :
    ∃ (index : Fin 16) (flag : UInt64) (after : Store NearState), index.val = pc.val + 1 ∧
      next = atCode after limits (phaseStack index.val flag) saveFrame [] (phaseCode index.val) ∧
      Installed cfg after := by
  have hs := phase_shape_closed cfg store hi limits pc written
  rw [hnext] at hs
  obtain ⟨index, flag, after, hn, ha⟩ := hs
  have hc := phase_code_after cfg store hi limits pc written herror
  rw [hnext] at hc
  change next.thread.frames = [{saveFrame with code := phaseCode (pc.val + 1)}] at hc
  rw [hn] at hc
  have hlen := congrArg (fun frames : List CallFrame => (frames.head?.map (fun frame => frame.code.length)).getD 0) hc
  change (phaseCode index.val).length = (phaseCode (pc.val + 1)).length at hlen
  simp only [phaseCode, List.length_drop] at hlen
  change 15 - index.val = 15 - (pc.val + 1) at hlen
  have hp := phase_progress cfg store hi limits pc written herror
  rw [hnext, hn] at hp
  simp only [phaseMachine, rank, atCode, phaseCode, List.length_drop] at hp
  change 15 - index.val + 1 < 15 - pc.val + 1 at hp
  have hpc := pc.isLt
  have hindex := index.isLt
  exact ⟨index, flag, after, by omega, hn, ha⟩

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

@[simp] theorem rank_charge (m : Machine) (cost : Nat) :
    rank (chargeWasm m cost).1 = rank m := by cases m <;> rfl

/-- Entry activation charges preserve the same concrete shape. -/
theorem shape_charge (cfg : RuntimeConfig) (limits : ExecLimits) (m : Machine) (cost : Nat)
    (hm : Shape cfg limits m) : Shape cfg limits (chargeWasm m cost).1 := by
  cases m with
  | done values store => trivial
  | trap reason store => trivial
  | next c =>
    obtain ⟨pc, written, store, rfl, hi⟩ := hm
    exact ⟨pc, written, chargedStore store cost, rfl, hi.charged cost⟩

/-- The real activation wrapper also cannot exhaust fuel, regardless of
whether its entry charge accepts. This does not change the guest context. -/
theorem runInitialized_not_fuel (cfg : RuntimeConfig) (limits : ExecLimits) (fuel : Nat)
    (m : Machine) (hm : Shape cfg limits m) (hbound : rank m ≤ fuel) :
    (runInitialized cfg.wasm fuel m).2 ≠ some (.executionIssue .fuelExhausted) := by
  unfold runInitialized
  cases he : (chargeWasm m (entryCost cfg.wasm m)).2 with
  | some error => simp [he]
  | none =>
    simp only [he]
    exact run_not_fuel cfg limits fuel _ (shape_charge cfg limits m _ hm)
      (by simpa only [rank_charge] using hbound)

end WNear.Skeleton.Progress
