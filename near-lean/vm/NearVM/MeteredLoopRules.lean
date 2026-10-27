import NearVM.MeteredControlRules

/-! Actual loop and conditional-branch steps, including paid loop backedges. -/
namespace Wasm.Near.MeteredLogic

def emptyLoopFrame (frame : CallFrame) (height : Nat) (body code : List Instr) : CallFrame :=
  {frame with labels := {arity := 0, height, rest := code, loop := some body} :: frame.labels}

theorem wp_loop_empty (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (body code : List Instr) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits stack
      (emptyLoopFrame frame stack.size body code) callers body)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack frame callers (.loop .empty body :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits stack frame callers (.loop .empty body :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack
        (emptyLoopFrame frame stack.size body code) callers body) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.blockType, Exec.Effect.continue,
      c, atCode, emptyLoopFrame, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c, emptyLoopFrame]
  · rw [← hcost, hstep]; exact hnext

theorem wp_br_if_loop_nonzero (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (body code discarded : List Instr) (condition : UInt32) (post : Post)
    (hcondition : condition ≠ 0)
    (hcredits : store.host.gas.Credits ((2 * cfg.regularOpCost) + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store (2 * cfg.regularOpCost)) limits
      stack (emptyLoopFrame frame stack.size body code) callers body)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 condition))
      (emptyLoopFrame frame stack.size body code) callers (.br_if 0 :: discarded)))
      ((2 * cfg.regularOpCost) + rest) post := by
  let c := atCode store limits (stack.push (.i32 condition))
    (emptyLoopFrame frame stack.size body code) callers (.br_if 0 :: discarded)
  have hcost : nextInstructionGas cfg c = (2 * cfg.regularOpCost) := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge,
      Config.stackTop?, Config.labelIsLoop, emptyLoopFrame, hcondition]
    omega
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store (2 * cfg.regularOpCost)) limits stack (emptyLoopFrame frame stack.size body code) callers body) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, Exec.branch, Exec.popN,
      c, atCode, chargeConfig, chargedStore, emptyLoopFrame, hcondition]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c, emptyLoopFrame]
  · rw [← hcost, hstep]; exact hnext

theorem wp_br_if_zero (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (depth : Nat) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits stack
      frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 0)) frame callers (.br_if depth :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i32 0)) frame callers (.br_if depth :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge, Config.stackTop?]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Falling through a block or loop label consumes a step and no gas. -/
theorem wp_end_label (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (label : Label) (post : Post)
    (hc : store.host.gas.Credits rest)
    (hnext : WP cfg fuel (.next (atCode store limits stack frame callers label.rest)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack
      {frame with labels := label :: frame.labels} callers [])) rest post := by
  let c := atCode store limits stack {frame with labels := label :: frame.labels} callers []
  have hz := chargeWasm_zero (.next c) (hc.mono (Nat.zero_le rest))
  have hcharge : chargeConfig c 0 = (c, none) := by
    cases he : chargeConfig c 0 with
    | mk c' error =>
      simp only [chargeWasm, he] at hz
      cases hz
      rfl
  have hcost : nextInstructionGas cfg c = 0 := rfl
  have hstep : Exec.step c = .next (atCode store limits stack frame callers label.rest) := by
    simp [Exec.step, c, atCode]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost, hcharge, hstep] at h
  simp only [Nat.zero_add] at h
  apply h hc
  · rfl
  · simp [frameTransitionGas, Config.callDepth, c, atCode]
  · exact hnext

end Wasm.Near.MeteredLogic
