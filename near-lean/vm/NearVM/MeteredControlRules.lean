import NearVM.MeteredRules

/-! Actual metered control steps used by the deployed accepted-result path.
Empty-result blocks cost no gas; branching to their end is not a loop backedge. -/
namespace Wasm.Near.MeteredLogic

/-- Enter a non-loop block whose branch result arity is zero. -/
def emptyBlockFrame (frame : CallFrame) (height : Nat) (rest : List Instr) : CallFrame :=
  {frame with labels := {arity := 0, height, rest, loop := none} :: frame.labels}

/-- Block entry consumes one interpreter step and no gas. The stack, locals,
store and caller frames are retained exactly. -/
theorem wp_block_empty (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (body code : List Instr) (post : Post)
    (hcredits : store.host.gas.Credits rest)
    (hnext : WP cfg fuel (.next (atCode store limits stack
      (emptyBlockFrame frame stack.size code) callers body)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack frame callers (.block .empty body :: code)))
      rest post := by
  let c := atCode store limits stack frame callers (.block .empty body :: code)
  have hz := chargeWasm_zero (.next c) (hcredits.mono (Nat.zero_le rest))
  have hc : chargeConfig c 0 = (c, none) := by
    cases he : chargeConfig c 0 with
    | mk c' error =>
      simp only [chargeWasm, he] at hz
      cases hz
      rfl
  have hcost : nextInstructionGas cfg c = 0 := rfl
  have hstep : Exec.step c = .next (atCode store limits stack
      (emptyBlockFrame frame stack.size code) callers body) := by
    simp [Exec.step, Exec.instr, Exec.blockType, Exec.Effect.continue, c, atCode, emptyBlockFrame]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost, hc, hstep] at h
  simp only [Nat.zero_add] at h
  apply h hcredits
  · rfl
  · simp [frameTransitionGas, c, atCode, emptyBlockFrame, Config.callDepth]
  · exact hnext

/-- i32 inequality pushes the actual Wasm zero-or-one result. -/
theorem wp_i32_ne (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : UInt32) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (Numeric.bool (a != b)))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_relop .ne :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 a)).push (.i32 b)) frame callers
    (.i32_relop .ne :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits
        (stack.push (.i32 (Numeric.bool (a != b)))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, Numeric.irelop32,
      c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- A nonzero condition exits the current empty-result non-loop block. The
discarded instruction tail need not be safe: it is never executed. -/
theorem wp_br_if_block_nonzero (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code discarded : List Instr) (condition : UInt32) (post : Post)
    (hcondition : condition ≠ 0)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      stack frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 condition))
      (emptyBlockFrame frame stack.size code) callers (.br_if 0 :: discarded)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i32 condition))
    (emptyBlockFrame frame stack.size code) callers (.br_if 0 :: discarded)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge,
      Config.stackTop?, Config.labelIsLoop, emptyBlockFrame]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, Exec.branch, Exec.popN,
      c, atCode, chargeConfig, chargedStore, emptyBlockFrame, hcondition]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c, emptyBlockFrame]
  · rw [← hcost, hstep]; exact hnext

end Wasm.Near.MeteredLogic
