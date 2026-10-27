import NearVM.MeteredControlRules

/-! Actual select, bitwise-or and nested block exits on the value-return path. -/
namespace Wasm.Near.MeteredLogic

theorem wp_i32_or (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : UInt32) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (a ||| b))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_binop .or :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 a)).push (.i32 b)) frame callers (.i32_binop .or :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (a ||| b))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig,
      chargedStore, Numeric.ibinop32]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_select (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : Value) (condition : UInt32) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (if condition ≠ 0 then a else b)) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (((stack.push a).push b).push (.i32 condition))
      frame callers (.select none :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (((stack.push a).push b).push (.i32 condition)) frame callers (.select none :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits
        (stack.push (if condition ≠ 0 then a else b)) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_br_two_blocks (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code innerRest discarded : List Instr) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      stack frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack
      (emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size innerRest)
      callers (.br 1 :: discarded))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits stack
    (emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size innerRest)
    callers (.br 1 :: discarded)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge,
      Config.labelIsLoop, emptyBlockFrame]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, Exec.branch, Exec.popN,
      c, atCode, chargeConfig, chargedStore, emptyBlockFrame]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c, emptyBlockFrame]
  · rw [← hcost, hstep]; exact hnext

end Wasm.Near.MeteredLogic
