import NearVM.MeteredBranchRules

/-! Actual316 success branches through four empty-result blocks. -/
namespace Wasm.Near.MeteredLogic

theorem wp_br_four_blocks (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code outerRest middleRest innerRest discarded : List Instr) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      stack frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack
      (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size outerRest) stack.size middleRest) stack.size innerRest)
      callers (.br 3 :: discarded))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits stack
    (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame (emptyBlockFrame frame stack.size code) stack.size outerRest) stack.size middleRest) stack.size innerRest)
    callers (.br 3 :: discarded)
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
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c, emptyBlockFrame]
  · rw [← hcost, hstep]; exact hnext

end Wasm.Near.MeteredLogic
