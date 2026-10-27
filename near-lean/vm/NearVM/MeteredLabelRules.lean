import NearVM.MeteredBranchRules

/-! Branches through arbitrary intervening labels to an empty-result non-loop target. -/
namespace Wasm.Near.MeteredLogic

def labelPrefixFrame (frame : CallFrame) (height : Nat) (skipped : List Label) (code : List Instr) : CallFrame :=
  { frame with labels := skipped ++ {arity := 0,height,rest := code,loop := none} :: frame.labels }

/-- All intervening labels are discarded by the actual branch depth. The
selected outer label determines its zero result arity and resumed code. -/
theorem wp_br_if_label_nonzero (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : List Instr) (condition : UInt32) (post : Post)
    (hcondition : condition ≠ 0)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 condition))
      (labelPrefixFrame frame stack.size skipped code) callers (.br_if skipped.length :: discarded)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i32 condition))
    (labelPrefixFrame frame stack.size skipped code) callers (.br_if skipped.length :: discarded)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c,atCode,nextInstructionGas,Config.nextInstr?,linearInstruction,loopBackedge,
      Config.labelIsLoop,Config.stackTop?,labelPrefixFrame]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step,Exec.instr,Exec.i32,Exec.Effect.continue,Exec.branch,Exec.popN,
      c,atCode,chargeConfig,chargedStore,labelPrefixFrame,hcondition]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost,hstep,hcost]; rfl
  · rw [← hcost,hstep]
    simp [frameTransitionGas,Config.callDepth,atCode,chargeConfig,c,labelPrefixFrame]
  · rw [← hcost,hstep]; exact hnext

end Wasm.Near.MeteredLogic
