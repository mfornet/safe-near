import NearVM.MeteredLabelRules

/-! Metered branch tables with a selected non-loop, empty-result target. -/
namespace Wasm.Near.MeteredLogic

/-- The actual popped index selects its table entry, or the default when absent.
All labels before the selected target are discarded by the branch. -/
theorem wp_br_table_label (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : List Instr) (index : UInt32)
    (targets : List Nat) (fallback : Nat) (post : Post)
    (htarget : targets[index.toNat]?.getD fallback=skipped.length)
    (hc : store.host.gas.Credits (cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code)) rest post) :
    WP cfg (fuel+1) (.next (atCode store limits (stack.push (.i32 index))
      (labelPrefixFrame frame stack.size skipped code) callers (.br_table targets fallback::discarded)))
      (cfg.regularOpCost+rest) post := by
  let c := atCode store limits (stack.push (.i32 index))
    (labelPrefixFrame frame stack.size skipped code) callers (.br_table targets fallback::discarded)
  have hcost : nextInstructionGas cfg c=cfg.regularOpCost := by
    simp [c,atCode,nextInstructionGas,Config.nextInstr?,linearInstruction,loopBackedge,
      Config.labelIsLoop,Config.stackTop?,labelPrefixFrame,htarget]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1=
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step,Exec.instr,Exec.i32,Exec.Effect.continue,Exec.branch,Exec.popN,
      c,atCode,chargeConfig,chargedStore,labelPrefixFrame,htarget]
  have h := wp_pure_next (cfg:=cfg) (fuel:=fuel) (c:=c) (rest:=rest) (post:=post)
  rw [hcost] at h
  apply h hc
  · rw [←hcost,hstep,hcost];rfl
  · rw [←hcost,hstep]
    simp [frameTransitionGas,Config.callDepth,atCode,chargeConfig,c,labelPrefixFrame]
  · rw [←hcost,hstep];exact hnext
end Wasm.Near.MeteredLogic
