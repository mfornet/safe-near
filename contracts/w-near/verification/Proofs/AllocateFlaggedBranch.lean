import NearVM.MeteredLabelRules

/-! Unconditional branch to the actual nonloop label used by the flags-two exit. -/
namespace WNear.Proofs.AllocateFlagged
open Wasm Wasm.Near MeteredLogic

theorem wp_br_label (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (skipped : List Label) (code discarded : Expr) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code)) rest post) :
    WP cfg (fuel+1) (.next (atCode store limits stack (labelPrefixFrame frame stack.size skipped code) callers
      (.br skipped.length::discarded))) (cfg.regularOpCost+rest) post := by
  let c := atCode store limits stack (labelPrefixFrame frame stack.size skipped code) callers (.br skipped.length::discarded)
  have cost : nextInstructionGas cfg c=cfg.regularOpCost := by
    simp [c,atCode,nextInstructionGas,Config.nextInstr?,linearInstruction,loopBackedge,Config.labelIsLoop,labelPrefixFrame]
  have step : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1=
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack frame callers code) := by
    rw [cost]
    simp [Exec.step,Exec.instr,Exec.Effect.continue,Exec.branch,Exec.popN,c,atCode,chargeConfig,chargedStore,labelPrefixFrame]
  have h := wp_pure_next (cfg:=cfg) (fuel:=fuel) (c:=c) (rest:=rest) (post:=post)
  rw [cost] at h
  apply h hc
  · rw [←cost,step,cost]; rfl
  · rw [←cost,step]; simp [frameTransitionGas,Config.callDepth,c,atCode,chargeConfig]
  · rw [←cost,step]; exact hnext
end WNear.Proofs.AllocateFlagged
