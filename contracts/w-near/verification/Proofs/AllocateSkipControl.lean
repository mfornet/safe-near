import NearVM.MeteredLabelRules
import Proofs.AllocateSearchShell

/-! The actual search traversal's paid backedge through its candidate block. -/
namespace WNear.Proofs.AllocateSkip
open Wasm Wasm.Near MeteredLogic

 theorem wp_backedge (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (body code innerRest discarded : Expr) (post : Post)
    (hc : store.host.gas.Credits (2*cfg.regularOpCost+rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store (2*cfg.regularOpCost)) limits stack
      (emptyLoopFrame frame stack.size body code) callers body)) rest post) :
    WP cfg (fuel+1) (.next (atCode store limits stack
      (emptyBlockFrame (emptyLoopFrame frame stack.size body code) stack.size innerRest) callers (.br 1::discarded)))
      (2*cfg.regularOpCost+rest) post := by
  let c := atCode store limits stack (emptyBlockFrame (emptyLoopFrame frame stack.size body code) stack.size innerRest) callers (.br 1::discarded)
  have cost : nextInstructionGas cfg c=2*cfg.regularOpCost := by
    simp [c,atCode,nextInstructionGas,Config.nextInstr?,linearInstruction,loopBackedge,Config.labelIsLoop,emptyBlockFrame,emptyLoopFrame]
    omega
  have step : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store (2*cfg.regularOpCost)) limits stack (emptyLoopFrame frame stack.size body code) callers body) := by
    rw [cost]
    simp [Exec.step,Exec.instr,Exec.Effect.continue,Exec.branch,Exec.popN,c,atCode,chargeConfig,chargedStore,emptyBlockFrame,emptyLoopFrame]
  have rule := wp_pure_next (cfg:=cfg) (fuel:=fuel) (c:=c) (rest:=rest) (post:=post)
  rw [cost] at rule
  apply rule hc
  · rw [←cost,step,cost];rfl
  · rw [←cost,step]
    simp [frameTransitionGas,Config.callDepth,atCode,chargeConfig,c,emptyBlockFrame,emptyLoopFrame]
  · rw [←cost,step];exact hnext
end WNear.Proofs.AllocateSkip
