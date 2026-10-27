import Proofs.ValueReturnThreadLocal
import NearVM.MeteredLoopRules

/-! The explicit return instruction on the deployed lazy lookup path. -/
namespace WNear.Proofs.ValueReturnLazyLookup
open Wasm Wasm.Near MeteredLogic
set_option maxRecDepth 16384

/-- Actual `return` discards the callee's labels and suffix and restores the
saved caller. Its one charged opcode is distinct from a free empty-body exit. -/
theorem wp_return_wasm (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (base results : List Value) (frame caller : CallFrame)
    (callers : List CallFrame) (code : List Instr) (post : Post)
    (harity : results.length = frame.arity) (hheight : frame.height = base.length)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (base ++ results).toArray caller callers caller.code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (base ++ results).toArray frame (caller :: callers)
      (.return :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (base ++ results).toArray frame (caller :: callers) (.return :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hp := popN_arguments base results
  rw [harity] at hp
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (base ++ results).toArray caller callers caller.code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, c, atCode, chargeConfig, Exec.leave, Exec.Effect.return, chargedStore, hp, hheight]
  have rule := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at rule
  apply rule hc
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, c, atCode, Config.callDepth, chargeConfig]
    omega
  · rw [← hcost, hstep]
    exact hnext


/-- The actual status comparison takes the lazy branch whenever the loaded
word differs from one. The next phase executes the real f467 call. -/
theorem wp_lazy_guard (cfg : WasmConfig) (fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (ptr : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hptr : frame.locals[0]? = some (.i32 ptr))
    (hm : s.modules[frame.inst]? = some mi) (hi : mi.memAddrs[0]? = some index)
    (hmem : s.mems[index]? = some memory) (hb : ptr.toNat + 4 ≤ memory.byteSize)
    (hstatus : readI32 memory ptr.toNat ≠ 1)
    (hc : s.host.gas.Credits (5 * cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (WNear.Proofs.StorePairCaller.paid s cfg.regularOpCost 5)
      limits stack frame callers code)) rest post) :
    WP cfg (fuel + 5) (.next (atCode s limits stack frame callers
      (WNear.Binary.ValueReturnThreadLocal.guard ++ code))) (5 * cfg.regularOpCost + rest) post := by
  let op := cfg.regularOpCost
  have hm1 : (chargedStore s op).modules[frame.inst]? = some mi := by simpa only [chargedStore] using hm
  have hmem1 : (chargedStore s op).mems[index]? = some memory := by simpa only [chargedStore] using hmem
  have hbool : Numeric.bool (Numeric.irelop32 .eq (readI32 memory ptr.toNat) 1) = 0 := by
    simp [Numeric.irelop32, Numeric.bool, hstatus]
  rw [show 5 * cfg.regularOpCost + rest = cfg.regularOpCost + (4 * op + rest) by dsimp [op]; omega]
  apply wp_local_get cfg (fuel + 4) _ s limits stack frame callers _ 0 (.i32 ptr) post hptr (hc.mono (by dsimp [op]; omega))
  rw [show 4 * op + rest = cfg.regularOpCost + (3 * op + rest) by dsimp [op]; omega]
  apply wp_i32_load cfg (fuel + 3) _ (chargedStore s op) limits stack frame callers _
    {align := 2, offset := 0} ptr mi index memory post hm1 hi hmem1 (by simpa using hb)
  · exact WNear.Proofs.StorePairCaller.paid_credits s op 1 _ (hc.mono (by dsimp [op]; omega))
  rw [show 3 * op + rest = cfg.regularOpCost + (2 * op + rest) by dsimp [op]; omega]
  apply wp_i32_const cfg (fuel + 2) _ (WNear.Proofs.StorePairCaller.paid s op 2) limits _ frame callers _ 1 post
  · exact WNear.Proofs.StorePairCaller.paid_credits s op 2 _ (hc.mono (by dsimp [op]; omega))
  rw [show 2 * op + rest = cfg.regularOpCost + (op + rest) by dsimp [op]; omega]
  apply wp_i32_relop cfg (fuel + 1) _ (WNear.Proofs.StorePairCaller.paid s op 3) limits stack frame callers _ .eq (readI32 memory ptr.toNat) 1 post
  · exact WNear.Proofs.StorePairCaller.paid_credits s op 3 _ (hc.mono (by dsimp [op]; omega))
  simp only [hbool]
  apply wp_br_if_zero cfg fuel rest (WNear.Proofs.StorePairCaller.paid s op 4) limits stack frame callers code 0 post
  · exact WNear.Proofs.StorePairCaller.paid_credits s op 4 _ (hc.mono (by dsimp [op]; omega))
  · exact hnext

end WNear.Proofs.ValueReturnLazyLookup
