import NearVM.MeteredNumericRules

/-! Exact metered i32 bitwise and non-trapping unsigned division instructions. -/
namespace Wasm.Near.MeteredLogic

theorem wp_i32_binop_ok (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (op : IBinOp) (a b value : UInt32) (post : Post)
    (hcalc : Numeric.ibinop32 op a b = .ok value)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 value)) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_binop op :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 a)).push (.i32 b)) frame callers (.i32_binop op :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 value)) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore, hcalc]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_i32_and (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : UInt32) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (a &&& b))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_binop .and :: code))) (cfg.regularOpCost + rest) post :=
  wp_i32_binop_ok cfg fuel rest store limits stack frame callers code .and a b (a &&& b) post rfl hc hnext

theorem wp_i32_or (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : UInt32) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (a ||| b))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_binop .or :: code))) (cfg.regularOpCost + rest) post :=
  wp_i32_binop_ok cfg fuel rest store limits stack frame callers code .or a b (a ||| b) post rfl hc hnext

theorem wp_i32_div_u (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : UInt32) (post : Post)
    (hb : b ≠ 0) (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (a / b))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_binop .div_u :: code))) (cfg.regularOpCost + rest) post := by
  apply wp_i32_binop_ok cfg fuel rest store limits stack frame callers code .div_u a b (a / b) post
  · simp [Numeric.ibinop32, hb]
  · exact hc
  · exact hnext

end Wasm.Near.MeteredLogic
