import NearVM.MeteredBitRules

/-! Metered word conversion, unary operations, and 64-bit scalar instructions. -/
namespace Wasm.Near.MeteredLogic

theorem wp_i32_unop (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (op : IUnOp) (a : UInt32) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (Numeric.iunop32 op a))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 a))
      frame callers (.i32_unop op :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i32 a)) frame callers (.i32_unop op :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (Numeric.iunop32 op a))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_i64_unop (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (op : IUnOp) (a : UInt64) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i64 (Numeric.iunop64 op a))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i64 a))
      frame callers (.i64_unop op :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i64 a)) frame callers (.i64_unop op :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i64 (Numeric.iunop64 op a))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_i64_relop (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (op : IRelOp) (a b : UInt64) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (Numeric.bool (Numeric.irelop64 op a b)))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i64 a)).push (.i64 b))
      frame callers (.i64_relop op :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i64 a)).push (.i64 b)) frame callers (.i64_relop op :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (Numeric.bool (Numeric.irelop64 op a b)))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_i64_eqz (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a : UInt64) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (Numeric.bool (a == 0)))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i64 a))
      frame callers (.i64_eqz :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i64 a)) frame callers (.i64_eqz :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (Numeric.bool (a == 0)))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_i64_binop_ok (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (op : IBinOp) (a b value : UInt64) (post : Post)
    (hcalc : Numeric.ibinop64 op a b = .ok value)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i64 value)) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i64 a)).push (.i64 b))
      frame callers (.i64_binop op :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i64 a)).push (.i64 b)) frame callers (.i64_binop op :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i64 value)) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore, hcalc]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_cvt_ok (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (op : CvtOp) (value result : Value) (post : Post)
    (hcalc : Numeric.cvt op value = .ok result)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push result) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push value)
      frame callers (.cvt op :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push value) frame callers (.cvt op :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push result) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore, hcalc]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hc
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

theorem wp_i32_wrap_i64 (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (value : UInt64) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (Value.i32 value.toUInt32)) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (Value.i64 value))
      frame callers (.cvt .i32_wrap_i64 :: code))) (cfg.regularOpCost + rest) post :=
  wp_cvt_ok cfg fuel rest store limits stack frame callers code .i32_wrap_i64
    (Value.i64 value) (Value.i32 value.toUInt32) post rfl hc hnext

theorem wp_i64_extend_i32_u (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (value : UInt32) (post : Post)
    (hc : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (Value.i64 value.toUInt64)) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (Value.i32 value))
      frame callers (.cvt .i64_extend_i32_u :: code))) (cfg.regularOpCost + rest) post :=
  wp_cvt_ok cfg fuel rest store limits stack frame callers code .i64_extend_i32_u
    (Value.i32 value) (Value.i64 value.toUInt64) post rfl hc hnext

end Wasm.Near.MeteredLogic
