import NearVM.MeteredLogic

/-!
# Straight-line rules for the metered interpreter

Instruction rules keep the arbitrary operand-stack prefix, enclosing labels and
caller frames explicit. Charging changes only the host state's gas accounting:
linear memory, tables, globals and the function/module environment are framed.
-/

namespace Wasm.Near.MeteredLogic

/-- Replace the active frame's code, retaining every caller and label. -/
def atCode (store : Store NearState) (limits : ExecLimits) (stack : Array Value)
    (frame : CallFrame) (callers : List CallFrame) (code : List Instr) : Config NearState :=
  { store, limits, thread := { stack, frames := { frame with code } :: callers } }

/-- A Wasm instruction's charge changes the host state alone. -/
def chargedStore (store : Store NearState) (cost : Nat) : Store NearState :=
  { store with host := (chargeHost store.host cost).1 }

@[simp] theorem chargedStore_mems (store : Store NearState) (cost : Nat) :
    (chargedStore store cost).mems = store.mems := rfl

@[simp] theorem chargedStore_globals (store : Store NearState) (cost : Nat) :
    (chargedStore store cost).globals = store.globals := rfl

@[simp] theorem chargedStore_tables (store : Store NearState) (cost : Nat) :
    (chargedStore store cost).tables = store.tables := rfl

/-- Push a constant without changing locals, labels, callers or the store's
non-host resources. The regular instruction cost is paid before continuing. -/
theorem wp_i32_const (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (n : UInt32) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 n))
        frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack frame callers (.i32_const n :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits stack frame callers (.i32_const n :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 n))
        frame callers code) := by rw [hcost]; rfl
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Push a constant without changing locals, labels, callers or the store's
non-host resources. The regular instruction cost is paid before continuing. -/
theorem wp_i64_const (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (n : UInt64) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i64 n))
        frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack frame callers (.i64_const n :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits stack frame callers (.i64_const n :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i64 n))
        frame callers code) := by rw [hcost]; rfl
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Reading an existing local retains all previous stack values and all locals. -/
theorem wp_local_get (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index : Nat) (value : Value) (post : Post)
    (hlocal : frame.locals[index]? = some value)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push value)
        frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack frame callers (.local_get index :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits stack frame callers (.local_get index :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push value)
        frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore, getElem!_def, hlocal]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Writing a local consumes the top value and retains the entire stack prefix. -/
theorem wp_local_set (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index : Nat) (value : Value) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (chargedStore store cfg.regularOpCost) limits stack
        { frame with locals := frame.locals.set! index value } callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push value) frame callers (.local_set index :: code)))
      (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push value) frame callers (.local_set index :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits stack
        { frame with locals := frame.locals.set! index value } callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig, chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- A frame returning one value, with arbitrary locals and module index. -/
def resultFrame (locals : Array Value) (inst : Nat) : CallFrame :=
  { locals, inst, arity := 1, height := 0, labels := [], code := [] }

private theorem chargeConfig_zero (c : Config NearState) (h : c.store.host.gas.Credits 0) :
    chargeConfig c 0 = (c, none) := by
  have hz := chargeWasm_zero (.next c) h
  cases hc : chargeConfig c 0 with
  | mk c' error =>
    simp only [chargeWasm, hc] at hz
    cases hz
    rfl

/-- Returning from a completed frame is administrative and spends no gas. -/
theorem wp_finish_i32 (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (n : UInt32) (post : Post)
    (hcredits : store.host.gas.Credits rest)
    (hpost : post rest (.done [.i32 n] store) none) :
    WP cfg (fuel + 1)
      (.next (atCode store limits #[.i32 n] (resultFrame locals inst) [] [])) rest post := by
  let c := atCode store limits #[.i32 n] (resultFrame locals inst) [] []
  have hzero := chargeConfig_zero c (hcredits.mono (Nat.zero_le rest))
  have hcost : nextInstructionGas cfg c = 0 := rfl
  have hstep : Exec.step c = .done [.i32 n] store := rfl
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost, hzero, hstep] at h
  simp only [Nat.zero_add] at h
  apply h (by simpa only [c, atCode] using hcredits)
  · rfl
  · rfl
  · exact wp_done cfg fuel _ store rest post hcredits hpost

/-- A complete constant-return program: one charged instruction and one free
administrative return. This runs from an already active frame; entry activation
is charged by `runInitialized` separately. The final store is explicit, so all
memory, globals, tables and the caller's unused gas credits are preserved. -/
theorem wp_const_return (cfg : WasmConfig) (rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (n : UInt32)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest)) :
    WP cfg 2 (.next (atCode store limits #[] (resultFrame locals inst) [] [.i32_const n]))
      (cfg.regularOpCost + rest)
      (fun remaining final error => remaining = rest ∧
        final = .done [.i32 n] (chargedStore store cfg.regularOpCost) ∧ error = none) := by
  apply wp_i32_const cfg 1 rest store limits #[] (resultFrame locals inst) [] [] n _ hcredits
  have hcharged := Pays.chargeWasm (.next (atCode store limits #[] (resultFrame locals inst) [] []))
    cfg.regularOpCost rest hcredits
  apply wp_finish_i32 cfg 0 rest (chargedStore store cfg.regularOpCost) limits locals inst n
  · exact hcharged.2.2.2.2
  · exact ⟨rfl, rfl, rfl⟩

/-- Adequacy for the example gives the actual interpreter result, preserving
linear memory and burning exactly one regular operation cost. -/
theorem run_const_return (cfg : WasmConfig) (rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (locals : Array Value) (inst : Nat) (n : UInt32)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest)) :
    let result := runMetered cfg 2
      (.next (atCode store limits #[] (resultFrame locals inst) [] [.i32_const n]))
    result = (.done [.i32 n] (chargedStore store cfg.regularOpCost), none) ∧
    result.1.store.mems = store.mems ∧
    result.1.host.gas.burnt = store.host.gas.burnt + cfg.regularOpCost := by
  obtain ⟨_, ⟨_, hfinal, herror⟩, _⟩ :=
    (wp_const_return cfg rest store limits locals inst n hcredits).result
  have hrun : runMetered cfg 2
      (.next (atCode store limits #[] (resultFrame locals inst) [] [.i32_const n])) =
      (.done [.i32 n] (chargedStore store cfg.regularOpCost), none) :=
    Prod.ext hfinal herror
  dsimp only
  rw [hrun]
  exact ⟨rfl, rfl, (GasCounter.burn_credits store.host.gas cfg.regularOpCost rest hcredits).2.1⟩

end Wasm.Near.MeteredLogic
