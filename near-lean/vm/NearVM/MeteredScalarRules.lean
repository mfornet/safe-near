import NearVM.MeteredMemoryRules

/-! Scalar rules for actual metered Wasm steps. Every rule retains arbitrary
operand-stack prefixes, labels and caller frames and charges the regular cost.
Integer operations use Wasm's UInt32 wrapping arithmetic. -/
namespace Wasm.Near.MeteredLogic

/-- The value obtained by the actual eight-byte little-endian memory reader. -/
def readI64 (memory : Memory) (address : Nat) : UInt64 :=
  UInt64.ofNat ((List.range 8).foldr
    (fun i acc => acc * 256 + (memory.read8 (address + i)).toNat) 0)

/-- Update one resolved global, retaining its type and every other store field. -/
def setGlobal (s : Store NearState) (index : Nat) (value : Value) : Store NearState :=
  {s with globals := s.globals.modify index ({ · with value })}

/-- Tee consumes no operand and changes only the selected local. -/
theorem wp_local_tee (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (index : Nat) (value : Value) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push value) {frame with locals := frame.locals.set! index value} callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push value) frame callers
      (.local_tee index :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push value) frame callers (.local_tee index :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push value) {frame with locals := frame.locals.set! index value} callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig,
      chargedStore]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Read a resolved global; no memory, locals or globals change. -/
theorem wp_global_get (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (slot index : Nat) (mi : ModuleInst)
    (global : GlobalInst) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.globalAddrs[slot]? = some index)
    (hglobal : store.globals[index]? = some global)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push global.value) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits stack frame callers
      (.global_get slot :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits stack frame callers (.global_get slot :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push global.value) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig,
      chargedStore, getElem!_def, hmodule, hindex, hglobal]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Write one resolved global, preserving its declared type. -/
theorem wp_global_set (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (slot index : Nat) (mi : ModuleInst)
    (value : Value) (global : GlobalInst) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.globalAddrs[slot]? = some index)
    (_hglobal : store.globals[index]? = some global)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode
      (setGlobal (chargedStore store cfg.regularOpCost) index value) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push value) frame callers
      (.global_set slot :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push value) frame callers (.global_set slot :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (setGlobal (chargedStore store cfg.regularOpCost) index value) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.Effect.continue, c, atCode, chargeConfig,
      chargedStore, setGlobal, getElem!_def, hmodule, hindex]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Actual i32 wrapping add; there is no arithmetic overflow trap. -/
theorem wp_i32_add (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : UInt32) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (a + b))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_binop .add :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 a)).push (.i32 b)) frame callers (.i32_binop .add :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (a + b))) frame callers code) := by
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

/-- Actual i32 wrapping sub; there is no arithmetic overflow trap. -/
theorem wp_i32_sub (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (a b : UInt32) (post : Post)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (a - b))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits ((stack.push (.i32 a)).push (.i32 b))
      frame callers (.i32_binop .sub :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 a)).push (.i32 b)) frame callers (.i32_binop .sub :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (a - b))) frame callers code) := by
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

/-- Bounds discharge the memory API directly; no load-result callback or
memory-well-formedness assumption is needed to execute the read. -/
theorem wp_i64_load (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg)
    (address : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.memAddrs[0]? = some index)
    (hmemory : store.mems[index]? = some memory)
    (hbound : address.toNat + arg.offset + 8 ≤ memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i64 (readI64 memory (address.toNat + arg.offset)))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 address)) frame callers
      (.load .i64 none arg :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i32 address)) frame callers (.load .i64 none arg :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i64 (readI64 memory (address.toNat + arg.offset)))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig,
      chargedStore, Exec.loadNat, Store.memOf, getElem!_def, hmodule, hindex, hmemory,
      Memory.readNat, Memory.inBounds, hbound, NumType.byteWidth, readI64]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

end Wasm.Near.MeteredLogic
