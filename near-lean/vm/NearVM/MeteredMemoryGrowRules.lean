import NearVM.MeteredMemoryRules

/-! Exact metering and store frame for successful linear memory growth. -/
namespace Wasm.Near.MeteredLogic

/-- The actual linear memory-growth fee, including the requested page count. -/
def memoryGrowCost (cfg : WasmConfig) (delta : UInt32) : Nat :=
  cfg.linearOpBaseCost + cfg.linearOpUnitCost * delta.toNat

/-- Install the memory returned by `Memory.grow`, retaining every other field. -/
def grownStore (store : Store NearState) (index : Nat) (memory : Memory) : Store NearState :=
  { store with mems := store.mems.set! index memory }

@[simp] theorem grownStore_frame (store : Store NearState) (index : Nat) (memory : Memory) :
    (grownStore store index memory).host = store.host ∧
    (grownStore store index memory).modules = store.modules ∧
    (grownStore store index memory).funcs = store.funcs ∧
    (grownStore store index memory).globals = store.globals ∧
    (grownStore store index memory).tables = store.tables := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem grownStore_memory (store : Store NearState) (index : Nat)
    (memory grown : Memory) (hmemory : store.mems[index]? = some memory) :
    (grownStore store index grown).mems[index]? = some grown := by
  have hi := (Array.getElem?_eq_some_iff.mp hmemory).1
  simp [grownStore, hi]

theorem grownStore_other_memory (store : Store NearState) (index other : Nat)
    (grown : Memory) (hne : other ≠ index) :
    (grownStore store index grown).mems[other]? = store.mems[other]? := by
  simp [grownStore, Ne.symm hne]

/-- Growth preserves the functional host and consumes exactly its linear fee. -/
theorem grownStore_gas (cfg : WasmConfig) (delta : UInt32) (store : Store NearState)
    (index rest : Nat) (grown : Memory)
    (hc : store.host.gas.Credits (memoryGrowCost cfg delta + rest)) :
    let after := grownStore (chargedStore store (memoryGrowCost cfg delta)) index grown
    after.host.gas.burnt = store.host.gas.burnt + memoryGrowCost cfg delta ∧
    after.host.gas.promises = store.host.gas.promises ∧
    after.host.gas.Credits rest ∧
    {after.host with gas := store.host.gas, gasProfile := store.host.gasProfile} = store.host := by
  have h := GasCounter.burn_credits store.host.gas (memoryGrowCost cfg delta) rest hc
  exact ⟨h.2.1, h.2.2.1, h.2.2.2, rfl⟩

/-- A successful grow charges the linear fee once and returns the old page count.
The premise describes the deterministic memory API, independently of execution. -/
theorem wp_memory_grow (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (delta : UInt32)
    (mi : ModuleInst) (index : Nat) (memory grown : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.memAddrs[0]? = some index)
    (hmemory : store.mems[index]? = some memory)
    (hgrow : memory.grow delta.toNat = some grown)
    (hcredits : store.host.gas.Credits (memoryGrowCost cfg delta + rest))
    (hnext : WP cfg fuel
      (.next (atCode (grownStore (chargedStore store (memoryGrowCost cfg delta)) index grown)
        limits (stack.push (.i32 (UInt32.ofNat memory.size))) frame callers code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits (stack.push (.i32 delta)) frame callers
        (.memory_grow :: code))) (memoryGrowCost cfg delta + rest) post := by
  let c := atCode store limits (stack.push (.i32 delta)) frame callers (.memory_grow :: code)
  have hcost : nextInstructionGas cfg c = memoryGrowCost cfg delta := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, Config.stackTop?,
      linearInstruction, memoryGrowCost]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (grownStore (chargedStore store (memoryGrowCost cfg delta)) index grown)
        limits (stack.push (.i32 (UInt32.ofNat memory.size))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode,
      chargeConfig, chargedStore, grownStore, Store.memOf, Store.setMemOf,
      getElem!_def, hmodule, hindex, hmemory, hgrow]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep, hcost]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

end Wasm.Near.MeteredLogic
