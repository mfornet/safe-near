import NearVM.MeteredRules
import Wasm.MemoryLemmas

/-! Metered four-byte loads and stores with exact little-endian footprints,
explicit bounds, and arbitrary operand prefixes and caller frames. -/
namespace Wasm.Near.MeteredLogic

/-- The four-byte little-endian value returned by the actual memory reader. -/
def readI32 (memory : Memory) (address : Nat) : UInt32 :=
  UInt32.ofNat ((List.range 4).foldr
    (fun i acc => acc * 256 + (memory.read8 (address + i)).toNat) 0)

/-- The four little-endian bytes written by an unpacked i32 store. -/
def writeI32 (memory : Memory) (address : Nat) (value : UInt32) : Memory :=
  memory.writeRun address 4 (fun i => UInt8.ofNat (value.toNat >>> (8 * i)))

/-- Replace exactly one memory; every other store field is retained. -/
def storeI32 (store : Store NearState) (index address : Nat) (memory : Memory)
    (value : UInt32) : Store NearState :=
  { store with mems := store.mems.set! index (writeI32 memory address value) }

@[simp] theorem storeI32_host (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI32 store index address memory value).host = store.host := rfl

@[simp] theorem storeI32_modules (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI32 store index address memory value).modules = store.modules := rfl

@[simp] theorem storeI32_funcs (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI32 store index address memory value).funcs = store.funcs := rfl

@[simp] theorem storeI32_globals (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI32 store index address memory value).globals = store.globals := rfl

@[simp] theorem storeI32_tables (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI32 store index address memory value).tables = store.tables := rfl

/-- Updating a present memory preserves its index and installs exactly the
    specified byte write. -/
theorem storeI32_memory (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) (hmemory : store.mems[index]? = some memory) :
    (storeI32 store index address memory value).mems[index]? =
      some (writeI32 memory address value) := by
  have hi := (Array.getElem?_eq_some_iff.mp hmemory).1
  simp [storeI32, hi]

/-- Every other memory is retained, including absent indices. -/
theorem storeI32_other_memory (store : Store NearState) (index address other : Nat)
    (memory : Memory) (value : UInt32) (hne : other ≠ index) :
    (storeI32 store index address memory value).mems[other]? = store.mems[other]? := by
  simp [storeI32, Ne.symm hne]

/-- Bounds suffice for the actual memory API, independently of alignment hints. -/
theorem writeNat_i32 (memory : Memory) (address : Nat) (value : UInt32)
    (hbound : address + 4 ≤ memory.byteSize) :
    memory.writeNat address 4 value.toNat = some (writeI32 memory address value) :=
  Memory.writeNat_eq hbound

/-- Complete byte-level frame: size and limit are fixed, and all bytes outside
    the four-byte interval retain their previous values. -/
theorem writeI32_spec (memory : Memory) (address : Nat) (value : UInt32)
    (hwf : memory.wf) (hbound : address + 4 ≤ memory.byteSize) :
    (writeI32 memory address value).wf ∧
    (writeI32 memory address value).byteSize = memory.byteSize ∧
    (writeI32 memory address value).max = memory.max ∧
    ∀ j, (writeI32 memory address value).read8 j =
      if address ≤ j ∧ j < address + 4 then
        UInt8.ofNat (value.toNat >>> (8 * (j - address))) else memory.read8 j :=
  Memory.writeRun_spec hwf hbound _

/-- An in-bounds i32 store pays one opcode charge, consumes only the address
    and value, and leaves locals, labels, caller frames and other store fields
    explicit in the continuation. -/
theorem wp_i32_store (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg)
    (address : UInt32) (value : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.memAddrs[0]? = some index)
    (hmemory : store.mems[index]? = some memory)
    (hbound : address.toNat + arg.offset + 4 ≤ memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (storeI32 (chargedStore store cfg.regularOpCost) index
        (address.toNat + arg.offset) memory value) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits ((stack.push (.i32 address)).push (.i32 value))
        frame callers (.store .i32 none arg :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 address)).push (.i32 value))
    frame callers (.store .i32 none arg :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hwrite := writeNat_i32 memory (address.toNat + arg.offset) value hbound
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (storeI32 (chargedStore store cfg.regularOpCost) index
        (address.toNat + arg.offset) memory value) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.storeEffect, Exec.storeNat, Exec.i32,
      Exec.Effect.continue, c, atCode, chargeConfig, chargedStore, storeI32,
      Store.memOf, Store.setMemOf, getElem!_def, hmodule, hindex, hmemory, hwrite,
      NumType.byteWidth]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Bounds discharge the memory API directly; no load-result callback or
memory-well-formedness assumption is needed to execute the read. -/
theorem wp_i32_load (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg)
    (address : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.memAddrs[0]? = some index)
    (hmemory : store.mems[index]? = some memory)
    (hbound : address.toNat + arg.offset + 4 ≤ memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (readI32 memory (address.toNat + arg.offset)))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 address)) frame callers
      (.load .i32 none arg :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i32 address)) frame callers (.load .i32 none arg :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (readI32 memory (address.toNat + arg.offset)))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig,
      chargedStore, Exec.loadNat, Store.memOf, getElem!_def, hmodule, hindex, hmemory,
      Memory.readNat, Memory.inBounds, hbound, NumType.byteWidth, readI32]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

end Wasm.Near.MeteredLogic
