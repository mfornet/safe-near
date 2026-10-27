import NearVM.MeteredRules
import Wasm.MemoryLemmas

/-! Metered stores with explicit byte footprints and arbitrary caller frames. -/
namespace Wasm.Near.MeteredLogic

/-- The eight little-endian bytes written by an unpacked i64 store. -/
def writeI64 (memory : Memory) (address : Nat) (value : UInt64) : Memory :=
  memory.writeRun address 8 (fun i => UInt8.ofNat (value.toNat >>> (8 * i)))

/-- Replace exactly one memory; every other store field is retained. -/
def storeI64 (store : Store NearState) (index address : Nat) (memory : Memory)
    (value : UInt64) : Store NearState :=
  { store with mems := store.mems.set! index (writeI64 memory address value) }

@[simp] theorem storeI64_host (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt64) :
    (storeI64 store index address memory value).host = store.host := rfl

@[simp] theorem storeI64_modules (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt64) :
    (storeI64 store index address memory value).modules = store.modules := rfl

@[simp] theorem storeI64_funcs (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt64) :
    (storeI64 store index address memory value).funcs = store.funcs := rfl

@[simp] theorem storeI64_globals (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt64) :
    (storeI64 store index address memory value).globals = store.globals := rfl

@[simp] theorem storeI64_tables (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt64) :
    (storeI64 store index address memory value).tables = store.tables := rfl

/-- Updating a present memory preserves its index and installs exactly the
    specified byte write. -/
theorem storeI64_memory (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt64) (hmemory : store.mems[index]? = some memory) :
    (storeI64 store index address memory value).mems[index]? =
      some (writeI64 memory address value) := by
  have hi := (Array.getElem?_eq_some_iff.mp hmemory).1
  simp [storeI64, hi]

/-- Every other memory is retained, including absent indices. -/
theorem storeI64_other_memory (store : Store NearState) (index address other : Nat)
    (memory : Memory) (value : UInt64) (hne : other ≠ index) :
    (storeI64 store index address memory value).mems[other]? = store.mems[other]? := by
  simp [storeI64, Ne.symm hne]

/-- Bounds suffice for the actual memory API, independently of alignment hints. -/
theorem writeNat_i64 (memory : Memory) (address : Nat) (value : UInt64)
    (hbound : address + 8 ≤ memory.byteSize) :
    memory.writeNat address 8 value.toNat = some (writeI64 memory address value) :=
  Memory.writeNat_eq hbound

/-- Complete byte-level frame: size and limit are fixed, and all bytes outside
    the eight-byte interval retain their previous values. -/
theorem writeI64_spec (memory : Memory) (address : Nat) (value : UInt64)
    (hwf : memory.wf) (hbound : address + 8 ≤ memory.byteSize) :
    (writeI64 memory address value).wf ∧
    (writeI64 memory address value).byteSize = memory.byteSize ∧
    (writeI64 memory address value).max = memory.max ∧
    ∀ j, (writeI64 memory address value).read8 j =
      if address ≤ j ∧ j < address + 8 then
        UInt8.ofNat (value.toNat >>> (8 * (j - address))) else memory.read8 j :=
  Memory.writeRun_spec hwf hbound _

/-- An in-bounds i64 store pays one opcode charge, consumes only the address
    and value, and leaves locals, labels, caller frames and other store fields
    explicit in the continuation. -/
theorem wp_i64_store (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg)
    (address : UInt32) (value : UInt64) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.memAddrs[0]? = some index)
    (hmemory : store.mems[index]? = some memory)
    (hbound : address.toNat + arg.offset + 8 ≤ memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (storeI64 (chargedStore store cfg.regularOpCost) index
        (address.toNat + arg.offset) memory value) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits ((stack.push (.i32 address)).push (.i64 value))
        frame callers (.store .i64 none arg :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 address)).push (.i64 value))
    frame callers (.store .i64 none arg :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hwrite := writeNat_i64 memory (address.toNat + arg.offset) value hbound
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (storeI64 (chargedStore store cfg.regularOpCost) index
        (address.toNat + arg.offset) memory value) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.storeEffect, Exec.storeNat, Exec.i32,
      Exec.Effect.continue, c, atCode, chargeConfig, chargedStore, storeI64,
      Store.memOf, Store.setMemOf, getElem!_def, hmodule, hindex, hmemory, hwrite,
      NumType.byteWidth]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

end Wasm.Near.MeteredLogic
