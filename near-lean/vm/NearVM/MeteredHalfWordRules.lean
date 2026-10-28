import NearVM.MeteredRules
import Wasm.MemoryLemmas

/-! Metered two-byte loads and stores with exact little-endian footprints,
explicit bounds, and arbitrary operand prefixes and caller frames. -/
namespace Wasm.Near.MeteredLogic

/-- The two-byte little-endian value returned by the actual memory reader. -/
def readI16 (memory : Memory) (address : Nat) : UInt32 :=
  UInt32.ofNat ((List.range 2).foldr
    (fun i acc => acc * 256 + (memory.read8 (address + i)).toNat) 0)

/-- The two little-endian bytes written by a packed i32.store16 instruction. -/
def writeI16 (memory : Memory) (address : Nat) (value : UInt32) : Memory :=
  memory.writeRun address 2 (fun i => UInt8.ofNat (value.toNat >>> (8 * i)))

/-- Replace exactly one memory; every other store field is retained. -/
def storeI16 (store : Store NearState) (index address : Nat) (memory : Memory)
    (value : UInt32) : Store NearState :=
  { store with mems := store.mems.set! index (writeI16 memory address value) }

@[simp] theorem storeI16_host (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI16 store index address memory value).host = store.host := rfl

@[simp] theorem storeI16_modules (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI16 store index address memory value).modules = store.modules := rfl

@[simp] theorem storeI16_funcs (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI16 store index address memory value).funcs = store.funcs := rfl

@[simp] theorem storeI16_globals (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI16 store index address memory value).globals = store.globals := rfl

@[simp] theorem storeI16_tables (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) :
    (storeI16 store index address memory value).tables = store.tables := rfl

/-- Updating a present memory preserves its index and installs exactly the
    specified byte write. -/
theorem storeI16_memory (store : Store NearState) (index address : Nat)
    (memory : Memory) (value : UInt32) (hmemory : store.mems[index]? = some memory) :
    (storeI16 store index address memory value).mems[index]? =
      some (writeI16 memory address value) := by
  have hi := (Array.getElem?_eq_some_iff.mp hmemory).1
  simp [storeI16, hi]

/-- Every other memory is retained, including absent indices. -/
theorem storeI16_other_memory (store : Store NearState) (index address other : Nat)
    (memory : Memory) (value : UInt32) (hne : other ≠ index) :
    (storeI16 store index address memory value).mems[other]? = store.mems[other]? := by
  simp [storeI16, Ne.symm hne]

/-- Bounds suffice for the actual memory API, independently of alignment hints. -/
theorem writeNat_i16 (memory : Memory) (address : Nat) (value : UInt32)
    (hbound : address + 2 ≤ memory.byteSize) :
    memory.writeNat address 2 value.toNat = some (writeI16 memory address value) :=
  Memory.writeNat_eq hbound

/-- Complete byte-level frame: size and limit are fixed, and all bytes outside
    the two-byte interval retain their previous values. -/
theorem writeI16_spec (memory : Memory) (address : Nat) (value : UInt32)
    (hwf : memory.wf) (hbound : address + 2 ≤ memory.byteSize) :
    (writeI16 memory address value).wf ∧
    (writeI16 memory address value).byteSize = memory.byteSize ∧
    (writeI16 memory address value).max = memory.max ∧
    ∀ j, (writeI16 memory address value).read8 j =
      if address ≤ j ∧ j < address + 2 then
        UInt8.ofNat (value.toNat >>> (8 * (j - address))) else memory.read8 j :=
  Memory.writeRun_spec hwf hbound _

/-- An in-bounds i32.store16 pays one opcode charge, consumes only the address
    and value, and leaves locals, labels, caller frames and other store fields
    explicit in the continuation. -/
theorem wp_i32_store16 (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg)
    (address : UInt32) (value : UInt32) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.memAddrs[0]? = some index)
    (hmemory : store.mems[index]? = some memory)
    (hbound : address.toNat + arg.offset + 2 ≤ memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel
      (.next (atCode (storeI16 (chargedStore store cfg.regularOpCost) index
        (address.toNat + arg.offset) memory value) limits stack frame callers code)) rest post) :
    WP cfg (fuel + 1)
      (.next (atCode store limits ((stack.push (.i32 address)).push (.i32 value))
        frame callers (.store .i32 (some 16) arg :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits ((stack.push (.i32 address)).push (.i32 value))
    frame callers (.store .i32 (some 16) arg :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hwrite := writeNat_i16 memory (address.toNat + arg.offset) value hbound
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (storeI16 (chargedStore store cfg.regularOpCost) index
        (address.toNat + arg.offset) memory value) limits stack frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.storeEffect, Exec.storeNat, Exec.i32,
      Exec.Effect.continue, c, atCode, chargeConfig, chargedStore, storeI16,
      Store.memOf, Store.setMemOf, getElem!_def, hmodule, hindex, hmemory, hwrite]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Bounds discharge the memory API directly; no load-result callback or
memory-well-formedness assumption is needed to execute the read. -/
theorem wp_i32_load16_u (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg)
    (address : UInt32) (mi : ModuleInst) (index : Nat) (memory : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (hindex : mi.memAddrs[0]? = some index)
    (hmemory : store.mems[index]? = some memory)
    (hbound : address.toNat + arg.offset + 2 ≤ memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + rest))
    (hnext : WP cfg fuel (.next (atCode (chargedStore store cfg.regularOpCost) limits
      (stack.push (.i32 (readI16 memory (address.toNat + arg.offset)))) frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (stack.push (.i32 address)) frame callers
      (.load .i32 (some {bits:=16,signed:=false}) arg :: code))) (cfg.regularOpCost + rest) post := by
  let c := atCode store limits (stack.push (.i32 address)) frame callers (.load .i32 (some {bits:=16,signed:=false}) arg :: code)
  have hcost : nextInstructionGas cfg c = cfg.regularOpCost := by
    simp [c, atCode, nextInstructionGas, Config.nextInstr?, linearInstruction, loopBackedge]
  have hstep : Exec.step (chargeConfig c (nextInstructionGas cfg c)).1 =
      .next (atCode (chargedStore store cfg.regularOpCost) limits (stack.push (.i32 (readI16 memory (address.toNat + arg.offset)))) frame callers code) := by
    rw [hcost]
    simp [Exec.step, Exec.instr, Exec.i32, Exec.Effect.continue, c, atCode, chargeConfig,
      chargedStore, Exec.loadNat, Store.memOf, getElem!_def, hmodule, hindex, hmemory,
      Memory.readNat, Memory.inBounds, hbound, readI16]
  have h := wp_pure_next (cfg := cfg) (fuel := fuel) (c := c) (rest := rest) (post := post)
  rw [hcost] at h
  apply h hcredits
  · rw [← hcost, hstep]; rfl
  · rw [← hcost, hstep]
    simp [frameTransitionGas, Config.callDepth, atCode, chargeConfig, c]
  · rw [← hcost, hstep]; exact hnext

/-- Explicit zero-extension: the high sixteen bits are zero. -/
theorem readI16_toNat (memory : Memory) (address : Nat) :
    (readI16 memory address).toNat=(memory.read8 address).toNat+256*(memory.read8 (address+1)).toNat := by
  have low := (memory.read8 address).toNat_lt
  have high := (memory.read8 (address+1)).toNat_lt
  simp only [readI16,List.range_succ,List.range_zero,List.nil_append,List.cons_append,List.foldr_cons,List.foldr_nil,
    Nat.zero_mul,Nat.zero_add,Nat.add_zero,UInt32.toNat_ofNat']
  omega

theorem readI16_lt (memory : Memory) (address : Nat) : (readI16 memory address).toNat<65536 := by
  rw [readI16_toNat]
  have low := (memory.read8 address).toNat_lt
  have high := (memory.read8 (address+1)).toNat_lt
  omega

/-- Packed stores retain exactly the low sixteen bits when read back unsigned. -/
theorem readI16_writeI16 (memory : Memory) (address : Nat) (value : UInt32)
    (hw : memory.wf) (hb : address+2≤memory.byteSize) :
    readI16 (writeI16 memory address value) address=UInt32.ofNat (value.toNat%65536) := by
  have spec := writeI16_spec memory address value hw hb
  have low : (writeI16 memory address value).read8 address=UInt8.ofNat value.toNat := by
    rw [spec.2.2.2]
    simp
  have high : (writeI16 memory address value).read8 (address+1)=UInt8.ofNat (value.toNat >>> 8) := by
    rw [spec.2.2.2]
    have inside : address≤address+1 ∧ address+1<address+2 := by omega
    rw [ite_eq_left inside]
    simp
  apply UInt32.toNat_inj.mp
  rw [readI16_toNat,low,high]
  simp only [UInt8.toNat_ofNat',UInt32.toNat_ofNat',Nat.shiftRight_eq_div_pow,Nat.reducePow]
  omega

end Wasm.Near.MeteredLogic
