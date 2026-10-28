import NearVM.MeteredI32MemoryRules

/-! Actual packed i64.store32: consume an i64 operand, write only its low32
bits, and charge one ordinary instruction. Original memory bounds suffice. -/
namespace Wasm.Near.MeteredLogic

/-- Each of the four written bytes agrees with UInt32 truncation. -/
theorem i64_store32_byte (value : UInt64) (i : Nat) (hi : i<4) :
    UInt8.ofNat (value.toNat >>> (8*i))=
      UInt8.ofNat ((UInt32.ofNat value.toNat).toNat >>> (8*i)) := by
  apply UInt8.toNat_inj.mp
  have cases:i=0 ∨i=1 ∨i=2 ∨i=3:=by omega
  rcases cases with h|h|h|h <;> subst i <;>
    simp only[UInt8.toNat_ofNat',UInt32.toNat_ofNat',Nat.shiftRight_eq_div_pow,Nat.reducePow,Nat.reduceMul,Nat.div_one] <;> omega

theorem writeNat_i64_store32 (memory : Memory) (address : Nat) (value : UInt64)
    (hbound : address+4≤memory.byteSize) :
    memory.writeNat address 4 value.toNat=some (writeI32 memory address (UInt32.ofNat value.toNat)) := by
  rw[Memory.writeNat_eq hbound]
  apply congrArg some
  simp only[writeI32,Memory.writeRun,List.range_succ,List.range_zero,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw[i64_store32_byte value 0 (by omega),i64_store32_byte value 1 (by omega),
    i64_store32_byte value 2 (by omega),i64_store32_byte value 3 (by omega)]

/-- Preserve every caller/local/label and operand prefix while installing the
four-byte write from the actual packed64 opcode. -/
theorem wp_i64_store32 (cfg : WasmConfig) (fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (stack : Array Value) (frame : CallFrame)
    (callers : List CallFrame) (code : List Instr) (arg : MemArg)
    (address : UInt32) (value : UInt64) (mi : ModuleInst) (index : Nat)
    (memory : Memory) (post : Post)
    (hmodule : store.modules[frame.inst]?=some mi)
    (hindex : mi.memAddrs[0]?=some index)
    (hmemory : store.mems[index]?=some memory)
    (hbound : address.toNat+arg.offset+4≤memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost+rest))
    (hnext : WP cfg fuel
      (.next (atCode (storeI32 (chargedStore store cfg.regularOpCost) index
        (address.toNat+arg.offset) memory (UInt32.ofNat value.toNat)) limits stack frame callers code)) rest post) :
    WP cfg (fuel+1)
      (.next (atCode store limits ((stack.push (.i32 address)).push (.i64 value))
        frame callers (.store .i64 (some 32) arg::code))) (cfg.regularOpCost+rest) post := by
  let c:=atCode store limits ((stack.push (.i32 address)).push (.i64 value)) frame callers (.store .i64 (some 32) arg::code)
  have hcost:nextInstructionGas cfg c=cfg.regularOpCost:=by
    simp[c,atCode,nextInstructionGas,Config.nextInstr?,linearInstruction,loopBackedge]
  have hwrite:=writeNat_i64_store32 memory (address.toNat+arg.offset) value hbound
  have hstep:Exec.step (chargeConfig c (nextInstructionGas cfg c)).1=
      .next (atCode (storeI32 (chargedStore store cfg.regularOpCost) index
        (address.toNat+arg.offset) memory (UInt32.ofNat value.toNat)) limits stack frame callers code) := by
    rw[hcost]
    simp[Exec.step,Exec.instr,Exec.storeEffect,Exec.storeNat,Exec.i32,Exec.Effect.continue,
      c,atCode,chargeConfig,chargedStore,storeI32,Store.memOf,Store.setMemOf,getElem!_def,
      hmodule,hindex,hmemory,hwrite]
  have h:=wp_pure_next (cfg:=cfg) (fuel:=fuel) (c:=c) (rest:=rest) (post:=post)
  rw[hcost] at h
  apply h hcredits
  · rw[←hcost,hstep];rfl
  · rw[←hcost,hstep]
    simp[frameTransitionGas,Config.callDepth,atCode,chargeConfig,c]
  · rw[←hcost,hstep];exact hnext
end Wasm.Near.MeteredLogic
