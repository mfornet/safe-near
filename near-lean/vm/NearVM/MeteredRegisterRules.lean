import NearVM.MeteredCall
import NearVM.MeteredHosts.RegisterReadMemory

/-! Typed direct calls to the actual metered register hosts, with derived execution. -/
namespace Wasm.Near.MeteredLogic.RegisterCalls
open MeteredHosts

/-- Actual host view after the caller's paid opcode. -/
def beforeCall (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) : HostStore NearState :=
  ⟨(store.memOf mi).getD (Memory.new 0 none), (chargedStore store cfg.regularOpCost).host⟩

def lengthAfter (st : HostStore NearState) : HostStore NearState :=
  RegisterRead.paid st [.ext "base"]

def readAfter (st : HostStore NearState) (ptr : UInt64) (bytes : List UInt8) : HostStore NearState :=
  { RegisterRead.paid st (RegisterRead.readCharges bytes.length) with mem := st.mem.writeList ptr.toNat bytes }

def lengthStore (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) : Store NearState :=
  let result := lengthAfter (beforeCall cfg store mi)
  Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi) result.host (some result.mem)

def readStore (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (ptr : UInt64) (bytes : List UInt8) : Store NearState :=
  let result := readAfter (beforeCall cfg store mi) ptr bytes
  Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi) result.host (some result.mem)

/-- One actual register_len opcode with original installed-code/data premises. -/
theorem wp_length_call (cfg : WasmConfig) (extra fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (functionIndex address memoryIndex : Nat) (mi : ModuleInst)
    (memory : Memory) (register : UInt64) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddress : mi.funcAddrs[functionIndex]? = some address)
    (hfunction : store.funcs[address]? = some (.host (metered extra "register_len" registerLenFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : store.mems[memoryIndex]? = some memory)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + (store.host.extCosts.cost "base" + rest)))
    (hnext : WP cfg fuel (.next (atCode (lengthStore cfg store mi)
      limits (base ++ [Value.i64 (RegisterRead.lengthValue (beforeCall cfg store mi) register)]).toArray frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (base ++ [Value.i64 register]).toArray
      frame callers (.call functionIndex :: code)))
      (cfg.regularOpCost + (store.host.extCosts.cost "base" + rest)) post := by
  have hmem : (beforeCall cfg store mi).mem = memory := by
    simp [beforeCall, Store.memOf, hmemoryIndex, hmemory]
  have hb := GasCounter.burn_credits store.host.gas cfg.regularOpCost
    (store.host.extCosts.cost "base" + rest) hcredits
  have hc : (beforeCall cfg store mi).host.gas.Credits
      (MeteredHosts.burnSum (beforeCall cfg store mi).host.extCosts [.ext "base"] + rest) := by
    rw [RegisterRead.length_cost]
    exact hb.2.2.2
  have hi := RegisterRead.length_contract extra (beforeCall cfg store mi) register rest hc
  have hburn : (lengthAfter (beforeCall cfg store mi)).host.gas.burnt =
      (chargedStore store cfg.regularOpCost).host.gas.burnt + store.host.extCosts.cost "base" := by
    simpa only [lengthAfter, RegisterRead.length_cost, beforeCall, chargedStore, chargeHost] using hi.2.1
  have hpromises : (lengthAfter (beforeCall cfg store mi)).host.gas.promises =
      (chargedStore store cfg.regularOpCost).host.gas.promises := hi.2.2.1
  apply wp_call_host cfg fuel (store.host.extCosts.cost "base") rest store limits base
    [Value.i64 register] [Value.i64 (RegisterRead.lengthValue (beforeCall cfg store mi) register)] frame callers code functionIndex address mi
    (metered extra "register_len" registerLenFn) (lengthAfter (beforeCall cfg store mi))
    hmodule haddress hfunction rfl hcredits hi.1
  · exact Nat.le_of_eq hburn
  · have hu : (lengthAfter (beforeCall cfg store mi)).host.gas.used =
        (chargedStore store cfg.regularOpCost).host.gas.used + store.host.extCosts.cost "base" := by
      simp only [GasCounter.used, hburn, hpromises]
      omega
    exact Nat.le_of_eq hu
  · exact hi.2.2.2
  · simpa only [lengthStore, List.append_nil] using hnext

/-- One actual read_register opcode with original installed-code/data premises. -/
theorem wp_read_call (cfg : WasmConfig) (extra fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (functionIndex address memoryIndex : Nat) (mi : ModuleInst)
    (memory : Memory) (register ptr : UInt64) (bytes : List UInt8) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddress : mi.funcAddrs[functionIndex]? = some address)
    (hfunction : store.funcs[address]? = some (.host (metered extra "read_register" readRegisterFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : store.mems[memoryIndex]? = some memory)
    (hreg : store.host.registers register.toNat = some bytes)
    (hbound : ptr.toNat + bytes.length ≤ memory.byteSize)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + (RegisterRead.readCost store.host bytes.length + rest)))
    (hnext : WP cfg fuel (.next (atCode (readStore cfg store mi ptr bytes)
      limits (base ++ []).toArray frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (base ++ [Value.i64 register, Value.i64 ptr]).toArray
      frame callers (.call functionIndex :: code)))
      (cfg.regularOpCost + (RegisterRead.readCost store.host bytes.length + rest)) post := by
  have hmem : (beforeCall cfg store mi).mem = memory := by
    simp [beforeCall, Store.memOf, hmemoryIndex, hmemory]
  have hb := GasCounter.burn_credits store.host.gas cfg.regularOpCost
    (RegisterRead.readCost store.host bytes.length + rest) hcredits
  have hc : (beforeCall cfg store mi).host.gas.Credits
      (MeteredHosts.burnSum (beforeCall cfg store mi).host.extCosts (RegisterRead.readCharges bytes.length) + rest) := by
    rw [RegisterRead.read_cost]
    exact hb.2.2.2
  have hbeforeReg : (beforeCall cfg store mi).host.registers register.toNat = some bytes := hreg
  have hbeforeBound : ptr.toNat + bytes.length ≤ (beforeCall cfg store mi).mem.byteSize := by
    rw [hmem]; exact hbound
  have hi := RegisterRead.read_contract extra (beforeCall cfg store mi) register ptr bytes rest
    hbeforeReg hbeforeBound hc
  have hburn : (readAfter (beforeCall cfg store mi) ptr bytes).host.gas.burnt =
      (chargedStore store cfg.regularOpCost).host.gas.burnt + RegisterRead.readCost store.host bytes.length := by
    simpa only [readAfter, RegisterRead.read_cost, beforeCall, chargedStore, chargeHost, RegisterRead.readCost] using hi.2.2.1
  have hpromises : (readAfter (beforeCall cfg store mi) ptr bytes).host.gas.promises =
      (chargedStore store cfg.regularOpCost).host.gas.promises := hi.2.2.2.1
  apply wp_call_host cfg fuel (RegisterRead.readCost store.host bytes.length) rest store limits base
    [Value.i64 register, Value.i64 ptr] [] frame callers code functionIndex address mi
    (metered extra "read_register" readRegisterFn) (readAfter (beforeCall cfg store mi) ptr bytes)
    hmodule haddress hfunction rfl hcredits hi.1
  · exact Nat.le_of_eq hburn
  · have hu : (readAfter (beforeCall cfg store mi) ptr bytes).host.gas.used =
        (chargedStore store cfg.regularOpCost).host.gas.used + RegisterRead.readCost store.host bytes.length := by
      simp only [GasCounter.used, hburn, hpromises]
      omega
    exact Nat.le_of_eq hu
  · exact hi.2.2.2.2
  · simpa only [readStore, List.append_nil] using hnext

end Wasm.Near.MeteredLogic.RegisterCalls
