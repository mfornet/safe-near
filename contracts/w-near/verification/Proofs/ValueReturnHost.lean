import NearVM.MeteredHosts.Output
import NearVM.MeteredCall

/-! Actual metered value_return for a bounded fixed memory span. All host
charges, including output-data receipt bytes, are discharged from credits. -/
namespace WNear.Proofs.ValueReturnHost
open Wasm Wasm.Near MeteredLogic MeteredHosts

/-- Receipt byte fees depend on each receiver's same-account send fee. -/
def dataCost (host : NearState) (length : Nat) : Nat :=
  (host.outputDataReceivers.map fun receiver =>
    host.fees.newDataReceiptByte.send (receiver == host.context.currentAccountId) * length +
      host.fees.newDataReceiptByte.execution * length).sum

def cost (host : NearState) (length : Nat) : Nat :=
  host.extCosts.cost "base" + host.extCosts.cost "read_memory_base" +
    host.extCosts.cost "read_memory_byte" * length + dataCost host length

def plan (host : NearState) (length : Nat) : List Charge :=
  [.ext "base", .ext "read_memory_base", .ext "read_memory_byte" length,
    .burn (dataCost host length)]

/-- A fixed memory span is read directly, with no register sentinel. -/
theorem memory_span (st : HostStore NearState) (len ptr : UInt64)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ st.mem.byteSize) :
    getMemOrReg st ptr len = some (st.mem.readList ptr.toNat len.toNat) := by
  have hb : ¬ptr.toNat + len.toNat > st.mem.size * 65536 := by
    change ¬st.mem.byteSize < ptr.toNat + len.toNat
    omega
  simp only [getMemOrReg, ite_eq_right hfixed, ite_eq_right hb]

theorem charges (st : HostStore NearState) (len ptr : UInt64)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ st.mem.byteSize)
    (hlimit : withinLimit st.host.config.maxReturnLen len.toNat = true) :
    chargesBefore "value_return" st [.i64 len, .i64 ptr] = plan st.host len.toNat := by
  have hr := memory_span st len ptr hfixed hbound
  simp [chargesBefore, chargesBeforeUnvalidated, storageMutationPlan?, creationAccountArgs,
    argU64, spanLen, readSpan, hfixed, hr, hlimit, plan, dataCost]

theorem plan_cost (host : NearState) (length : Nat) :
    burnSum host.extCosts (plan host length) = cost host length := by
  simp [plan, cost, burnSum, burnCost, Nat.add_assoc]

def after (st : HostStore NearState) (len ptr : UInt64) : HostStore NearState :=
  let paid := Output.paidStore st (applyCharges st.host (plan st.host len.toNat)).1
  { paid with host := { paid.host with
      returnData := some (st.mem.readList ptr.toNat len.toNat), returnedPromise := none } }

/-- Complete actual host replay; no host invocation or charge-success equation
is assumed. The exact returned store records gas/profile/used-gas sync. -/
theorem invoke_ok (extra rest : Nat) (st : HostStore NearState) (len ptr : UInt64)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ st.mem.byteSize)
    (hlimit : withinLimit st.host.config.maxReturnLen len.toNat = true)
    (hcredits : st.host.gas.Credits (cost st.host len.toNat + rest)) :
    (metered extra "value_return" valueReturnFn).invoke st [.i64 len, .i64 ptr] =
      .Return [] (after st len ptr) ∧
    (after st len ptr).host.gas.burnt = st.host.gas.burnt + cost st.host len.toNat ∧
    (after st len ptr).host.gas.promises = st.host.gas.promises ∧
    (after st len ptr).host.gas.Credits rest := by
  have hburn : ∀ charge ∈ plan st.host len.toNat, BurnsOnly charge := by simp [plan, BurnsOnly]
  have hc : st.host.gas.Credits (burnSum st.host.extCosts (plan st.host len.toNat) + rest) := by
    rw [plan_cost]; exact hcredits
  have hp := applyCharges_credits st.host (plan st.host len.toNat) rest hburn hc
  have hf := applyCharges_frame st.host (plan st.host len.toNat) hburn
  have hconfig := congrArg (fun host : NearState => host.config) hf
  have hplan := charges st len ptr hfixed hbound hlimit
  have hcharge : applyCharges st.host (chargesBefore "value_return" st [.i64 len, .i64 ptr]) =
      ((applyCharges st.host (plan st.host len.toNat)).1, none) := by
    rw [hplan]; exact Prod.ext rfl hp.1
  have hread := memory_span (Output.paidStore st (applyCharges st.host (plan st.host len.toNat)).1)
    len ptr hfixed hbound
  have hpaidLimit : withinLimit (applyCharges st.host (plan st.host len.toNat)).1.config.maxReturnLen
      (st.mem.readList ptr.toNat len.toNat).length = true := by
    rw [Memory.readList_length, hconfig]; exact hlimit
  have hi := Output.metered_valueReturn_ok extra st len ptr
    (applyCharges st.host (plan st.host len.toNat)).1
    (st.mem.readList ptr.toNat len.toNat) hcharge hread hpaidLimit
  refine ⟨hi, ?_, hp.2.2.1, hp.2.2.2.2⟩
  simpa only [after, Output.paidStore, plan_cost] using hp.2.1


/-- View passed by the actual direct host call after paying its opcode. -/
def beforeCall (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst) : HostStore NearState :=
  ⟨(store.memOf mi).getD (Memory.new 0 none), (chargedStore store cfg.regularOpCost).host⟩

def callStore (cfg : WasmConfig) (store : Store NearState) (mi : ModuleInst)
    (len ptr : UInt64) : Store NearState :=
  let result := after (beforeCall cfg store mi) len ptr
  Exec.commitHost (chargedStore store cfg.regularOpCost) (some mi) result.host (some result.mem)

/-- A concrete installed metered value_return call, with its charge list and
functional host execution derived above, not supplied by a callback premise. -/
theorem wp_call (cfg : WasmConfig) (extra fuel rest : Nat) (store : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (functionIndex address memoryIndex : Nat) (mi : ModuleInst)
    (memory : Memory) (len ptr : UInt64) (post : Post)
    (hmodule : store.modules[frame.inst]? = some mi)
    (haddress : mi.funcAddrs[functionIndex]? = some address)
    (hfunction : store.funcs[address]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : store.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit store.host.config.maxReturnLen len.toNat = true)
    (hcredits : store.host.gas.Credits (cfg.regularOpCost + (cost store.host len.toNat + rest)))
    (hnext : WP cfg fuel (.next (atCode (callStore cfg store mi len ptr)
      limits base.toArray frame callers code)) rest post) :
    WP cfg (fuel + 1) (.next (atCode store limits (base ++ [Value.i64 len, Value.i64 ptr]).toArray
      frame callers (.call functionIndex :: code)))
      (cfg.regularOpCost + (cost store.host len.toNat + rest)) post := by
  have hmem : (beforeCall cfg store mi).mem = memory := by
    simp [beforeCall, Store.memOf, hmemoryIndex, hmemory]
  have hb := GasCounter.burn_credits store.host.gas cfg.regularOpCost
    (cost store.host len.toNat + rest) hcredits
  have hbeforeCredits : (beforeCall cfg store mi).host.gas.Credits
      (cost (beforeCall cfg store mi).host len.toNat + rest) := hb.2.2.2
  have hbeforeBound : ptr.toNat + len.toNat ≤ (beforeCall cfg store mi).mem.byteSize := by
    rw [hmem]; exact hbound
  have hi := invoke_ok extra rest (beforeCall cfg store mi) len ptr hfixed hbeforeBound hlimit hbeforeCredits
  apply wp_call_host cfg fuel (cost store.host len.toNat) rest store limits base
    [.i64 len, .i64 ptr] [] frame callers code functionIndex address mi
    (metered extra "value_return" valueReturnFn) (after (beforeCall cfg store mi) len ptr)
    hmodule haddress hfunction rfl hcredits hi.1
  · exact Nat.le_of_eq hi.2.1
  · have hu : (after (beforeCall cfg store mi) len ptr).host.gas.used =
        (chargedStore store cfg.regularOpCost).host.gas.used + cost store.host len.toNat := by
      have hburn : (after (beforeCall cfg store mi) len ptr).host.gas.burnt =
          (chargedStore store cfg.regularOpCost).host.gas.burnt + cost store.host len.toNat := hi.2.1
      have hpromises : (after (beforeCall cfg store mi) len ptr).host.gas.promises =
          (chargedStore store cfg.regularOpCost).host.gas.promises := hi.2.2.1
      simp only [GasCounter.used, hburn, hpromises]
      omega
    exact Nat.le_of_eq hu
  · exact hi.2.2.2
  · simpa only [callStore, List.append_nil] using hnext

end WNear.Proofs.ValueReturnHost
