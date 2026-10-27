import NearVM.MeteredHosts.RegisterRead
import NearVM.MemoryListRules

/-! Functional frames and byte-level readback for metered register copies. -/
namespace Wasm.Near.MeteredHosts.RegisterRead

def readCost (host : NearState) (length : Nat) : Nat :=
  host.extCosts.cost "base" + host.extCosts.cost "read_register_base" +
  host.extCosts.cost "read_register_byte" * length + host.extCosts.cost "write_memory_base" +
  host.extCosts.cost "write_memory_byte" * length

theorem read_cost (host : NearState) (length : Nat) :
    burnSum host.extCosts (readCharges length) = readCost host length := by
  simp [burnSum, readCharges, burnCost, readCost, Nat.add_assoc]

theorem length_cost (host : NearState) :
    burnSum host.extCosts [.ext "base"] = host.extCosts.cost "base" := by
  simp [burnSum, burnCost]

/-- Successful or failing charge lists preserve all functional host fields;
only gas counters, profiles and the observed used-gas field are updated. -/
theorem paid_frame (st : HostStore NearState) (charges : List Charge)
    (hburn : ∀ c ∈ charges, BurnsOnly c) :
    paid st charges = { st with host := { st.host with
      gas := (paid st charges).host.gas
      gasProfile := (paid st charges).host.gasProfile
      actionProfile := (paid st charges).host.actionProfile
      context := { st.host.context with usedGas := (paid st charges).host.context.usedGas } } } := by
  have h := applyCharges_frame st.host charges hburn
  have hr := congrArg (fun ns : NearState => { ns with
    gas := (applyCharges st.host charges).1.gas
    gasProfile := (applyCharges st.host charges).1.gasProfile
    actionProfile := (applyCharges st.host charges).1.actionProfile
    context := { ns.context with usedGas := UInt64.ofNat (applyCharges st.host charges).1.gas.used } }) h
  have hs := congrArg (fun host : NearState => { st with host }) hr
  simpa only [paid, Output.paidStore] using hs

/-- Actual successful copying plus exact byte observations. All original data
and memory premises refer to the pre-call store. -/
theorem read_memory_contract (extra : Nat) (st : HostStore NearState) (register ptr : UInt64)
    (bytes : List UInt8) (rest : Nat)
    (hreg : st.host.registers register.toNat = some bytes)
    (hwf : st.mem.wf) (hspan : ptr.toNat + bytes.length ≤ st.mem.byteSize)
    (hcredits : st.host.gas.Credits (readCost st.host bytes.length + rest)) :
    let final := { paid st (readCharges bytes.length) with mem := st.mem.writeList ptr.toNat bytes }
    (metered extra "read_register" readRegisterFn).invoke st [.i64 register, .i64 ptr] = .Return [] final ∧
    final.mem.wf ∧ final.mem.byteSize = st.mem.byteSize ∧ final.mem.max = st.mem.max ∧
    final.mem.readList ptr.toNat bytes.length = bytes ∧
    (∀ j, final.mem.read8 j = if ptr.toNat ≤ j ∧ j < ptr.toNat + bytes.length
      then bytes[j - ptr.toNat]! else st.mem.read8 j) ∧
    final.host.registers = st.host.registers ∧
    final.host.gas.burnt = st.host.gas.burnt + readCost st.host bytes.length ∧
    final.host.gas.promises = st.host.gas.promises ∧ final.host.gas.Credits rest := by
  have hc : st.host.gas.Credits (burnSum st.host.extCosts (readCharges bytes.length) + rest) := by
    simpa only [read_cost] using hcredits
  have hr := read_contract extra st register ptr bytes rest hreg hspan hc
  have hm := Memory.writeList_spec bytes st.mem ptr.toNat hwf hspan
  refine ⟨hr.1, hm.1, hm.2.1, hm.2.2.1,
    Memory.readList_writeList bytes st.mem ptr.toNat hwf hspan, hm.2.2.2,
    hr.2.1, ?_, hr.2.2.2⟩
  simpa only [read_cost] using hr.2.2.1

end Wasm.Near.MeteredHosts.RegisterRead
