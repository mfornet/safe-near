import Proofs.ValueReturnDispatch

/-! Gas and resource composition for the actual indirect value-return fragment. -/
namespace WNear.Proofs.ValueReturnDispatchGas
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.ValueReturnDispatch
open WNear.Proofs.StorePairCaller (paid paid_credits paid_gas paid_resources)

/-- Opcode charging retains every field used to price the actual host call,
including data-receipt receivers and the same-account fee test. -/
theorem cost_paid (s : Store NearState) (op count length : Nat) :
    ValueReturnHost.cost (paid s op count).host length = ValueReturnHost.cost s.host length := by
  induction count with
  | zero => rfl
  | succ n ih =>
    change ValueReturnHost.cost (paid s op n).host length = _
    exact ih

theorem cost_calleeStore (cfg : WasmConfig) (s : Store NearState) (length : Nat) :
    ValueReturnHost.cost (calleeStore cfg s).host length = ValueReturnHost.cost s.host length := rfl

/-- Nine preparation opcodes, one indirect-call opcode, eleven activation
units and the three-opcode f260 body leave the advertised residual credits. -/
theorem fragmentAfter_gas (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (mi : ModuleInst) (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hindex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (24 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    (fragmentAfter cfg s mi len ptr).host.gas.burnt = s.host.gas.burnt +
      24 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat ∧
    (fragmentAfter cfg s mi len ptr).host.gas.promises = s.host.gas.promises ∧
    (fragmentAfter cfg s mi len ptr).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let price := ValueReturnHost.cost s.host len.toNat
  let prepared := paid s op 9
  let entered := calleeStore cfg prepared
  have h0 : s.host.gas.Credits (9 * op + (15 * op + price + rest)) :=
    hc.mono (by dsimp [op, price]; omega)
  have hp := paid_gas s op 9 (15 * op + price + rest) h0
  have cp := paid_credits s op 9 (15 * op + price + rest) h0
  have ccall : prepared.host.gas.Credits (op + (11 * op + (3 * op + price + rest))) :=
    cp.mono (by omega)
  have hop := GasCounter.burn_credits prepared.host.gas op
    (11 * op + (3 * op + price + rest)) ccall
  have hactivation := GasCounter.burn_credits (chargedStore prepared op).host.gas
    (11 * op) (3 * op + price + rest) hop.2.2.2
  have ccost : ValueReturnHost.cost entered.host len.toNat = price := by
    simp only [entered, cost_calleeStore, prepared, cost_paid, price]
  have cb : entered.host.gas.Credits
      (3 * cfg.regularOpCost + ValueReturnHost.cost entered.host len.toNat + rest) := by
    rw [ccost]
    exact hactivation.2.2.2
  have hmem : entered.mems[memoryIndex]? = some memory := by
    have hframe := paid_resources s op 9
    have hfield := congrArg (fun t : Store NearState => t.mems[memoryIndex]?) hframe
    simpa only [entered, calleeStore, chargedStore, prepared] using hfield.trans hmemory
  have hl := ValueReturnLeaf.finalStore_gas cfg extra rest entered mi memoryIndex memory len ptr
    hindex hmem hfixed hbound hlimit cb
  have hentered : entered.host.gas.burnt = prepared.host.gas.burnt + op + 11 * op := by
    have ha : entered.host.gas.burnt = (chargedStore prepared op).host.gas.burnt + 11 * op :=
      hactivation.2.1
    rw [ha, show (chargedStore prepared op).host.gas.burnt = prepared.host.gas.burnt + op from hop.2.1]
  have hreserved : entered.host.gas.promises = prepared.host.gas.promises :=
    hactivation.2.2.1.trans hop.2.2.1
  change (ValueReturnLeaf.finalStore cfg entered mi len ptr).host.gas.burnt = _ ∧
    (ValueReturnLeaf.finalStore cfg entered mi len ptr).host.gas.promises = _ ∧
    (ValueReturnLeaf.finalStore cfg entered mi len ptr).host.gas.Credits rest
  refine ⟨?_, hl.2.1.trans (hreserved.trans hp.2), hl.2.2⟩
  rw [hl.1, ccost, hentered, hp.1]
  dsimp only [op, price]
  omega

theorem fragmentAfter_credits (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (mi : ModuleInst) (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hindex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (24 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    (fragmentAfter cfg s mi len ptr).host.gas.Credits rest :=
  (fragmentAfter_gas cfg extra rest s mi memoryIndex memory len ptr hindex hmemory
    hfixed hbound hlimit hc).2.2

/-- The fragment changes no non-host resource except committing its unchanged
memory. This unconditional frame also applies before span checks are supplied. -/
theorem fragmentAfter_resources (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (len ptr : UInt64) :
    {fragmentAfter cfg s mi len ptr with mems := s.mems, host := s.host} = s := by
  have h := ValueReturnLeaf.finalStore_resources cfg
    (calleeStore cfg (paid s cfg.regularOpCost 9)) mi len ptr
  have hr := congrArg (fun t : Store NearState => {t with host := s.host}) h
  simpa only [fragmentAfter, after, calleeStore, paid, chargedStore] using hr

/-- The actual memory selected by the host is committed back unchanged. -/
theorem fragmentAfter_mems (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hindex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) :
    (fragmentAfter cfg s mi len ptr).mems = s.mems := by
  have hmem : (calleeStore cfg (paid s cfg.regularOpCost 9)).mems[memoryIndex]? = some memory := by
    simpa only [calleeStore, paid, chargedStore] using hmemory
  have hh := ValueReturnLeaf.finalStore_mems cfg (calleeStore cfg (paid s cfg.regularOpCost 9))
    mi memoryIndex memory len ptr hindex hmem
  simpa only [fragmentAfter, after, calleeStore, paid, chargedStore] using hh

/-- With the actual memory resolution, all non-host store fields are framed. -/
theorem fragmentAfter_frame (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hindex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) :
    {fragmentAfter cfg s mi len ptr with host := s.host} = s := by
  have hr := fragmentAfter_resources cfg s mi len ptr
  rw [← fragmentAfter_mems cfg s mi memoryIndex memory len ptr hindex hmemory] at hr
  exact hr

/-- The committed terminal return selects the original memory span exactly. -/
theorem fragmentAfter_returnData (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hindex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) :
    (fragmentAfter cfg s mi len ptr).host.returnData = some (memory.readList ptr.toNat len.toNat) ∧
    (fragmentAfter cfg s mi len ptr).host.returnedPromise = none := by
  have hmem : (calleeStore cfg (paid s cfg.regularOpCost 9)).mems[memoryIndex]? = some memory := by
    simpa only [calleeStore, paid, chargedStore] using hmemory
  have hh := ValueReturnLeaf.finalStore_returnData cfg (calleeStore cfg (paid s cfg.regularOpCost 9))
    mi memoryIndex memory len ptr hindex hmem
  simpa only [fragmentAfter, after] using hh

end WNear.Proofs.ValueReturnDispatchGas
