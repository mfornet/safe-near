import Binary.ValueReturnLeaf
import Proofs.ValueReturnHost
import Proofs.StorePairCallerState
import NearVM.MeteredEntry

/-! Actual f260 terminal trait method. Its caller's RefCell/vtable dispatch is
outside this local contract; its installed metered host call is proved here. -/
namespace WNear.Proofs.ValueReturnLeaf
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.StorePairCaller (paid paid_credits)
set_option maxHeartbeats 800000

/-- Two local reads precede the actual env.value_return call. -/
def finalStore (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (len ptr : UInt64) : Store NearState :=
  ValueReturnHost.callStore cfg (paid s cfg.regularOpCost 2) mi len ptr

theorem wp_body (cfg : WasmConfig) (extra fuel rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (base : List Value) (frame : CallFrame) (callers : List CallFrame)
    (code : List Instr) (len ptr : UInt64) (mi : ModuleInst) (hostAddress memoryIndex : Nat)
    (memory : Memory) (post : Post)
    (hlen : frame.locals[1]? = some (.i64 len)) (hptr : frame.locals[2]? = some (.i64 ptr))
    (hmodule : s.modules[frame.inst]? = some mi)
    (hhostAddress : mi.funcAddrs[20]? = some hostAddress)
    (hhost : s.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest))
    (hnext : WP cfg fuel (.next (atCode (finalStore cfg s mi len ptr) limits base.toArray
      frame callers code)) rest post) :
    WP cfg (fuel + 3) (.next (atCode s limits base.toArray frame callers
      (WNear.Binary.ValueReturnLeaf.body ++ code)))
      (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) post := by
  have hm2 : (paid s cfg.regularOpCost 2).modules[frame.inst]? = some mi := by simpa only [paid, chargedStore] using hmodule
  have hf2 : (paid s cfg.regularOpCost 2).funcs[hostAddress]? =
      some (.host (metered extra "value_return" valueReturnFn).toHostFn) := by simpa only [paid, chargedStore] using hhost
  have hmem2 : (paid s cfg.regularOpCost 2).mems[memoryIndex]? = some memory := by simpa only [paid, chargedStore] using hmemory
  have hcost : ValueReturnHost.cost (paid s cfg.regularOpCost 2).host len.toNat =
      ValueReturnHost.cost s.host len.toNat := rfl
  have h0 : s.host.gas.Credits (cfg.regularOpCost +
      (2 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) := hc.mono (by omega)
  rw [show 3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest =
    cfg.regularOpCost + (2 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) by omega]
  apply wp_local_get cfg (fuel + 2) (2 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)
    s limits base.toArray frame callers _ 1 (.i64 len) post hlen h0
  rw [show 2 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest =
    cfg.regularOpCost + (cfg.regularOpCost + (ValueReturnHost.cost s.host len.toNat + rest)) by omega]
  apply wp_local_get cfg (fuel + 1) (cfg.regularOpCost + (ValueReturnHost.cost s.host len.toNat + rest))
    _ limits _ frame callers _ 2 (.i64 ptr) post hptr
  · exact paid_credits s cfg.regularOpCost 1 _ (hc.mono (by omega))
  have hc2 : (paid s cfg.regularOpCost 2).host.gas.Credits
      (cfg.regularOpCost + (ValueReturnHost.cost (paid s cfg.regularOpCost 2).host len.toNat + rest)) := by
    rw [hcost]
    exact paid_credits s cfg.regularOpCost 2 _ (hc.mono (by omega))
  have hh := ValueReturnHost.wp_call cfg extra fuel rest (paid s cfg.regularOpCost 2)
    limits base frame callers code 20 hostAddress memoryIndex mi memory len ptr post
    hm2 hhostAddress hf2 hmemoryIndex hmem2 hfixed hbound hlimit hc2 hnext
  rw [hcost] at hh
  simpa [paid] using hh

/-- Accounting for the two local reads, the call opcode and all concrete host
charges. Functional fields do not enter the gas precondition implicitly. -/
theorem finalStore_gas (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (mi : ModuleInst) (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    (finalStore cfg s mi len ptr).host.gas.burnt = s.host.gas.burnt +
      3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat ∧
    (finalStore cfg s mi len ptr).host.gas.promises = s.host.gas.promises ∧
    (finalStore cfg s mi len ptr).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  let initial := paid s op 2
  let before := ValueReturnHost.beforeCall cfg initial mi
  have hc2 : s.host.gas.Credits (2 * op + (op + (ValueReturnHost.cost s.host len.toNat + rest))) := hc.mono (by dsimp [op]; omega)
  have hp := StorePairCaller.paid_gas s op 2 (op + (ValueReturnHost.cost s.host len.toNat + rest)) hc2
  have hr := paid_credits s op 2 (op + (ValueReturnHost.cost s.host len.toNat + rest)) hc2
  have hb := GasCounter.burn_credits initial.host.gas op (ValueReturnHost.cost s.host len.toNat + rest) hr
  have hmem : before.mem = memory := by
    simp [before, ValueReturnHost.beforeCall, initial, Store.memOf, paid, chargedStore, hmemoryIndex, hmemory]
  have hbound' : ptr.toNat + len.toNat ≤ before.mem.byteSize := by rw [hmem]; exact hbound
  have hcredit' : before.host.gas.Credits (ValueReturnHost.cost before.host len.toNat + rest) := hb.2.2.2
  have hi := ValueReturnHost.invoke_ok extra rest before len ptr hfixed hbound' hlimit hcredit'
  have hhost : (finalStore cfg s mi len ptr).host = (ValueReturnHost.after before len ptr).host := by
    simp only [finalStore, ValueReturnHost.callStore, initial, before, op, commitHost_host]
  have hopBurn : before.host.gas.burnt = initial.host.gas.burnt + op := hb.2.1
  have hopPromises : before.host.gas.promises = initial.host.gas.promises := hb.2.2.1
  have hcost : ValueReturnHost.cost before.host len.toNat = ValueReturnHost.cost s.host len.toNat := rfl
  rw [hhost]
  refine ⟨?_, hi.2.2.1.trans (hopPromises.trans hp.2), hi.2.2.2⟩
  rw [hi.2.1, hopBurn, hcost]
  dsimp only [initial] at *
  dsimp only [op] at *
  omega

/-- The terminal host selects exactly the requested memory bytes. -/
theorem finalStore_returnData (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory) :
    (finalStore cfg s mi len ptr).host.returnData = some (memory.readList ptr.toNat len.toNat) ∧
    (finalStore cfg s mi len ptr).host.returnedPromise = none := by
  have hmem : (ValueReturnHost.beforeCall cfg (paid s cfg.regularOpCost 2) mi).mem = memory := by
    simp [ValueReturnHost.beforeCall, Store.memOf, paid, chargedStore, hmemoryIndex, hmemory]
  simp only [finalStore, ValueReturnHost.callStore, commitHost_host, ValueReturnHost.after,
    Wasm.Near.MeteredHosts.Output.paidStore, hmem]
  exact ⟨trivial, trivial⟩

/-- Actual active f260 body returns normally in four steps. -/
theorem wp_return (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (receiver : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (hostAddress memoryIndex : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hhostAddress : mi.funcAddrs[20]? = some hostAddress)
    (hhost : s.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    WP cfg 4 (.next (atCode s limits #[] (StorePair.voidFrame #[.i32 receiver, .i64 len, .i64 ptr] inst)
      [] WNear.Binary.ValueReturnLeaf.body))
      (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)
      (fun remaining final error => remaining = rest ∧ final = .done [] (finalStore cfg s mi len ptr) ∧ error = none) := by
  have hg := (finalStore_gas cfg extra rest s mi memoryIndex memory len ptr hmemoryIndex hmemory
    hfixed hbound hlimit hc).2.2
  let post : Post := fun remaining final error => remaining = rest ∧
    final = .done [] (finalStore cfg s mi len ptr) ∧ error = none
  have hfinish := StorePair.wp_finish_void cfg 0 rest (finalStore cfg s mi len ptr) limits
    #[.i32 receiver, .i64 len, .i64 ptr] inst post hg ⟨rfl, rfl, rfl⟩
  exact wp_body cfg extra 1 rest s limits [] (StorePair.voidFrame #[.i32 receiver, .i64 len, .i64 ptr] inst)
    [] [] len ptr mi hostAddress memoryIndex memory post rfl rfl hmodule hhostAddress hhost
    hmemoryIndex hmemory hfixed hbound hlimit hc hfinish

theorem run_return (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (receiver : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (hostAddress memoryIndex : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hhostAddress : mi.funcAddrs[20]? = some hostAddress)
    (hhost : s.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    runMetered cfg 4 (.next (atCode s limits #[] (StorePair.voidFrame #[.i32 receiver, .i64 len, .i64 ptr] inst)
      [] WNear.Binary.ValueReturnLeaf.body)) = (.done [] (finalStore cfg s mi len ptr), none) := by
  obtain ⟨_, hp, _⟩ := (wp_return cfg extra rest s limits inst receiver len ptr mi hostAddress memoryIndex memory
    hmodule hhostAddress hhost hmemoryIndex hmemory hfixed hbound hlimit hc).result
  exact Prod.ext hp.2.1 hp.2.2

/-- Returning bytes never writes linear memory, including its unused receiver. -/
theorem finalStore_mems (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (memoryIndex : Nat) (memory : Memory) (len ptr : UInt64)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory) :
    (finalStore cfg s mi len ptr).mems = s.mems := by
  have hm := (Array.getElem?_eq_some_iff.mp hmemory).2
  simp [finalStore, ValueReturnHost.callStore, Exec.commitHost, Store.setMemOf,
    ValueReturnHost.after, ValueReturnHost.beforeCall, Wasm.Near.MeteredHosts.Output.paidStore,
    Store.memOf, paid, chargedStore, hmemoryIndex, hmemory]
  apply Array.ext
  · simp
  · intro j hj hk
    by_cases he : memoryIndex = j
    · subst j
      simp [hm]
    · exact Array.getElem_setIfInBounds_ne hk he

/-- All store fields apart from host and its unchanged memory are retained. -/
theorem finalStore_resources (cfg : WasmConfig) (s : Store NearState) (mi : ModuleInst)
    (len ptr : UInt64) :
    { finalStore cfg s mi len ptr with mems := s.mems, host := s.host } = s := by
  simp only [finalStore, ValueReturnHost.callStore, Exec.commitHost]
  cases hm : mi.memAddrs[0]? <;>
    simp only [Store.setMemOf, hm, paid, chargedStore]

/-- Root activation initializes exactly the decoded f260 locals. -/
def entry (s : Store NearState) (limits : ExecLimits) (inst : Nat)
    (receiver : UInt32) (len ptr : UInt64) : Config NearState :=
  atCode s limits #[] (StorePair.voidFrame #[.i32 receiver, .i64 len, .i64 ptr] inst)
    [] WNear.Binary.ValueReturnLeaf.body

theorem start (s : Store NearState) (limits : ExecLimits) (functionAddress inst : Nat)
    (receiver : UInt32) (len ptr : UInt64)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function)) :
    Exec.startWasm s limits functionAddress [.i32 receiver, .i64 len, .i64 ptr] =
      some (entry s limits inst receiver len ptr) := by
  simp [Exec.startWasm, hfunction, entry, atCode, StorePair.voidFrame,
    WNear.Binary.ValueReturnLeaf.signature, WNear.Binary.ValueReturnLeaf.function]

/-- Root entry adds eleven opcode units to the actual three-instruction body
and its concrete host charges. The caller's opcode is outside this total. -/
theorem run_initialized (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (receiver : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (hostAddress memoryIndex : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hhostAddress : mi.funcAddrs[20]? = some hostAddress)
    (hhost : s.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (14 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    runInitialized cfg 4 (.next (entry s limits inst receiver len ptr)) =
      (.done [] (finalStore cfg (chargedStore s (11 * cfg.regularOpCost)) mi len ptr), none) := by
  have h0 : s.host.gas.Credits (11 * cfg.regularOpCost +
      (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) := hc.mono (by omega)
  have hb := GasCounter.burn_credits s.host.gas (11 * cfg.regularOpCost)
    (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest) h0
  have hcost : activationGas cfg.regularOpCost (entry s limits inst receiver len ptr).locals =
      11 * cfg.regularOpCost := WNear.Binary.ValueReturnLeaf.activation_cost _ _ _ _
  have hentry : s.host.gas.Credits (activationGas cfg.regularOpCost
      (entry s limits inst receiver len ptr).locals +
        (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) := by
    rw [hcost]; exact h0
  have he := runInitialized_entry cfg 4
    (3 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)
    (entry s limits inst receiver len ptr) hentry
  rw [hcost] at he
  rw [he]
  exact run_return cfg extra rest (chargedStore s (11 * cfg.regularOpCost)) limits inst receiver len ptr
    mi hostAddress memoryIndex memory hmodule hhostAddress hhost hmemoryIndex hmemory hfixed hbound hlimit hb.2.2.2

/-- Actual typed function lookup, root activation, and host-backed execution. -/
theorem invoke (cfg : WasmConfig) (extra rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (functionAddress inst : Nat) (receiver : UInt32) (len ptr : UInt64)
    (mi : ModuleInst) (hostAddress memoryIndex : Nat) (memory : Memory)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.ValueReturnLeaf.signature inst WNear.Binary.ValueReturnLeaf.function))
    (hmodule : s.modules[inst]? = some mi) (hhostAddress : mi.funcAddrs[20]? = some hostAddress)
    (hhost : s.funcs[hostAddress]? = some (.host (metered extra "value_return" valueReturnFn).toHostFn))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hfixed : len ≠ u64Max) (hbound : ptr.toNat + len.toNat ≤ memory.byteSize)
    (hlimit : withinLimit s.host.config.maxReturnLen len.toNat = true)
    (hc : s.host.gas.Credits (14 * cfg.regularOpCost + ValueReturnHost.cost s.host len.toNat + rest)) :
    (Exec.startWasm s limits functionAddress [.i32 receiver, .i64 len, .i64 ptr]).map
      (fun c => runInitialized cfg 4 (.next c)) =
      some (.done [] (finalStore cfg (chargedStore s (11 * cfg.regularOpCost)) mi len ptr), none) := by
  rw [start s limits functionAddress inst receiver len ptr hfunction]
  exact congrArg some (run_initialized cfg extra rest s limits inst receiver len ptr mi hostAddress
    memoryIndex memory hmodule hhostAddress hhost hmemoryIndex hmemory hfixed hbound hlimit hc)

end WNear.Proofs.ValueReturnLeaf
