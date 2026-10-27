import Proofs.StorePairCallerState
import Proofs.StorePairCaller
import Binary.StorePairCaller
import NearVM.MeteredEntry

/-! Typed entry for the actual deployed f414 stack-and-copy caller. -/
namespace WNear.Proofs.StorePairCallerEntry
open Wasm Wasm.Near Wasm.Near.MeteredLogic

def entry (s : Store NearState) (limits : ExecLimits) (inst : Nat)
    (out source : UInt32) : Config NearState :=
  atCode s limits #[]
    (StorePair.voidFrame #[.i32 out, .i32 source, .i32 0, .i64 0] inst)
    [] WNear.Binary.StorePairCaller.body

theorem start (s : Store NearState) (limits : ExecLimits) (functionAddress inst : Nat)
    (out source : UInt32)
    (hfunction : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.StorePairCaller.signature inst WNear.Binary.StorePairCaller.function)) :
    Exec.startWasm s limits functionAddress [.i32 out, .i32 source] =
      some (entry s limits inst out source) := by
  simp [Exec.startWasm, hfunction, entry, atCode, StorePair.voidFrame,
    WNear.Binary.StorePairCaller.signature, WNear.Binary.StorePairCaller.function,
    ValType.default]

theorem activation_cost (cfg : WasmConfig) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32) :
    activationGas cfg.regularOpCost (entry s limits inst out source).locals =
      11 * cfg.regularOpCost :=
  WNear.Binary.StorePairCaller.activation_cost _ _ _

/-- Entry charge followed by the checked sequential state effect. Execution
is established separately by the body composition theorem. -/
def finalStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) : Store NearState :=
  StorePairCaller.finalStore (chargedStore s (11 * op)) op globalIndex memoryIndex sp out memory
    (readI64 memory source.toNat) (readI64 memory (source.toNat + 8))

theorem finalStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out source : UInt32) (memory : Memory)
    (hgas : s.host.gas.Credits (57 * op + rest)) :
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.burnt =
      s.host.gas.burnt + 57 * op ∧
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.promises =
      s.host.gas.promises ∧
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (11 * op + (46 * op + rest)) := hgas.mono (by omega)
  have hb := GasCounter.burn_credits s.host.gas (11 * op) (46 * op + rest) h0
  have hp := StorePairCaller.finalStore_gas (chargedStore s (11 * op)) op globalIndex
    memoryIndex rest sp out memory (readI64 memory source.toNat)
    (readI64 memory (source.toNat + 8)) hb.2.2.2
  have hburn : (chargedStore s (11 * op)).host.gas.burnt = s.host.gas.burnt + 11 * op := hb.2.1
  refine ⟨?_, hp.2.1.trans hb.2.2.1, hp.2.2⟩
  change (StorePairCaller.finalStore _ _ _ _ _ _ _ _ _).host.gas.burnt = _
  omega

theorem finalStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory)
    (hmemory : s.mems[memoryIndex]? = some memory) :
    (finalStore s op globalIndex memoryIndex sp out source memory).mems[memoryIndex]? =
      some (StorePairCaller.sequentialMemory memory (sp - 16).toNat out.toNat
        (readI64 memory source.toNat) (readI64 memory (source.toNat + 8))) :=
  StorePairCaller.finalStore_memory (chargedStore s (11 * op)) op globalIndex memoryIndex
    sp out memory (readI64 memory source.toNat) (readI64 memory (source.toNat + 8)) hmemory

theorem finalStore_globals (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) (global : GlobalInst)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    (finalStore s op globalIndex memoryIndex sp out source memory).globals = s.globals :=
  StorePairCaller.finalStore_globals (chargedStore s (11 * op)) op globalIndex memoryIndex
    sp out memory (readI64 memory source.toNat) (readI64 memory (source.toNat + 8)) global hglobal hsp

theorem finalStore_other_memory (s : Store NearState) (op globalIndex memoryIndex other : Nat)
    (sp out source : UInt32) (memory : Memory) (hne : other ≠ memoryIndex) :
    (finalStore s op globalIndex memoryIndex sp out source memory).mems[other]? = s.mems[other]? :=
  StorePairCaller.finalStore_other_memory (chargedStore s (11 * op)) op globalIndex memoryIndex
    other sp out memory (readI64 memory source.toNat) (readI64 memory (source.toNat + 8)) hne

theorem finalStore_resources (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) :
    { finalStore s op globalIndex memoryIndex sp out source memory with
      mems := s.mems, globals := s.globals, host := s.host } = s := by
  have h := StorePairCaller.finalStore_resources (chargedStore s (11 * op)) op globalIndex
    memoryIndex sp out memory (readI64 memory source.toNat) (readI64 memory (source.toNat + 8))
  have hr := congrArg (fun store : Store NearState => {store with host := s.host}) h
  simpa only [finalStore, chargedStore] using hr

theorem finalStore_host_frame (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) :
    { (finalStore s op globalIndex memoryIndex sp out source memory).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  have h := StorePairCaller.finalStore_host_frame (chargedStore s (11 * op)) op
    globalIndex memoryIndex sp out memory (readI64 memory source.toNat)
    (readI64 memory (source.toNat + 8))
  have hr := congrArg (fun host : NearState =>
    {host with gas := s.host.gas, gasProfile := s.host.gasProfile}) h
  simpa only [finalStore, chargedStore, chargeHost] using hr

/-- Actual initialized execution, including the nested f566 activation and
both free frame leaves. The original stack global is restored. -/
theorem run_initialized (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32) (mi : ModuleInst)
    (globalIndex memoryIndex helperAddress : Nat) (global : GlobalInst) (memory : Memory) (sp : UInt32)
    (hmodule : s.modules[inst]? = some mi) (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hspValue : global.value = .i32 sp)
    (hhelper : mi.funcAddrs[566]? = some helperAddress)
    (hfunction : s.funcs[helperAddress]? =
      some (.wasm WNear.Binary.StorePair.signature inst WNear.Binary.StorePair.function))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (houtBound : out.toNat + 16 ≤ memory.byteSize) (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth) (hgas : s.host.gas.Credits (57 * cfg.regularOpCost + rest)) :
    runInitialized cfg 37 (.next (entry s limits inst out source)) =
      (.done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory), none) := by
  have h0 : s.host.gas.Credits (11 * cfg.regularOpCost + (46 * cfg.regularOpCost + rest)) :=
    hgas.mono (by omega)
  have hb := GasCounter.burn_credits s.host.gas (11 * cfg.regularOpCost)
    (46 * cfg.regularOpCost + rest) h0
  have hcost := activation_cost cfg s limits inst out source
  have hc : s.host.gas.Credits
      (activationGas cfg.regularOpCost (entry s limits inst out source).locals +
        (46 * cfg.regularOpCost + rest)) := by
    rw [hcost]
    exact h0
  have he := runInitialized_entry cfg 37 (46 * cfg.regularOpCost + rest)
    (entry s limits inst out source) hc
  rw [hcost] at he
  rw [he]
  have hm : (chargedStore s (11 * cfg.regularOpCost)).modules[inst]? = some mi := by
    simpa only [chargedStore] using hmodule
  have hg : (chargedStore s (11 * cfg.regularOpCost)).globals[globalIndex]? = some global := by
    simpa only [chargedStore] using hglobal
  have hf : (chargedStore s (11 * cfg.regularOpCost)).funcs[helperAddress]? =
      some (.wasm WNear.Binary.StorePair.signature inst WNear.Binary.StorePair.function) := by
    simpa only [chargedStore] using hfunction
  have hmem : (chargedStore s (11 * cfg.regularOpCost)).mems[memoryIndex]? = some memory := by
    simpa only [chargedStore] using hmemory
  exact StorePairCaller.run_return cfg rest (chargedStore s (11 * cfg.regularOpCost)) limits
    inst out source mi globalIndex memoryIndex helperAddress global memory sp hm hglobalIndex hg hspValue
    hhelper hf hmemoryIndex hmem hwf hwidth hsp hstack houtBound hsourceBound hdepth hb.2.2.2

/-- Compose the actual typed f414 lookup, initialization, body and return. -/
theorem invoke (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (functionAddress inst : Nat) (out source : UInt32) (mi : ModuleInst)
    (globalIndex memoryIndex helperAddress : Nat) (global : GlobalInst) (memory : Memory) (sp : UInt32)
    (hcaller : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.StorePairCaller.signature inst WNear.Binary.StorePairCaller.function))
    (hmodule : s.modules[inst]? = some mi) (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hspValue : global.value = .i32 sp)
    (hhelper : mi.funcAddrs[566]? = some helperAddress)
    (hfunction : s.funcs[helperAddress]? =
      some (.wasm WNear.Binary.StorePair.signature inst WNear.Binary.StorePair.function))
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex) (hmemory : s.mems[memoryIndex]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hsp : 16 ≤ sp.toNat) (hstack : sp.toNat ≤ memory.byteSize)
    (houtBound : out.toNat + 16 ≤ memory.byteSize) (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (hdepth : 1 < limits.maxCallDepth) (hgas : s.host.gas.Credits (57 * cfg.regularOpCost + rest)) :
    (Exec.startWasm s limits functionAddress [.i32 out, .i32 source]).map
      (fun c => runInitialized cfg 37 (.next c)) =
      some (.done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory), none) := by
  rw [start s limits functionAddress inst out source hcaller]
  exact congrArg some (run_initialized cfg rest s limits inst out source mi globalIndex memoryIndex
    helperAddress global memory sp hmodule hglobalIndex hglobal hspValue hhelper hfunction hmemoryIndex
    hmemory hwf hwidth hsp hstack houtBound hsourceBound hdepth hgas)

end WNear.Proofs.StorePairCallerEntry
