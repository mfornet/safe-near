import Proofs.ExpectResult
import NearVM.MeteredEntry

/-! Typed entry and entry-inclusive normal execution of deployed f158's accepted
branch. The caller opcode, panic branch, and loader are outside this contract. -/
namespace WNear.Proofs.ExpectResultEntry
open Wasm Wasm.Near MeteredLogic

/-- Actual parameter locals followed by the declared zero-initialized i32 local. -/
def entry (s : Store NearState) (limits : ExecLimits) (inst : Nat)
    (out source location : UInt32) : Config NearState :=
  atCode s limits #[]
    (StorePair.voidFrame #[.i32 out, .i32 source, .i32 location, .i32 0] inst)
    [] WNear.Binary.ExpectResult.body

theorem start (s : Store NearState) (limits : ExecLimits) (functionAddress inst : Nat)
    (out source location : UInt32)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.ExpectResult.signature inst WNear.Binary.ExpectResult.function)) :
    Exec.startWasm s limits functionAddress [.i32 out, .i32 source, .i32 location] =
      some (entry s limits inst out source location) := by
  simp [Exec.startWasm, hfunction, entry, atCode, StorePair.voidFrame,
    WNear.Binary.ExpectResult.signature, WNear.Binary.ExpectResult.function, ValType.default]

def finalStore (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) : Store NearState :=
  ExpectResultState.finalStore (chargedStore s (10 * op)) op globalIndex memoryIndex sp out source memory

/-- Activation costs ten units and the accepted body costs twenty-six. There
is no lower bound on the stack pointer and no alias-disjointness hypothesis. -/
theorem run_initialized (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (sp out source location : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hwidth : memory.byteSize ≤ 2 ^ 32)
    (houtBound : out.toNat + 12 ≤ memory.byteSize)
    (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1)
    (hc : s.host.gas.Credits (36 * cfg.regularOpCost + rest)) :
    runInitialized cfg 28 (.next (entry s limits inst out source location)) =
      (.done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory), none) := by
  have h0 : s.host.gas.Credits (10 * cfg.regularOpCost + (26 * cfg.regularOpCost + rest)) := hc.mono (by omega)
  have hb := GasCounter.burn_credits s.host.gas (10 * cfg.regularOpCost) (26 * cfg.regularOpCost + rest) h0
  have hcost : activationGas cfg.regularOpCost (entry s limits inst out source location).locals =
      10 * cfg.regularOpCost := WNear.Binary.ExpectResult.activation_cost _ _ _ _
  have hentry : s.host.gas.Credits
      (activationGas cfg.regularOpCost (entry s limits inst out source location).locals +
        (26 * cfg.regularOpCost + rest)) := by
    rw [hcost]; exact h0
  have he := runInitialized_entry cfg 28 (26 * cfg.regularOpCost + rest)
    (entry s limits inst out source location) hentry
  rw [hcost] at he
  rw [he]
  exact ExpectResult.run_return cfg rest (chargedStore s (10 * cfg.regularOpCost)) limits inst
    sp out source location mi globalIndex memoryIndex global memory hmodule hglobalIndex hglobal hsp
    hmemoryIndex hmemory hwf hwidth houtBound hsourceBound htag hb.2.2.2

/-- Real function lookup, activation and accepted-body execution composed. -/
theorem invoke (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (functionAddress inst : Nat) (sp out source location : UInt32)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (global : GlobalInst) (memory : Memory)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.ExpectResult.signature inst WNear.Binary.ExpectResult.function))
    (hmodule : s.modules[inst]? = some mi)
    (hglobalIndex : mi.globalAddrs[0]? = some globalIndex)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp)
    (hmemoryIndex : mi.memAddrs[0]? = some memoryIndex)
    (hmemory : s.mems[memoryIndex]? = some memory) (hwf : memory.wf)
    (hwidth : memory.byteSize ≤ 2 ^ 32)
    (houtBound : out.toNat + 12 ≤ memory.byteSize)
    (hsourceBound : source.toNat + 16 ≤ memory.byteSize)
    (htag : readI32 memory source.toNat ≠ 1)
    (hc : s.host.gas.Credits (36 * cfg.regularOpCost + rest)) :
    (Exec.startWasm s limits functionAddress [.i32 out, .i32 source, .i32 location]).map
      (fun c => runInitialized cfg 28 (.next c)) =
      some (.done [] (finalStore s cfg.regularOpCost globalIndex memoryIndex sp out source memory), none) := by
  rw [start s limits functionAddress inst out source location hfunction]
  exact congrArg some (run_initialized cfg rest s limits inst sp out source location mi globalIndex
    memoryIndex global memory hmodule hglobalIndex hglobal hsp hmemoryIndex hmemory hwf hwidth
    houtBound hsourceBound htag hc)

/-- Both entry and body gas are exact, with reservations and residual credits retained. -/
theorem finalStore_gas (s : Store NearState) (op globalIndex memoryIndex rest : Nat)
    (sp out source : UInt32) (memory : Memory) (hc : s.host.gas.Credits (36 * op + rest)) :
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.burnt = s.host.gas.burnt + 36 * op ∧
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.promises = s.host.gas.promises ∧
    (finalStore s op globalIndex memoryIndex sp out source memory).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (10 * op + (26 * op + rest)) := hc.mono (by omega)
  have hb := GasCounter.burn_credits s.host.gas (10 * op) (26 * op + rest) h0
  have hp := ExpectResultState.finalStore_gas (chargedStore s (10 * op)) op globalIndex memoryIndex rest
    sp out source memory hb.2.2.2
  have hburn : (chargedStore s (10 * op)).host.gas.burnt = s.host.gas.burnt + 10 * op := hb.2.1
  refine ⟨?_, hp.2.1.trans hb.2.2.1, hp.2.2⟩
  change (ExpectResultState.finalStore _ _ _ _ _ _ _ _).host.gas.burnt = _
  omega

theorem finalStore_memory (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) (hmemory : s.mems[memoryIndex]? = some memory) :
    (finalStore s op globalIndex memoryIndex sp out source memory).mems[memoryIndex]? =
      some (ExpectResultState.resultMemory memory out.toNat source.toNat) :=
  ExpectResultState.finalStore_memory (chargedStore s (10 * op)) op globalIndex memoryIndex
    sp out source memory hmemory

theorem finalStore_other_memory (s : Store NearState) (op globalIndex memoryIndex other : Nat)
    (sp out source : UInt32) (memory : Memory) (hne : other ≠ memoryIndex) :
    (finalStore s op globalIndex memoryIndex sp out source memory).mems[other]? = s.mems[other]? :=
  ExpectResultState.finalStore_other_memory (chargedStore s (10 * op)) op globalIndex memoryIndex other
    sp out source memory hne

theorem finalStore_globals (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) (global : GlobalInst)
    (hglobal : s.globals[globalIndex]? = some global) (hsp : global.value = .i32 sp) :
    (finalStore s op globalIndex memoryIndex sp out source memory).globals = s.globals :=
  ExpectResultState.finalStore_globals (chargedStore s (10 * op)) op globalIndex memoryIndex
    sp out source memory global hglobal hsp

theorem finalStore_host_frame (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) :
    { (finalStore s op globalIndex memoryIndex sp out source memory).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  simp only [finalStore, ExpectResultState.finalStore, ExpectResultState.highStore,
    ExpectResultState.lowStore, ExpectResultState.checked, ExpectResultState.reserved,
    StorePairCaller.paid, storeI64, storeI32, setGlobal, chargedStore, chargeHost]

theorem finalStore_resources (s : Store NearState) (op globalIndex memoryIndex : Nat)
    (sp out source : UInt32) (memory : Memory) :
    { finalStore s op globalIndex memoryIndex sp out source memory with
      mems := s.mems, globals := s.globals, host := s.host } = s := by
  simp only [finalStore, ExpectResultState.finalStore, ExpectResultState.highStore,
    ExpectResultState.lowStore, ExpectResultState.checked, ExpectResultState.reserved,
    StorePairCaller.paid, storeI64, storeI32, setGlobal, chargedStore]

end WNear.Proofs.ExpectResultEntry
