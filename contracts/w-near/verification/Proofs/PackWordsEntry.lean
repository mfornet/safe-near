import Proofs.PackWords
import NearVM.MeteredEntry

/-! Actual typed entry and entry-inclusive execution for deployed f779. -/
namespace WNear.Proofs.PackWordsEntry
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.PackWords

def entry (s : Store NearState) (limits : ExecLimits) (inst : Nat)
    (out source : UInt32) : Config NearState :=
  atCode s limits #[] (StorePair.voidFrame #[.i32 out, .i32 source] inst) [] body

theorem start (s : Store NearState) (limits : ExecLimits) (functionAddress inst : Nat)
    (out source : UInt32)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.PackWords.signature inst WNear.Binary.PackWords.function)) :
    Exec.startWasm s limits functionAddress [.i32 out, .i32 source] =
      some (entry s limits inst out source) := by
  simp [Exec.startWasm, hfunction, entry, atCode, StorePair.voidFrame,
    WNear.Binary.PackWords.signature, WNear.Binary.PackWords.function]

def finalStore (s : Store NearState) (op index out source : Nat)
    (memory : Memory) : Store NearState :=
  packedStore (chargedStore s (9 * op)) op index out source memory

theorem run_initialized (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hread : source.toNat + 12 ≤ memory.byteSize) (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (17 * cfg.regularOpCost + rest)) :
    runInitialized cfg 9 (.next (entry s limits inst out source)) =
      (.done [] (finalStore s cfg.regularOpCost index out.toNat source.toNat memory), none) := by
  have h0 : s.host.gas.Credits (9 * cfg.regularOpCost + (8 * cfg.regularOpCost + rest)) :=
    hgas.mono (by omega)
  have hb := GasCounter.burn_credits s.host.gas (9 * cfg.regularOpCost)
    (8 * cfg.regularOpCost + rest) h0
  have hcost : activationGas cfg.regularOpCost (entry s limits inst out source).locals =
      9 * cfg.regularOpCost := WNear.Binary.PackWords.activation_cost _ _ _
  have hc : s.host.gas.Credits
      (activationGas cfg.regularOpCost (entry s limits inst out source).locals +
        (8 * cfg.regularOpCost + rest)) := by
    rw [hcost]
    exact h0
  have he := runInitialized_entry cfg 9 (8 * cfg.regularOpCost + rest)
    (entry s limits inst out source) hc
  rw [hcost] at he
  rw [he]
  exact run_return cfg rest (chargedStore s (9 * cfg.regularOpCost)) limits inst out source
    mi index memory hmodule hindex hmemory hwf hread hwrite hb.2.2.2

theorem invoke (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (functionAddress inst : Nat) (out source : UInt32)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.PackWords.signature inst WNear.Binary.PackWords.function))
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hread : source.toNat + 12 ≤ memory.byteSize) (hwrite : out.toNat + 8 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (17 * cfg.regularOpCost + rest)) :
    (Exec.startWasm s limits functionAddress [.i32 out, .i32 source]).map
      (fun c => runInitialized cfg 9 (.next c)) =
      some (.done [] (finalStore s cfg.regularOpCost index out.toNat source.toNat memory), none) := by
  rw [start s limits functionAddress inst out source hfunction]
  exact congrArg some (run_initialized cfg rest s limits inst out source mi index memory
    hmodule hindex hmemory hwf hread hwrite hgas)

theorem finalStore_gas (s : Store NearState) (op index out source rest : Nat)
    (memory : Memory) (hgas : s.host.gas.Credits (17 * op + rest)) :
    (finalStore s op index out source memory).host.gas.burnt = s.host.gas.burnt + 17 * op ∧
    (finalStore s op index out source memory).host.gas.promises = s.host.gas.promises ∧
    (finalStore s op index out source memory).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (9 * op + (8 * op + rest)) := hgas.mono (by omega)
  have hb := GasCounter.burn_credits s.host.gas (9 * op) (8 * op + rest) h0
  have hp := packedStore_gas (chargedStore s (9 * op)) op index out source rest memory hb.2.2.2
  have hc := packedStore_credits (chargedStore s (9 * op)) op index out source rest memory hb.2.2.2
  have hburn : (chargedStore s (9 * op)).host.gas.burnt = s.host.gas.burnt + 9 * op := hb.2.1
  refine ⟨?_, hp.2.trans hb.2.2.1, hc⟩
  change (packedStore _ _ _ _ _ _).host.gas.burnt = _
  omega

theorem finalStore_memory (s : Store NearState) (op index out source : Nat)
    (memory : Memory) (hmemory : s.mems[index]? = some memory) :
    (finalStore s op index out source memory).mems[index]? =
      some (packedMemory memory out source) :=
  packedStore_memory (chargedStore s (9 * op)) op index out source memory hmemory

theorem finalStore_other_memory (s : Store NearState) (op index out source other : Nat)
    (memory : Memory) (hne : other ≠ index) :
    (finalStore s op index out source memory).mems[other]? = s.mems[other]? :=
  packedStore_other_memory (chargedStore s (9 * op)) op index out source other memory hne

theorem finalStore_frame (s : Store NearState) (op index out source : Nat) (memory : Memory) :
    (finalStore s op index out source memory).modules = s.modules ∧
    (finalStore s op index out source memory).funcs = s.funcs ∧
    (finalStore s op index out source memory).globals = s.globals ∧
    (finalStore s op index out source memory).tables = s.tables ∧
    { (finalStore s op index out source memory).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  simp only [finalStore, packedStore, copyWord, storeI32, charge4, chargedStore, chargeHost]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end WNear.Proofs.PackWordsEntry
