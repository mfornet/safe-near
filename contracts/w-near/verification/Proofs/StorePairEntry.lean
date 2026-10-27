import Proofs.StorePair
import Binary.StorePair

/-! Entry-inclusive contract for the actual deployed f566 helper. -/
namespace WNear.Proofs.StorePairEntry
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.StorePair

/-- Active entry configuration produced by the actual typed Wasm-function lookup. -/
def entry (s : Store NearState) (limits : ExecLimits) (inst : Nat)
    (address : UInt32) (lo hi : UInt64) : Config NearState :=
  atCode s limits #[] (voidFrame #[.i32 address, .i64 lo, .i64 hi] inst) [] body

/-- The lookup names the decoded deployed function, rather than an arbitrary
successful activation or execution equation. -/
theorem start (s : Store NearState) (limits : ExecLimits) (functionAddress inst : Nat)
    (address : UInt32) (lo hi : UInt64)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.StorePair.signature inst WNear.Binary.StorePair.function)) :
    Exec.startWasm s limits functionAddress [.i32 address, .i64 lo, .i64 hi] =
      some (entry s limits inst address lo hi) := by
  simp [Exec.startWasm, hfunction, entry, atCode, voidFrame,
    WNear.Binary.StorePair.signature, WNear.Binary.StorePair.function]

/-- Exact terminal store: entry is charged once, then the six body instructions
perform the two writes. The caller's call opcode is outside this allowance. -/
def finalStore (s : Store NearState) (op index address : Nat) (memory : Memory)
    (lo hi : UInt64) : Store NearState :=
  pairStore (chargedStore s (11 * op)) op index address memory lo hi

/-- The entry-inclusive interpreter executes normally with seventeen opcode
units, including rounded typed-frame activation. No execution-success premise
is assumed. -/
theorem run_initialized (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (inst : Nat) (address : UInt32) (lo hi : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hbound : address.toNat + 16 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (17 * cfg.regularOpCost + rest)) :
    runInitialized cfg 7 (.next (entry s limits inst address lo hi)) =
      (.done [] (finalStore s cfg.regularOpCost index address.toNat memory lo hi), none) := by
  have h0 : s.host.gas.Credits (11 * cfg.regularOpCost + (6 * cfg.regularOpCost + rest)) := by
    convert hgas using 1; omega
  have hburn := GasCounter.burn_credits s.host.gas (11 * cfg.regularOpCost)
    (6 * cfg.regularOpCost + rest) h0
  have hcost : entryCost cfg (.next (entry s limits inst address lo hi)) =
      11 * cfg.regularOpCost := by
    exact WNear.Binary.StorePair.activation_cost _ _ _ _
  have hcharge : chargeWasm (.next (entry s limits inst address lo hi))
      (11 * cfg.regularOpCost) =
      (.next (entry (chargedStore s (11 * cfg.regularOpCost)) limits inst address lo hi), none) := by
    simp [chargeWasm, chargeConfig, entry, atCode, chargedStore, chargeHost, hburn.1]
  unfold runInitialized
  rw [hcost, hcharge]
  exact run_return cfg rest (chargedStore s (11 * cfg.regularOpCost)) limits inst address lo hi
    mi index memory hmodule hindex hmemory hwf hbound hburn.2.2.2

/-- Compose real typed function activation and the entry-inclusive runner. -/
theorem invoke (cfg : WasmConfig) (rest : Nat) (s : Store NearState)
    (limits : ExecLimits) (functionAddress inst : Nat) (address : UInt32) (lo hi : UInt64)
    (mi : ModuleInst) (index : Nat) (memory : Memory)
    (hfunction : s.funcs[functionAddress]? =
      some (.wasm WNear.Binary.StorePair.signature inst WNear.Binary.StorePair.function))
    (hmodule : s.modules[inst]? = some mi) (hindex : mi.memAddrs[0]? = some index)
    (hmemory : s.mems[index]? = some memory) (hwf : memory.wf)
    (hbound : address.toNat + 16 ≤ memory.byteSize)
    (hgas : s.host.gas.Credits (17 * cfg.regularOpCost + rest)) :
    (Exec.startWasm s limits functionAddress [.i32 address, .i64 lo, .i64 hi]).map
      (fun c => runInitialized cfg 7 (.next c)) =
      some (.done [] (finalStore s cfg.regularOpCost index address.toNat memory lo hi), none) := by
  rw [start s limits functionAddress inst address lo hi hfunction]
  exact congrArg some (run_initialized cfg rest s limits inst address lo hi mi index memory
    hmodule hindex hmemory hwf hbound hgas)

/-- The full charge is exact and retains both promise reservations and the
    caller's remaining credits. -/
theorem finalStore_gas (s : Store NearState) (op index address rest : Nat)
    (memory : Memory) (lo hi : UInt64) (hgas : s.host.gas.Credits (17 * op + rest)) :
    (finalStore s op index address memory lo hi).host.gas.burnt = s.host.gas.burnt + 17 * op ∧
    (finalStore s op index address memory lo hi).host.gas.promises = s.host.gas.promises ∧
    (finalStore s op index address memory lo hi).host.gas.Credits rest := by
  have h0 : s.host.gas.Credits (11 * op + (6 * op + rest)) := by
    convert hgas using 1; omega
  have hb := GasCounter.burn_credits s.host.gas (11 * op) (6 * op + rest) h0
  have hg : (chargedStore s (11 * op)).host.gas.Credits (6 * op + rest) := hb.2.2.2
  have hp := pairStore_gas (chargedStore s (11 * op)) op index address rest memory lo hi hg
  have hs : (chargedStore s (11 * op)).host.gas.Credits (3 * op + (3 * op + rest)) := by
    convert hg using 1; omega
  have hc1 := storeWord_credits (chargedStore s (11 * op)) op index (address + 8)
    (3 * op + rest) memory hi hs
  have hc2 := storeWord_credits
    (storeWord (chargedStore s (11 * op)) op index (address + 8) memory hi)
    op index address rest (writeI64 memory (address + 8) hi) lo hc1
  have hburn : (chargedStore s (11 * op)).host.gas.burnt = s.host.gas.burnt + 11 * op := hb.2.1
  have hpromises : (chargedStore s (11 * op)).host.gas.promises = s.host.gas.promises := hb.2.2.1
  refine ⟨?_, ?_, hc2⟩
  · change (pairStore _ _ _ _ _ _ _).host.gas.burnt = _
    omega
  · exact hp.2.trans hpromises

/-- The resulting memory is the same pair write as the active-body contract. -/
theorem finalStore_memory (s : Store NearState) (op index address : Nat)
    (memory : Memory) (lo hi : UInt64) (hmemory : s.mems[index]? = some memory) :
    (finalStore s op index address memory lo hi).mems[index]? =
      some (pairMemory memory address lo hi) :=
  pairStore_memory (chargedStore s (11 * op)) op index address memory lo hi hmemory

/-- Function entry and execution retain every other memory. -/
theorem finalStore_other_memory (s : Store NearState) (op index address other : Nat)
    (memory : Memory) (lo hi : UInt64) (hne : other ≠ index) :
    (finalStore s op index address memory lo hi).mems[other]? = s.mems[other]? :=
  pairStore_other_memory (chargedStore s (11 * op)) op index address other memory lo hi hne

/-- All non-memory Wasm resources and all functional host fields are retained. -/
theorem finalStore_frame (s : Store NearState) (op index address : Nat)
    (memory : Memory) (lo hi : UInt64) :
    (finalStore s op index address memory lo hi).modules = s.modules ∧
    (finalStore s op index address memory lo hi).funcs = s.funcs ∧
    (finalStore s op index address memory lo hi).globals = s.globals ∧
    (finalStore s op index address memory lo hi).tables = s.tables ∧
    { (finalStore s op index address memory lo hi).host with
      gas := s.host.gas, gasProfile := s.host.gasProfile } = s.host := by
  simp only [finalStore, pairStore, storeWord, storeI64, charge3, chargedStore, chargeHost]
  exact ⟨trivial, trivial, trivial, trivial, trivial⟩

end WNear.Proofs.StorePairEntry
