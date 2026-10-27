import Proofs.TotalSupply
import NearVM.MeteredEntry

/-! Typed entry and the actual root activation of deployed ft_total_supply.
All local callee and representation/boundary assumptions remain explicit. -/
namespace WNear.Proofs.TotalSupplyEntry
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply

def entry (s : Store NearState) (limits : ExecLimits) (inst : Nat) : Wasm.Config NearState :=
  atCode s limits #[] (StorePair.voidFrame #[.i32 0] inst) [] WNear.Binary.TotalSupply.body

/-- The zero-argument export allocates its one zero-initialized i32 local. -/
theorem start (s : Store NearState) (limits : ExecLimits) (functionAddress inst : Nat)
    (hfunction : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.TotalSupply.signature inst WNear.Binary.TotalSupply.function)) :
    Exec.startWasm s limits functionAddress [] = some (entry s limits inst) := by
  simp [Exec.startWasm, hfunction, entry, atCode, StorePair.voidFrame,
    WNear.Binary.TotalSupply.signature, WNear.Binary.TotalSupply.function, ValType.default]

theorem activation_cost (cfg : WasmConfig) (s : Store NearState) (limits : ExecLimits) (inst : Nat) :
    activationGas cfg.regularOpCost (entry s limits inst).locals = 9 * cfg.regularOpCost :=
  WNear.Binary.TotalSupply.activation_cost _

/-- Only the actual root activation is charged here; the complete body budget
continues to count65scalarinstructions and eleven local call budgets. -/
def activated (cfg : WasmConfig) (s : Store NearState) : Store NearState :=
  chargedStore s (9 * cfg.regularOpCost)

/-- Root activation does not change the original STATE representation. -/
theorem activated_originalState (cfg : WasmConfig) (s : Store NearState) (state : WNear.State) :
    OriginalState (activated cfg s).host state ↔ OriginalState s.host state := by
  constructor
  · intro h; exact ⟨h.wellFormed, h.header⟩
  · intro h; exact ⟨h.wellFormed, h.header⟩

/-- Actual initialized execution includes the nine-unit activation and then
uses the checked76instruction body. Every missing functional callee contract
is still named in hcalls; no successful execution hypothesis is assumed. -/
theorem run_initialized (cfg : WasmConfig) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (inst : Nat) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (sp scratch pointer length : UInt32) (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hcalls : CallObligations cfg limits (StorePair.voidFrame #[.i32 scratch] inst)
      scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg (activated cfg s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (activated cfg s) after (StorePair.voidFrame #[.i32 0] inst) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg cost + rest)) :
    runInitialized cfg (1 + bodySteps steps) (.next (entry s limits inst)) = (.done [] final, none) := by
  have hc : s.host.gas.Credits (9 * cfg.regularOpCost + (bodyCost cfg cost + rest)) :=
    hgas.mono (by simp only [TotalSupply.entryCost]; omega)
  have hb := GasCounter.burn_credits s.host.gas (9 * cfg.regularOpCost) (bodyCost cfg cost + rest) hc
  have hcost := activation_cost cfg s limits inst
  have heCredit : s.host.gas.Credits
      (activationGas cfg.regularOpCost (entry s limits inst).locals + (bodyCost cfg cost + rest)) := by
    rw [hcost]; exact hc
  have he := runInitialized_entry cfg (1 + bodySteps steps) (bodyCost cfg cost + rest) (entry s limits inst) heCredit
  rw [hcost] at he
  rw [he]
  have hbody := TotalSupply.run_return cfg rest (activated cfg s) final limits inst before after cost steps
    mi globalIndex memoryIndex sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory
    hcalls hboundaries hinv hb.2.2.2
  exact hbody

/-- Compose actual function lookup, zero-argument initialization, activation,
the deployed body and its final void return. -/
theorem invoke (cfg : WasmConfig) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (functionAddress inst : Nat) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) (mi : ModuleInst) (globalIndex memoryIndex : Nat)
    (sp scratch pointer length : UInt32) (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hfunction : s.funcs[functionAddress]? = some
      (.wasm WNear.Binary.TotalSupply.signature inst WNear.Binary.TotalSupply.function))
    (hcalls : CallObligations cfg limits (StorePair.voidFrame #[.i32 scratch] inst)
      scratch pointer length before after cost steps)
    (hboundaries : ScalarBoundaries cfg (activated cfg s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (activated cfg s) after (StorePair.voidFrame #[.i32 0] inst) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg cost + rest)) :
    (Exec.startWasm s limits functionAddress []).map
      (fun c => runInitialized cfg (1 + bodySteps steps) (.next c)) = some (.done [] final, none) := by
  rw [start s limits functionAddress inst hfunction]
  have h := run_initialized cfg rest s final limits inst before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory hcalls hboundaries hinv hgas
  exact congrArg some h

end WNear.Proofs.TotalSupplyEntry
