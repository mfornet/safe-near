import Proofs.TotalSupplyInterfaceFrontier
import Proofs.PanicHookCall

/-! The deployed getter frontier after proving actual panic setup, interface installation and SDK value return. -/
namespace WNear.Proofs.TotalSupplyPanicFrontier
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.TotalSupply
open WNear.Proofs.TotalSupplyFrontier
open WNear.Proofs.TotalSupplyReturnFrontier (ReturnResources)
open WNear.Proofs.TotalSupplyInterfaceFrontier (InstallResources)

structure RemainingCalls (cfg : WasmConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) : Prop where
  readState : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 219 [.i32 (scratch + 72)]
    (before 2) (after 2) (cost 2) (steps 2)
  serialize : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 96
    [.i32 (scratch + 72), .i32 (scratch + 112)] (before 5) (after 5) (cost 5) (steps 5)
  dropReturnVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 128)]
    (before 9) (after 9) (cost 9) (steps 9)
  dropStateVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 56)]
    (before 10) (after 10) (cost 10) (steps 10)

structure PanicResources (cfg : WasmConfig) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) (cost steps : Nat) where
  layout : PanicHookState.Layout
  site : PanicHookCall.Resources before limits (StorePair.voidFrame #[.i32 scratch] 0) layout
  after_eq : after = PanicHookCall.calledAfter before cfg.regularOpCost layout
  cost_eq : cost = 140 * cfg.regularOpCost
  steps_eq : steps = 104

theorem remaining_calls (cfg : RuntimeConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (panic : PanicResources cfg.wasm limits (before 0) (after 0) scratch (cost 0) (steps 0)) :
    TotalSupplyInterfaceFrontier.RemainingCalls cfg.wasm limits scratch pointer length before after cost steps := by
  have actual := PanicHookCall.calleeContract cfg.wasm (before 0) limits
    (StorePair.voidFrame #[.i32 scratch] 0) panic.layout panic.site
  have h0 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 522 []
      (before 0) (after 0) (cost 0) (steps 0) := by
    simpa only [panic.after_eq, panic.cost_eq, panic.steps_eq] using actual
  exact ⟨h0, remaining.readState, remaining.serialize, remaining.dropReturnVector, remaining.dropStateVector⟩

theorem assemble (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (panic : PanicResources cfg.wasm limits (before 0) (after 0) scratch (cost 0) (steps 0))
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps) :
    CallObligations cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0)
      scratch pointer length before after cost steps := by
  exact TotalSupplyInterfaceFrontier.assemble cfg host limits scratch pointer length before after cost steps
    (remaining_calls cfg limits scratch pointer length before after cost steps remaining panic) installed returned resources

theorem invoke (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (panic : PanicResources cfg.wasm limits (before 0) (after 0) scratch (cost 0) (steps 0))
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[296]! []).map
      (fun c => runInitialized cfg.wasm (1 + bodySteps steps) (.next c)) = some (.done [] final, none) := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining panic installed returned resources
  exact LoadedCallees.totalSupply cfg host rest s final limits before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory hload calls hboundaries hinv hgas

/-- Original-store gas bounds for the same four-call frontier, including
activation and the seven concrete helper implementations. -/
theorem gas_bounds (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (panic : PanicResources cfg.wasm limits (before 0) (after 0) scratch (cost 0) (steps 0))
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    final.host.gas.burnt ≤ s.host.gas.burnt + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.used ≤ s.host.gas.used + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.Credits rest := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining panic installed returned resources
  exact TotalSupplyBudget.gas_bounds cfg.wasm rest s final limits 0 before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory calls hboundaries hinv hgas

end WNear.Proofs.TotalSupplyPanicFrontier
