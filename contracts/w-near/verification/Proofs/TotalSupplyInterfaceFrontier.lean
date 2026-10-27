import Proofs.TotalSupplyReturnFrontier
import Proofs.InterfaceInstallCall

/-! The deployed getter frontier after proving actual first interface installation and SDK value return. -/
namespace WNear.Proofs.TotalSupplyInterfaceFrontier
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.TotalSupply
open WNear.Proofs.TotalSupplyFrontier
open WNear.Proofs.TotalSupplyReturnFrontier (ReturnResources)

structure RemainingCalls (cfg : WasmConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) : Prop where
  panicHook : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 522 []
    (before 0) (after 0) (cost 0) (steps 0)
  readState : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 219 [.i32 (scratch + 72)]
    (before 2) (after 2) (cost 2) (steps 2)
  serialize : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 96
    [.i32 (scratch + 72), .i32 (scratch + 112)] (before 5) (after 5) (cost 5) (steps 5)
  dropReturnVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 128)]
    (before 9) (after 9) (cost 9) (steps 9)
  dropStateVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 56)]
    (before 10) (after 10) (cost 10) (steps 10)

structure InstallResources (cfg : WasmConfig) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) (cost steps : Nat) where
  layout : InterfaceSetState.Layout
  initializerAddress : Nat
  site : InterfaceInstallCall.Resources before limits (StorePair.voidFrame #[.i32 scratch] 0) layout initializerAddress
  receiver : layout.receiver = 1
  vtable : layout.vtable = 1050188
  after_eq : after = InterfaceInstallCall.calledAfter before cfg.regularOpCost layout initializerAddress
  cost_eq : cost = 328 * cfg.regularOpCost
  steps_eq : steps = 226

theorem remaining_calls (cfg : RuntimeConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1)) :
    TotalSupplyReturnFrontier.RemainingCalls cfg.wasm limits scratch pointer length before after cost steps := by
  have actual := InterfaceInstallCall.calleeContract cfg.wasm (before 1) limits
    (StorePair.voidFrame #[.i32 scratch] 0) installed.layout installed.initializerAddress installed.site
  have h1 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 520 [.i32 1, .i32 1050188]
      (before 1) (after 1) (cost 1) (steps 1) := by
    simpa only [installed.after_eq, installed.cost_eq, installed.steps_eq, installed.receiver, installed.vtable] using actual
  exact ⟨remaining.panicHook, h1, remaining.readState, remaining.serialize, remaining.dropReturnVector, remaining.dropStateVector⟩

theorem assemble (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps) :
    CallObligations cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0)
      scratch pointer length before after cost steps := by
  exact TotalSupplyReturnFrontier.assemble cfg host limits scratch pointer length before after cost steps
    (remaining_calls cfg limits scratch pointer length before after cost steps remaining installed) returned resources

theorem invoke (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[296]! []).map
      (fun c => runInitialized cfg.wasm (1 + bodySteps steps) (.next c)) = some (.done [] final, none) := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining installed returned resources
  exact LoadedCallees.totalSupply cfg host rest s final limits before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory hload calls hboundaries hinv hgas

/-- Original-store gas bounds for the same five-call frontier, including
activation and the six concrete helper implementations. -/
theorem gas_bounds (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
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
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining installed returned resources
  exact TotalSupplyBudget.gas_bounds cfg.wasm rest s final limits 0 before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory calls hboundaries hinv hgas

end WNear.Proofs.TotalSupplyInterfaceFrontier
