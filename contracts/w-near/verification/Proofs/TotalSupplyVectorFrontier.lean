import Proofs.TotalSupplyPanicFrontier
import Proofs.VectorDropPositiveCall

/-! The deployed getter frontier after proving both actual vector drops and the earlier concrete calls. -/
namespace WNear.Proofs.TotalSupplyVectorFrontier
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.TotalSupply
open WNear.Proofs.TotalSupplyFrontier
open WNear.Proofs.TotalSupplyReturnFrontier (ReturnResources)
open WNear.Proofs.TotalSupplyInterfaceFrontier (InstallResources)
open WNear.Proofs.TotalSupplyPanicFrontier (PanicResources)

structure RemainingCalls (cfg : WasmConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) : Prop where
  readState : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 219 [.i32 (scratch + 72)]
    (before 2) (after 2) (cost 2) (steps 2)
  serialize : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 96
    [.i32 (scratch + 72), .i32 (scratch + 112)] (before 5) (after 5) (cost 5) (steps 5)

structure DropResources (cfg : WasmConfig) (limits : ExecLimits)
    (before after : Store NearState) (vector : UInt32) (cost steps : Nat) where
  layout : VectorDropPositive.Layout
  heap : DeallocateCore.Layout
  address68 : Nat
  address237 : Nat
  address582 : Nat
  site : VectorDropPositive.Resources before 0 layout heap address68 address237 address582
  depth : 8 < limits.maxCallDepth
  vector_eq : layout.vector = vector
  after_eq : after = VectorDropPositive.callAfter before cfg.regularOpCost heap
  cost_eq : cost = 319 * cfg.regularOpCost
  steps_eq : steps = 230

theorem remaining_calls (cfg : RuntimeConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (returnDrop : DropResources cfg.wasm limits (before 9) (after 9) (scratch + 128) (cost 9) (steps 9))
    (stateDrop : DropResources cfg.wasm limits (before 10) (after 10) (scratch + 56) (cost 10) (steps 10)) :
    TotalSupplyPanicFrontier.RemainingCalls cfg.wasm limits scratch pointer length before after cost steps := by
  have actual9 := VectorDropPositive.calleeContract cfg.wasm (before 9) limits
    (StorePair.voidFrame #[.i32 scratch] 0) returnDrop.layout returnDrop.heap
    returnDrop.address68 returnDrop.address237 returnDrop.address582 returnDrop.site returnDrop.depth
  have h9 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 128)]
      (before 9) (after 9) (cost 9) (steps 9) := by
    simpa only [returnDrop.after_eq, returnDrop.cost_eq, returnDrop.steps_eq, returnDrop.vector_eq] using actual9
  have actual10 := VectorDropPositive.calleeContract cfg.wasm (before 10) limits
    (StorePair.voidFrame #[.i32 scratch] 0) stateDrop.layout stateDrop.heap
    stateDrop.address68 stateDrop.address237 stateDrop.address582 stateDrop.site stateDrop.depth
  have h10 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 56)]
      (before 10) (after 10) (cost 10) (steps 10) := by
    simpa only [stateDrop.after_eq, stateDrop.cost_eq, stateDrop.steps_eq, stateDrop.vector_eq] using actual10
  exact ⟨remaining.readState, remaining.serialize, h9, h10⟩

theorem assemble (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (panic : PanicResources cfg.wasm limits (before 0) (after 0) scratch (cost 0) (steps 0))
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (returnDrop : DropResources cfg.wasm limits (before 9) (after 9) (scratch + 128) (cost 9) (steps 9))
    (stateDrop : DropResources cfg.wasm limits (before 10) (after 10) (scratch + 56) (cost 10) (steps 10))
    (resources : HelperResources cfg host limits before after scratch cost steps) :
    CallObligations cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0)
      scratch pointer length before after cost steps := by
  exact TotalSupplyPanicFrontier.assemble cfg host limits scratch pointer length before after cost steps
    (remaining_calls cfg limits scratch pointer length before after cost steps remaining returnDrop stateDrop) panic installed returned resources

theorem invoke (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (panic : PanicResources cfg.wasm limits (before 0) (after 0) scratch (cost 0) (steps 0))
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (returnDrop : DropResources cfg.wasm limits (before 9) (after 9) (scratch + 128) (cost 9) (steps 9))
    (stateDrop : DropResources cfg.wasm limits (before 10) (after 10) (scratch + 56) (cost 10) (steps 10))
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[296]! []).map
      (fun c => runInitialized cfg.wasm (1 + bodySteps steps) (.next c)) = some (.done [] final, none) := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining panic installed returned returnDrop stateDrop resources
  exact LoadedCallees.totalSupply cfg host rest s final limits before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory hload calls hboundaries hinv hgas

/-- Original-store gas bounds for the same two-call frontier, including
activation and the nine concrete call sites. -/
theorem gas_bounds (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (panic : PanicResources cfg.wasm limits (before 0) (after 0) scratch (cost 0) (steps 0))
    (installed : InstallResources cfg.wasm limits (before 1) (after 1) scratch (cost 1) (steps 1))
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (returnDrop : DropResources cfg.wasm limits (before 9) (after 9) (scratch + 128) (cost 9) (steps 9))
    (stateDrop : DropResources cfg.wasm limits (before 10) (after 10) (scratch + 56) (cost 10) (steps 10))
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    final.host.gas.burnt ≤ s.host.gas.burnt + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.used ≤ s.host.gas.used + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.Credits rest := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining panic installed returned returnDrop stateDrop resources
  exact TotalSupplyBudget.gas_bounds cfg.wasm rest s final limits 0 before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory calls hboundaries hinv hgas

end WNear.Proofs.TotalSupplyVectorFrontier
