import Proofs.TotalSupplyFrontier
import Proofs.ValueReturnWrapperCall

/-! The deployed getter frontier after proving the full SDK value-return path. -/
namespace WNear.Proofs.TotalSupplyReturnFrontier
open Wasm Wasm.Near MeteredLogic
open WNear.Proofs.TotalSupply
open WNear.Proofs.TotalSupplyFrontier

structure RemainingCalls (cfg : WasmConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState)
    (cost steps : Fin 11 → Nat) : Prop where
  panicHook : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 522 []
    (before 0) (after 0) (cost 0) (steps 0)
  installInterface : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 520 [.i32 1, .i32 1050188]
    (before 1) (after 1) (cost 1) (steps 1)
  readState : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 219 [.i32 (scratch + 72)]
    (before 2) (after 2) (cost 2) (steps 2)
  serialize : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 96
    [.i32 (scratch + 72), .i32 (scratch + 112)] (before 5) (after 5) (cost 5) (steps 5)
  dropReturnVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 128)]
    (before 9) (after 9) (cost 9) (steps 9)
  dropStateVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 56)]
    (before 10) (after 10) (cost 10) (steps 10)

structure ReturnResources (cfg : RuntimeConfig) (limits : ExecLimits)
    (before after : Store NearState) (scratch pointer length : UInt32) (cost steps : Nat) where
  layout : ValueReturnOuterBody.Layout
  memory : Memory
  sp : UInt32
  site : ValueReturnWrapperBody.Resources cfg.wasm cfg.fees.numExtraBytesRecord before limits
    (StorePair.voidFrame #[.i32 scratch] 0) sp pointer length memory layout
  after_eq : after = ValueReturnWrapperBody.calledStore cfg.wasm before sp pointer length memory layout
  cost_eq : cost = 278 * cfg.wasm.regularOpCost + ValueReturnHost.cost before.host layout.len.toNat
  steps_eq : steps = 182

theorem remaining_calls (cfg : RuntimeConfig) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8)) :
    TotalSupplyFrontier.RemainingCalls cfg.wasm limits scratch pointer length before after cost steps := by
  have actual := ValueReturnWrapperCall.calleeContract cfg.wasm cfg.fees.numExtraBytesRecord (before 8) limits
    (StorePair.voidFrame #[.i32 scratch] 0) returned.sp pointer length returned.memory returned.layout returned.site
  have h8 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 545 [.i32 pointer, .i32 length]
      (before 8) (after 8) (cost 8) (steps 8) := by
    simpa only [returned.after_eq, returned.cost_eq, returned.steps_eq] using actual
  exact ⟨remaining.panicHook, remaining.installInterface, remaining.readState, remaining.serialize,
    h8, remaining.dropReturnVector, remaining.dropStateVector⟩

theorem assemble (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps) :
    CallObligations cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0)
      scratch pointer length before after cost steps := by
  exact TotalSupplyFrontier.assemble cfg host limits scratch pointer length before after cost steps
    (remaining_calls cfg limits scratch pointer length before after cost steps remaining returned) resources

theorem invoke (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[296]! []).map
      (fun c => runInitialized cfg.wasm (1 + bodySteps steps) (.next c)) = some (.done [] final, none) := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining returned resources
  exact LoadedCallees.totalSupply cfg host rest s final limits before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory hload calls hboundaries hinv hgas

/-- Original-store gas bounds for the same six-call frontier, including
activation and the five concrete helper implementations. -/
theorem gas_bounds (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (returned : ReturnResources cfg limits (before 8) (after 8) scratch pointer length (cost 8) (steps 8))
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    final.host.gas.burnt ≤ s.host.gas.burnt + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.used ≤ s.host.gas.used + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.Credits rest := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining returned resources
  exact TotalSupplyBudget.gas_bounds cfg.wasm rest s final limits 0 before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory calls hboundaries hinv hgas

end WNear.Proofs.TotalSupplyReturnFrontier
