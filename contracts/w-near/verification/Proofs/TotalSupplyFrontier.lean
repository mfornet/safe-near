import Proofs.TotalSupplyCallees
import Proofs.UnwrapStateCallees
import Proofs.TotalSupplyBudget

/-! Actual ft_total_supply frontier after discharging f155, f414, f158 and f779.
Only the seven named remaining callees carry execution contracts; the proved
helpers require structural resources and equalities to their concrete effects. -/
namespace WNear.Proofs.TotalSupplyFrontier
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply
open WNear.Proofs.TotalSupplyCallees
set_option maxHeartbeats 800000

/-- The seven local call contracts still unproved on the deployed wrapper path.
The two occurrences of Vec.drop remain distinct call-site obligations. -/
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
  returnValue : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 545 [.i32 pointer, .i32 length]
    (before 8) (after 8) (cost 8) (steps 8)
  dropReturnVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 128)]
    (before 9) (after 9) (cost 9) (steps 9)
  dropStateVector : CalleeContract cfg limits (StorePair.voidFrame #[.i32 scratch] 0) 68 [.i32 (scratch + 56)]
    (before 10) (after 10) (cost 10) (steps 10)

/-- The accepted f155 site performs the actual forty-byte copy; no copy
execution contract is supplied. The nonzero tag is a representation premise. -/
structure UnwrapResources (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) where
  module : ModuleInst
  memoryIndex : Nat
  memory : Memory
  installed : LoadedCallees.Installed cfg host before module
  memoryIndex_eq : module.memAddrs[0]? = some memoryIndex
  memory_eq : before.mems[memoryIndex]? = some memory
  memory_wf : memory.wf
  memory_width : memory.byteSize ≤ 2 ^ 32
  source_bound : (scratch + 72).toNat + 40 ≤ memory.byteSize
  output_bound : (scratch + 32).toNat + 40 ≤ memory.byteSize
  present_tag : readI32 memory ((scratch + 72).toNat + 24) ≠ 0
  depth : 2 < limits.maxCallDepth
  after_eq : after = UnwrapStateCallees.callAfter before cfg.wasm.regularOpCost memoryIndex
    (scratch + 32) (scratch + 72) memory

/-- The f414 site reads the decoded object's U128 into scratch+16. These are
actual installed-code and native-memory facts, with its exact computed poststore. -/
structure SupplyResources (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) where
  module : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  memory : Memory
  installed : LoadedCallees.Installed cfg host before module
  globalIndex_eq : module.globalAddrs[0]? = some globalIndex
  global_eq : before.globals[globalIndex]? = some global
  sp_eq : global.value = .i32 scratch
  memoryIndex_eq : module.memAddrs[0]? = some memoryIndex
  memory_eq : before.mems[memoryIndex]? = some memory
  memory_wf : memory.wf
  memory_width : memory.byteSize ≤ 2 ^ 32
  scratch_room : 16 ≤ scratch.toNat
  scratch_end : scratch.toNat ≤ memory.byteSize
  output_bound : (scratch + 16).toNat + 16 ≤ memory.byteSize
  source_bound : (scratch + 32).toNat + 16 ≤ memory.byteSize
  depth : 2 < limits.maxCallDepth
  after_eq : after = supplyAfter before cfg.wasm.regularOpCost globalIndex memoryIndex scratch
    (scratch + 16) (scratch + 32) memory

/-- The f158 site accepts the actual Result tag and copies its payload to the
return vector. The panic branch is not silently assumed to return. -/
structure ExpectResources (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) where
  module : ModuleInst
  globalIndex : Nat
  memoryIndex : Nat
  global : GlobalInst
  memory : Memory
  installed : LoadedCallees.Installed cfg host before module
  globalIndex_eq : module.globalAddrs[0]? = some globalIndex
  global_eq : before.globals[globalIndex]? = some global
  sp_eq : global.value = .i32 scratch
  memoryIndex_eq : module.memAddrs[0]? = some memoryIndex
  memory_eq : before.mems[memoryIndex]? = some memory
  memory_wf : memory.wf
  memory_width : memory.byteSize ≤ 2 ^ 32
  output_bound : (scratch + 128).toNat + 12 ≤ memory.byteSize
  source_bound : (scratch + 72).toNat + 16 ≤ memory.byteSize
  accepted_tag : readI32 memory (scratch + 72).toNat ≠ 1
  depth : 1 < limits.maxCallDepth
  after_eq : after = expectAfter before cfg.wasm.regularOpCost globalIndex memoryIndex scratch
    (scratch + 128) (scratch + 72) memory

/-- The f779 site has the actual two-word sequential effect and no alias
restriction or whole-call execution premise. -/
structure PackResources (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) where
  module : ModuleInst
  memoryIndex : Nat
  memory : Memory
  installed : LoadedCallees.Installed cfg host before module
  memoryIndex_eq : module.memAddrs[0]? = some memoryIndex
  memory_eq : before.mems[memoryIndex]? = some memory
  memory_wf : memory.wf
  source_bound : (scratch + 128).toNat + 12 ≤ memory.byteSize
  output_bound : (scratch + 8).toNat + 8 ≤ memory.byteSize
  depth : 1 < limits.maxCallDepth
  after_eq : after = packedAfter before cfg.wasm.regularOpCost memoryIndex (scratch + 8) (scratch + 128) memory

/-- Structural resources for precisely the four proved helper call sites.
Their costs include the caller opcode and their fuel includes the free leave. -/
structure HelperResources (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (before after : Fin 11 → Store NearState) (scratch : UInt32) (cost steps : Fin 11 → Nat) where
  unwrap : UnwrapResources cfg host limits (before 3) (after 3) scratch
  cost_unwrap : cost 3 = 754 * cfg.wasm.regularOpCost
  steps_unwrap : steps 3 = 702
  supply : SupplyResources cfg host limits (before 4) (after 4) scratch
  expect : ExpectResources cfg host limits (before 6) (after 6) scratch
  pack : PackResources cfg host limits (before 7) (after 7) scratch
  cost_supply : cost 4 = 58 * cfg.wasm.regularOpCost
  steps_supply : steps 4 = 38
  cost_expect : cost 6 = 37 * cfg.wasm.regularOpCost
  steps_expect : steps 6 = 29
  cost_pack : cost 7 = 18 * cfg.wasm.regularOpCost
  steps_pack : steps 7 = 10

/-- Assemble the actual eleven-call wrapper interface from only seven local
execution contracts and the four kernel-proved helper implementations. -/
theorem assemble (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (scratch pointer length : UInt32) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (resources : HelperResources cfg host limits before after scratch cost steps) :
    CallObligations cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0)
      scratch pointer length before after cost steps := by
  let u := resources.unwrap
  have unwrap := UnwrapStateCallees.unwrapState_installed cfg host limits (StorePair.voidFrame #[.i32 scratch] 0)
    (before 3) (scratch + 32) (scratch + 72) u.module u.memoryIndex u.memory u.installed rfl
    u.memoryIndex_eq u.memory_eq u.memory_wf u.memory_width u.source_bound u.output_bound u.present_tag u.depth
  have h3 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 155
      [.i32 (scratch + 32), .i32 (scratch + 72)] (before 3) (after 3) (cost 3) (steps 3) := by
    simpa only [u.after_eq, resources.cost_unwrap, resources.steps_unwrap] using unwrap
  let s := resources.supply
  have supply := readSupply_installed cfg host limits (StorePair.voidFrame #[.i32 scratch] 0)
    (before 4) scratch (scratch + 16) (scratch + 32) s.module s.globalIndex s.memoryIndex s.global s.memory
    s.installed rfl s.globalIndex_eq s.global_eq s.sp_eq s.memoryIndex_eq s.memory_eq s.memory_wf s.memory_width
    s.scratch_room s.scratch_end s.output_bound s.source_bound s.depth
  have h4 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 414
      [.i32 (scratch + 16), .i32 (scratch + 32)] (before 4) (after 4) (cost 4) (steps 4) := by
    simpa only [s.after_eq, resources.cost_supply, resources.steps_supply] using supply
  let e := resources.expect
  have expect := expectResult_installed cfg host limits (StorePair.voidFrame #[.i32 scratch] 0)
    (before 6) scratch (scratch + 128) (scratch + 72) 1050984 e.module e.globalIndex e.memoryIndex e.global e.memory
    e.installed rfl e.globalIndex_eq e.global_eq e.sp_eq e.memoryIndex_eq e.memory_eq e.memory_wf e.memory_width
    e.output_bound e.source_bound e.accepted_tag e.depth
  have h6 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 158
      [.i32 (scratch + 128), .i32 (scratch + 72), .i32 1050984] (before 6) (after 6) (cost 6) (steps 6) := by
    simpa only [e.after_eq, resources.cost_expect, resources.steps_expect] using expect
  let p := resources.pack
  have pack := packWords_installed cfg host limits (StorePair.voidFrame #[.i32 scratch] 0)
    (before 7) (scratch + 8) (scratch + 128) p.module p.memoryIndex p.memory p.installed rfl
    p.memoryIndex_eq p.memory_eq p.memory_wf p.source_bound p.output_bound p.depth
  have h7 : CalleeContract cfg.wasm limits (StorePair.voidFrame #[.i32 scratch] 0) 779
      [.i32 (scratch + 8), .i32 (scratch + 128)] (before 7) (after 7) (cost 7) (steps 7) := by
    simpa only [p.after_eq, resources.cost_pack, resources.steps_pack] using pack
  exact ⟨remaining.panicHook, remaining.installInterface, remaining.readState, h3,
    h4, remaining.serialize, h6, h7, remaining.returnValue, remaining.dropReturnVector, remaining.dropStateVector⟩

/-- Actual loaded export execution now exposes only the seven remaining local
callee contracts. Helper resources contain no call or method execution callback. -/
theorem invoke (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (hload : LoadedCallees.Installed cfg host s mi)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    (Exec.startWasm s limits mi.funcAddrs[296]! []).map
      (fun c => runInitialized cfg.wasm (1 + bodySteps steps) (.next c)) = some (.done [] final, none) := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining resources
  exact LoadedCallees.totalSupply cfg host rest s final limits before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory hload calls hboundaries hinv hgas

/-- Original-store gas bounds for the same eight-call frontier, including
activation and the three concrete helper implementations. -/
theorem gas_bounds (cfg : RuntimeConfig) (host : NearState) (rest : Nat) (s final : Store NearState)
    (limits : ExecLimits) (before after : Fin 11 → Store NearState) (cost steps : Fin 11 → Nat)
    (mi : ModuleInst) (globalIndex memoryIndex : Nat) (sp scratch pointer length : UInt32)
    (originalGlobal finalGlobal : GlobalInst) (copyMemory sliceMemory : Memory)
    (remaining : RemainingCalls cfg.wasm limits scratch pointer length before after cost steps)
    (resources : HelperResources cfg host limits before after scratch cost steps)
    (hboundaries : ScalarBoundaries cfg.wasm (TotalSupplyEntry.activated cfg.wasm s) final before after scratch globalIndex memoryIndex copyMemory)
    (hinv : BoundaryInvariants (TotalSupplyEntry.activated cfg.wasm s) after (StorePair.voidFrame #[.i32 0] 0) mi globalIndex memoryIndex
      sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory)
    (hgas : s.host.gas.Credits (TotalSupply.entryCost cfg.wasm cost + rest)) :
    final.host.gas.burnt ≤ s.host.gas.burnt + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.used ≤ s.host.gas.used + TotalSupply.entryCost cfg.wasm cost ∧
    final.host.gas.Credits rest := by
  have calls := assemble cfg host limits scratch pointer length before after cost steps remaining resources
  exact TotalSupplyBudget.gas_bounds cfg.wasm rest s final limits 0 before after cost steps mi globalIndex memoryIndex
    sp scratch pointer length originalGlobal finalGlobal copyMemory sliceMemory calls hboundaries hinv hgas

end WNear.Proofs.TotalSupplyFrontier
