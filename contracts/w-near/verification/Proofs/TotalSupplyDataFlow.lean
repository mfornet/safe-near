import Proofs.TotalSupplyRepresentation

/-! The getter's actual scalar boundaries thread one decoded supply value
through unwrap, the f414 copy and the serializer argument writes. -/
namespace WNear.Proofs.TotalSupplyDataFlow
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply WNear.Proofs.TotalSupplyFrontier
open WNear.Proofs.TotalSupplyRepresentation

/-- A single SDK-decoded U128 premise implies all three intermediate supply
representations. Store equalities are the actual proved scalar effects. -/
theorem decoded_to_serializer (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (initial final : Store NearState) (before after : Fin 11 → Store NearState)
    (scratch : UInt32) (globalIndex memoryIndex value : Nat) (copyMemory : Memory)
    (u : UnwrapResources cfg host limits (before 3) (after 3) scratch)
    (s : SupplyResources cfg host limits (before 4) (after 4) scratch)
    (huindex : u.memoryIndex = memoryIndex) (hsindex : s.memoryIndex = memoryIndex)
    (boundaries : ScalarBoundaries cfg.wasm initial final before after scratch globalIndex memoryIndex copyMemory)
    (hcopy : (after 4).mems[memoryIndex]? = some copyMemory)
    (hwf : copyMemory.wf) (hwidth : copyMemory.byteSize ≤ 2 ^ 32)
    (hspan : scratch.toNat + 128 ≤ copyMemory.byteSize)
    (decoded : U128At u.memory (scratch + 72).toNat value) :
    ∃ unwrapped serialization,
      (after 3).mems[memoryIndex]? = some unwrapped ∧
      U128At unwrapped (scratch + 32).toNat value ∧
      U128At copyMemory (scratch + 16).toNat value ∧
      (before 5).mems[memoryIndex]? = some serialization ∧
      U128At serialization (scratch + 112).toNat value := by
  obtain ⟨unwrapped, humemory, huvalue⟩ := unwrapped_supply cfg host limits (before 3) (after 3) scratch value u decoded
  rw [huindex] at humemory
  have hbefore : (before 4).mems[memoryIndex]? = some unwrapped := by
    rw [boundaries.supplyArgs]
    simpa only [StorePairCaller.paid, chargedStore] using humemory
  have hsmemory : (before 4).mems[memoryIndex]? = some s.memory := by
    rw [← hsindex]
    exact s.memory_eq
  have hsame : s.memory = unwrapped := Option.some.inj (hsmemory.symm.trans hbefore)
  have hsource : U128At s.memory (scratch + 32).toNat value := by
    rw [hsame]
    exact huvalue
  obtain ⟨returned, hrmemory, hrvalue⟩ := copied_supply cfg host limits (before 4) (after 4) scratch value s hsource
  rw [hsindex] at hrmemory
  have hr : returned = copyMemory := Option.some.inj (hrmemory.symm.trans hcopy)
  rw [hr] at hrvalue
  obtain ⟨serialization, hserialization, hv⟩ := serializer_input (after 4) cfg.wasm.regularOpCost memoryIndex
    scratch copyMemory value hcopy hwf hwidth hspan hrvalue
  refine ⟨unwrapped, serialization, humemory, huvalue, hrvalue, ?_, hv⟩
  rw [boundaries.serializeArgs]
  simpa only [StorePairCaller.paid, chargedStore] using hserialization

end WNear.Proofs.TotalSupplyDataFlow
