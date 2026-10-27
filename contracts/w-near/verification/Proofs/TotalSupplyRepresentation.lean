import Proofs.TotalSupplyFrontier
import Proofs.UnwrapStateEffects
import Proofs.StorePairReadback

/-! Actual memory effects establish the model U128 representation at the
getter's copy boundaries. This does not assume serialization or SDK success. -/
namespace WNear.Proofs.TotalSupplyRepresentation
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.TotalSupply WNear.Proofs.StorePair WNear.Proofs.StorePairReadback

/-- A word read depends on exactly its eight bytes. -/
theorem readI64_congr (left right : Memory) (address : Nat)
    (h : ∀ i, i < 8 → left.read8 (address + i) = right.read8 (address + i)) :
    readI64 left address = readI64 right address := by
  have hm : (List.range 8).map (fun i => left.read8 (address + i)) =
      (List.range 8).map (fun i => right.read8 (address + i)) := by
    apply List.map_congr_left
    intro i hi
    exact h i (List.mem_range.mp hi)
  have hd := congrArg (fun bytes => UInt64.ofNat (Memory.decodeLE bytes)) hm
  simpa only [Memory.decodeLE, List.foldr_map, readI64] using hd

/-- The checked pair write represents the mathematical U128 of its two words. -/
theorem pair_u128 (memory : Memory) (address : Nat) (lo hi : UInt64)
    (hwf : memory.wf) (hbound : address + 16 ≤ memory.byteSize) :
    U128At (pairMemory memory address lo hi) address (lo.toNat + 2 ^ 64 * hi.toNat) := by
  unfold U128At
  rw [pairMemory_read_low memory address lo hi hwf hbound,
    pairMemory_read_high memory address lo hi hwf hbound]

/-- f414's scratch then output stores preserve the original source U128 even
when its source, scratch and output regions overlap. -/
theorem sequential_u128 (memory : Memory) (scratch out source value : Nat)
    (hwf : memory.wf) (hscratch : scratch + 16 ≤ memory.byteSize)
    (hout : out + 16 ≤ memory.byteSize) (hvalue : U128At memory source value) :
    U128At (StorePairCaller.sequentialMemory memory scratch out (readI64 memory source)
      (readI64 memory (source + 8))) out value := by
  have hs := pairMemory_spec memory scratch (readI64 memory source) (readI64 memory (source + 8)) hwf hscratch
  have ho : out + 16 ≤ (pairMemory memory scratch (readI64 memory source) (readI64 memory (source + 8))).byteSize := by
    rw [hs.2.1]; exact hout
  have hp := pair_u128 _ out (readI64 memory source) (readI64 memory (source + 8)) hs.1 ho
  change (readI64 memory source).toNat + 2 ^ 64 * (readI64 memory (source + 8)).toNat = value at hvalue
  rw [hvalue] at hp
  exact hp

/-- A word read outside an actual word write is retained. -/
theorem readI64_write_disjoint (memory : Memory) (address source : Nat) (value : UInt64)
    (hwf : memory.wf) (hbound : address + 8 ≤ memory.byteSize)
    (hdisjoint : source + 8 ≤ address ∨ address + 8 ≤ source) :
    readI64 (writeI64 memory address value) source = readI64 memory source := by
  have hs := writeI64_spec memory address value hwf hbound
  apply readI64_congr
  intro i hi
  rw [hs.2.2.2]
  have hn : ¬ (address ≤ source + i ∧ source + i < address + 8) := by omega
  simp only [hn, ↓reduceIte]

/-- The serializer's two actual scalar stores, retaining sequential semantics. -/
def serializerMemory (memory : Memory) (scratch : UInt32) : Memory :=
  writeI64 (highMemory memory scratch) (scratch.toNat + 112)
    (readI64 (highMemory memory scratch) (scratch.toNat + 16))

/-- The first output write cannot affect the later source read on this
concrete stack layout. The result is the original low/high pair. -/
theorem serializer_pair (memory : Memory) (scratch : UInt32)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hspan : scratch.toNat + 128 ≤ memory.byteSize) :
    serializerMemory memory scratch = pairMemory memory (scratch.toNat + 112)
      (readI64 memory (scratch.toNat + 16)) (readI64 memory (scratch.toNat + 24)) := by
  have ha : (scratch + 24).toNat = scratch.toNat + 24 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hb : scratch.toNat + 120 + 8 ≤ memory.byteSize := by omega
  have hd : scratch.toNat + 16 + 8 ≤ scratch.toNat + 120 ∨
      scratch.toNat + 120 + 8 ≤ scratch.toNat + 16 := Or.inl (by omega)
  have hr := readI64_write_disjoint memory (scratch.toNat + 120) (scratch.toNat + 16)
    (readI64 memory (scratch + 24).toNat) hwf hb hd
  unfold serializerMemory highMemory
  rw [hr, ha]
  simp only [pairMemory, Nat.add_assoc, Nat.reduceAdd]

/-- Copying the decoded supply into the formatter's argument retains exactly
that original model value, rather than requiring a second representation premise. -/
theorem serializer_u128 (memory : Memory) (scratch : UInt32) (value : Nat)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hspan : scratch.toNat + 128 ≤ memory.byteSize)
    (hvalue : U128At memory (scratch + 16).toNat value) :
    U128At (serializerMemory memory scratch) (scratch + 112).toNat value := by
  have h16 : (scratch + 16).toNat = scratch.toNat + 16 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have h112 : (scratch + 112).toNat = scratch.toNat + 112 := by
    rw [UInt32.toNat_add]
    simp only [UInt32.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  have hb : scratch.toNat + 112 + 16 ≤ memory.byteSize := by omega
  have hp := pair_u128 memory (scratch.toNat + 112)
    (readI64 memory (scratch.toNat + 16)) (readI64 memory (scratch.toNat + 24)) hwf hb
  change (readI64 memory (scratch + 16).toNat).toNat +
    2 ^ 64 * (readI64 memory ((scratch + 16).toNat + 8)).toNat = value at hvalue
  rw [h16] at hvalue
  have hv : (readI64 memory (scratch.toNat + 16)).toNat +
      2 ^ 64 * (readI64 memory (scratch.toNat + 24)).toNat = value := by
    simpa only [Nat.add_assoc, Nat.reduceAdd] using hvalue
  rw [hv] at hp
  rw [serializer_pair memory scratch hwf hwidth hspan, h112]
  exact hp

/-- The concrete local f414 result establishes copiedSupply from the single
representation premise on the original decoded object. -/
theorem copied_supply (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) (value : Nat)
    (r : TotalSupplyFrontier.SupplyResources cfg host limits before after scratch)
    (hv : U128At r.memory (scratch + 32).toNat value) :
    ∃ memory, after.mems[r.memoryIndex]? = some memory ∧
      U128At memory (scratch + 16).toNat value := by
  have hb := StorePairAddresses.scratch_bounds r.memory scratch r.scratch_room r.scratch_end
  let result := StorePairCaller.sequentialMemory r.memory (scratch - 16).toNat (scratch + 16).toNat
    (readI64 r.memory (scratch + 32).toNat) (readI64 r.memory ((scratch + 32).toNat + 8))
  have hm : (TotalSupplyCallees.entered before cfg.wasm.regularOpCost (11 * cfg.wasm.regularOpCost)).mems[r.memoryIndex]? = some r.memory := r.memory_eq
  have hr := StorePairCaller.finalStore_memory
    (TotalSupplyCallees.entered before cfg.wasm.regularOpCost (11 * cfg.wasm.regularOpCost))
    cfg.wasm.regularOpCost r.globalIndex r.memoryIndex scratch (scratch + 16) r.memory
    (readI64 r.memory (scratch + 32).toNat) (readI64 r.memory ((scratch + 32).toNat + 8)) hm
  refine ⟨result, ?_, ?_⟩
  · exact (congrArg (fun store : Store NearState => store.mems[r.memoryIndex]?) r.after_eq).trans hr
  · exact sequential_u128 r.memory (scratch - 16).toNat (scratch + 16).toNat (scratch + 32).toNat
      value r.memory_wf hb.1 r.output_bound hv

/-- The actual ten scalar instructions install exactly serializerMemory. -/
theorem copyStore_memory (s : Store NearState) (op index : Nat) (scratch : UInt32) (memory : Memory)
    (hmemory : s.mems[index]? = some memory) :
    (copyStore s op index scratch memory).mems[index]? = some (serializerMemory memory scratch) := by
  have hp : (StorePairCaller.paid s op 6).mems[index]? = some memory := by
    simpa only [StorePairCaller.paid, chargedStore] using hmemory
  have hh := storeI64_memory (StorePairCaller.paid s op 6) index (scratch.toNat + 120) memory
    (readI64 memory (scratch + 24).toNat) hp
  have hl : (StorePairCaller.paid (copyHighStore s op index scratch memory) op 4).mems[index]? =
      some (highMemory memory scratch) := by
    simpa only [StorePairCaller.paid, chargedStore, copyHighStore, highMemory] using hh
  exact storeI64_memory _ index (scratch.toNat + 112) (highMemory memory scratch)
    (readI64 (highMemory memory scratch) (scratch.toNat + 16)) hl

/-- Formatter-input representation follows the actual scalar memory effect. -/
theorem serializer_input (s : Store NearState) (op index : Nat) (scratch : UInt32)
    (memory : Memory) (value : Nat) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hspan : scratch.toNat + 128 ≤ memory.byteSize)
    (hv : U128At memory (scratch + 16).toNat value) :
    ∃ result, (copyStore s op index scratch memory).mems[index]? = some result ∧
      U128At result (scratch + 112).toNat value :=
  ⟨serializerMemory memory scratch, copyStore_memory s op index scratch memory hmemory,
    serializer_u128 memory scratch value hwf hwidth hspan hv⟩

/-- At the actual getter call site, the unwrapped supply is derived from the
SDK-decoded source representation and the complete proved f155 effect. -/
theorem unwrapped_supply (cfg : RuntimeConfig) (host : NearState) (limits : ExecLimits)
    (before after : Store NearState) (scratch : UInt32) (value : Nat)
    (r : TotalSupplyFrontier.UnwrapResources cfg host limits before after scratch)
    (hv : U128At r.memory (scratch + 72).toNat value) :
    ∃ result, after.mems[r.memoryIndex]? = some result ∧ U128At result (scratch + 32).toNat value := by
  have h := UnwrapStateEffects.callAfter_u128 before cfg.wasm.regularOpCost r.memoryIndex
    (scratch + 32) (scratch + 72) r.memory value r.memory_eq r.memory_wf r.memory_width
    r.source_bound r.output_bound (UnwrapStateEffects.getter_disjoint scratch) hv
  obtain ⟨result, hm, hu⟩ := h
  refine ⟨result, ?_, hu⟩
  exact (congrArg (fun store : Store NearState => store.mems[r.memoryIndex]?) r.after_eq).trans hm

end WNear.Proofs.TotalSupplyRepresentation
