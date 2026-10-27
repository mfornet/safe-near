import Proofs.UnwrapStateCopyState

/-! The actual f951 loop installs the sequential forward-copy memory. -/
namespace WNear.Proofs.UnwrapStateCopyMemory
open Wasm Wasm.Near Wasm.Near.MeteredLogic
open WNear.Proofs.UnwrapStateCopy

/-- The runtime loop's memory agrees with the functional copy even for
arbitrary source/output overlap and a final pointer increment that wraps. -/
theorem loopStore_memory (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count : Nat) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize) :
    (loopStore s op index out source memory count).mems[index]? =
      some (ForwardCopyMemory.forward memory out.toNat source.toNat count) := by
  induction count generalizing s memory out source with
  | zero => exact hmemory
  | succ n ih =>
    by_cases hn : n = 0
    · subst n
      rw [loopStore_one]
      simpa only [chargedStore, ForwardCopyMemory.forward] using prefixStore_memory s op index out source memory hmemory
    · let written := writeByte memory out.toNat (readByteWord memory source.toNat)
      let next := chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op)
      have hb : out.toNat + 1 ≤ memory.byteSize := by omega
      have hs := writeByte_spec memory out.toNat (readByteWord memory source.toNat) hwf hb
      have ho : (out + 1).toNat = out.toNat + 1 := pointer_next out (by omega)
      have hr : (source + 1).toNat = source.toNat + 1 := pointer_next source (by omega)
      have hm : next.mems[index]? = some written := by
        simpa only [next, chargedStore, written] using prefixStore_memory s op index out source memory hmemory
      have hw : written.byteSize ≤ 2 ^ 32 := by rw [show written.byteSize = memory.byteSize from hs.2.1]; exact hwidth
      have hsource : (source + 1).toNat + n ≤ written.byteSize := by
        rw [hr, show written.byteSize = memory.byteSize from hs.2.1]; omega
      have hout : (out + 1).toNat + n ≤ written.byteSize := by
        rw [ho, show written.byteSize = memory.byteSize from hs.2.1]; omega
      have ht := ih next (out + 1) (source + 1) written hm hs.1 hw hsource hout
      rw [ho, hr] at ht
      rw [loopStore_succ]
      exact ht

/-- The installed result has precisely the checked copy footprint and remains
well formed; no source/output separation is needed. -/
theorem loopStore_footprint (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count : Nat) (hmemory : s.mems[index]? = some memory)
    (hwf : memory.wf) (hwidth : memory.byteSize ≤ 2 ^ 32)
    (hread : source.toNat + count ≤ memory.byteSize) (hwrite : out.toNat + count ≤ memory.byteSize) :
    ∃ result, (loopStore s op index out source memory count).mems[index]? = some result ∧
      result.wf ∧ result.byteSize = memory.byteSize ∧ result.max = memory.max ∧
      ∀ j, (j < out.toNat ∨ out.toNat + count ≤ j) → result.read8 j = memory.read8 j :=
  ⟨_, loopStore_memory s op index out source memory count hmemory hwf hwidth hread hwrite,
    ForwardCopyMemory.spec memory out.toNat source.toNat count hwf hwrite⟩

/-- One byte-copy iteration changes only memory and metering state. -/
theorem prefixStore_frame (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) :
    {prefixStore s op index out source memory with mems := s.mems, host := s.host} = s := by
  simp only [prefixStore, byteStore, StorePairCaller.paid, chargedStore, storeByte]

/-- All non-memory Wasm resources are retained by the complete loop. -/
theorem loopStore_frame (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count : Nat) :
    {loopStore s op index out source memory count with mems := s.mems, host := s.host} = s := by
  induction count generalizing s memory out source with
  | zero => rfl
  | succ n ih =>
    let next := chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op)
    have ht := ih next (out + 1) (source + 1) (writeByte memory out.toNat (readByteWord memory source.toNat))
    have hr := congrArg (fun st : Store NearState => {st with mems := s.mems, host := s.host}) ht
    have hp : {next with mems := s.mems, host := s.host} = s := by
      simpa only [next, chargedStore] using prefixStore_frame s op index out source memory
    rw [loopStore_succ]
    exact hr.trans hp

/-- A byte-copy prefix changes no functional host field. -/
theorem prefixStore_host_frame (s : Store NearState) (op index : Nat) (out source : UInt32) (memory : Memory) :
    {(prefixStore s op index out source memory).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  simp only [prefixStore, byteStore, StorePairCaller.paid, chargedStore, storeByte, chargeHost]

/-- The entire loop retains storage, return data, logs, registers, fees and
all other functional host fields. Exact gas is established separately. -/
theorem loopStore_host_frame (s : Store NearState) (op index : Nat) (out source : UInt32)
    (memory : Memory) (count : Nat) :
    {(loopStore s op index out source memory count).host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
  induction count generalizing s memory out source with
  | zero => rfl
  | succ n ih =>
    let next := chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op)
    have ht := ih next (out + 1) (source + 1) (writeByte memory out.toNat (readByteWord memory source.toNat))
    have hr := congrArg (fun host : NearState => {host with gas := s.host.gas, gasProfile := s.host.gasProfile}) ht
    have hp : {next.host with gas := s.host.gas, gasProfile := s.host.gasProfile} = s.host := by
      simpa only [next, chargedStore, chargeHost] using prefixStore_host_frame s op index out source memory
    rw [loopStore_succ]
    exact hr.trans hp

theorem prefixStore_other_memory (s : Store NearState) (op index other : Nat)
    (out source : UInt32) (memory : Memory) (hne : other ≠ index) :
    (prefixStore s op index out source memory).mems[other]? = s.mems[other]? := by
  simp only [prefixStore, byteStore, StorePairCaller.paid, chargedStore]
  exact storeByte_other_memory _ index out.toNat other memory (readByteWord memory source.toNat) hne

/-- Every other installed memory, including absent indices, is retained. -/
theorem loopStore_other_memory (s : Store NearState) (op index other : Nat)
    (out source : UInt32) (memory : Memory) (count : Nat) (hne : other ≠ index) :
    (loopStore s op index out source memory count).mems[other]? = s.mems[other]? := by
  induction count generalizing s memory out source with
  | zero => rfl
  | succ n ih =>
    let next := chargedStore (prefixStore s op index out source memory) ((if n = 0 then 1 else 2) * op)
    have ht := ih next (out + 1) (source + 1) (writeByte memory out.toNat (readByteWord memory source.toNat))
    have hp : next.mems[other]? = s.mems[other]? := by
      simpa only [next, chargedStore] using prefixStore_other_memory s op index other out source memory hne
    rw [loopStore_succ]
    exact ht.trans hp

end WNear.Proofs.UnwrapStateCopyMemory
