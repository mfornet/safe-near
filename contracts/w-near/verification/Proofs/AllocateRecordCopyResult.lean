import Proofs.AllocateRecordCopyCall

/-! Exact typed690 resources and alias-aware output readbacks. -/
namespace WNear.Proofs.AllocateRecordCopy
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (gasUnits_charge)
open AllocateGrowth (GasCost)
attribute [local irreducible] after callAfter allocatedMemory resultMemory readI32 AllocateRecord.finalMemory AllocateRecord.allocatedMemory

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.inner.memoryIndex]?=some p.inner.memory) :
    (callAfter cfg s p).mems[p.inner.memoryIndex]?=some (resultMemory p) := by
  unfold callAfter
  exact after_memory cfg (entered s cfg.regularOpCost) p hm

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).funcs=s.funcs ∧ (callAfter cfg s p).modules=s.modules ∧ (callAfter cfg s p).tables=s.tables := by
  unfold callAfter
  exact after_fields cfg (entered s cfg.regularOpCost) p

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.inner.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter cfg s p).globals=s.globals := by
  unfold callAfter
  exact after_globals cfg (entered s cfg.regularOpCost) p hn hg hv

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_reset (seed old host : NearState) : view seed (view old host)=view seed host := rfl
private theorem view_after (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (after cfg s p).host=view seed s.host := by
  have h := congrArg (view seed) (after_functional_host cfg s p)
  exact h

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter cfg s p).host=s.host
  rw [callAfter,view_after]
  rfl

theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (rest : Nat)
    (hc : s.host.gas.Credits ((bodyCost p+11)*cfg.regularOpCost+fee cfg p+rest)) :
    (callAfter cfg s p).host.gas.burnt=s.host.gas.burnt+(bodyCost p+11)*cfg.regularOpCost+fee cfg p ∧
    (callAfter cfg s p).host.gas.promises=s.host.gas.promises ∧ (callAfter cfg s p).host.gas.Credits rest := by
  let op := cfg.regularOpCost
  have a := gasUnits_charge s op 1
  simp only [Nat.one_mul] at a
  have b := a.trans (gasUnits_charge (chargedStore s op) op 10)
  have entry : GasCost s (entered s op) (11*op) := by simpa only [entered,Nat.reduceAdd] using GasCost.of_units b
  have all := entry.trans (after_gas cfg (entered s op) p)
  have ce : 11*op+(bodyCost p*cfg.regularOpCost+fee cfg p)=(bodyCost p+11)*cfg.regularOpCost+fee cfg p := by simp only [op,Nat.add_mul];omega
  rw [ce] at all
  simpa only [callAfter,op,Nat.add_assoc] using all rest hc

/-- The inner output address does not wrap: its eight bytes lie in the original
outer scratch span, whose bound and width are original native premises. -/
theorem innerOut_toNat (p : Layout) (hn : Native p) : p.inner.out.toNat=p.inner.sp.toNat+8 := by
  have width := hn.inner.allocation.width
  have bound := hn.scratchBound
  rw [hn.innerOut,UInt32.toNat_add]
  simp only [UInt32.toNat_ofNat,Nat.reducePow,Nat.reduceMod]
  apply Nat.mod_eq_of_lt
  omega

/-- The low output is the allocated pointer without any alias restriction. -/
theorem resultMemory_low (p : Layout) (hn : Native p) :
    readI32 (resultMemory p) p.out.toNat=AllocateRecord.result p.inner := by
  have shape := allocated_spec p hn
  rw [resultMemory,finalMemory_read_low (allocatedMemory p) p.out p.inner.sp shape.1 (hn.outputBound.trans shape.2.1)]
  have record := (AllocateRecord.finalMemory_spec p.inner hn.inner).2.2.2.1
  rw [innerOut_toNat p hn] at record
  simpa only [allocatedMemory] using record

/-- With aliases, the high output remains the actual read after the low write. -/
theorem resultMemory_high (p : Layout) (hn : Native p) :
    readI32 (resultMemory p) (p.out.toNat+4)=
      readI32 (firstMemory (allocatedMemory p) p.out p.inner.sp) (p.inner.sp.toNat+12) := by
  have shape := allocated_spec p hn
  simpa only [resultMemory] using finalMemory_read_high (allocatedMemory p) p.out p.inner.sp shape.1 (hn.outputBound.trans shape.2.1)

/-- Four-byte separation, rather than whole-record separation, recovers the
original size word emitted by689. -/
theorem resultMemory_high_size (p : Layout) (hn : Native p)
    (hsep : p.out.toNat+4≤p.inner.sp.toNat+12 ∨ p.inner.sp.toNat+16≤p.out.toNat) :
    readI32 (resultMemory p) (p.out.toNat+4)=p.inner.size := by
  have shape := allocated_spec p hn
  rw [resultMemory,finalMemory_read_high_original (allocatedMemory p) p.out p.inner.sp shape.1 (hn.outputBound.trans shape.2.1) hsep]
  have record := (AllocateRecord.finalMemory_spec p.inner hn.inner).2.2.2.2.1
  rw [innerOut_toNat p hn] at record
  simpa only [allocatedMemory,Nat.add_assoc,Nat.reduceAdd] using record
end WNear.Proofs.AllocateRecordCopy
