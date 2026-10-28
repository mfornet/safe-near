import Proofs.AllocatePositiveSkipCall
import Proofs.AllocateSkipGas

/-! Observable result, sequential memory, SP/code/host frames, and exact gas of
an actual positive581 call. No post-execution lookup is assumed. -/
namespace WNear.Proofs.AllocatePositiveSkip
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_charge)
set_option maxRecDepth 16384
attribute [local irreducible] callAfter after readI32 writeI32

theorem callAfter_memory (s : Store NearState) (op : Nat) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter s op p).mems[p.memoryIndex]?=some (finalMemory p) := by
  unfold callAfter
  exact after_memory (entered s op) op p hm

theorem callAfter_globals (s : Store NearState) (op : Nat) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter s op p).globals=s.globals := by
  unfold callAfter
  exact after_globals (entered s op) op p hg hv

theorem callAfter_fields (s : Store NearState) (op : Nat) (p : Layout) :
    (callAfter s op p).funcs=s.funcs ∧ (callAfter s op p).modules=s.modules ∧ (callAfter s op p).tables=s.tables := by
  unfold callAfter
  exact after_fields (entered s op) op p

theorem gasUnits_entered (s : Store NearState) (op : Nat) : GasUnits s (entered s op) op 12 := by
  have first := gasUnits_charge s op 1
  simp only [Nat.one_mul] at first
  have h := first.trans (gasUnits_charge (chargedStore s op) op 11)
  simpa only [entered,Nat.one_mul,Nat.reduceAdd] using h

theorem gasUnits_callAfter (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (callAfter s op p) op 429 := by
  have h := (gasUnits_entered s op).trans (gasUnits_after (entered s op) op p)
  simpa only [callAfter,Nat.reduceAdd] using h

theorem callAfter_gas (s : Store NearState) (op rest : Nat) (p : Layout)
    (hc : s.host.gas.Credits (429*op+rest)) :
    (callAfter s op p).host.gas.burnt=s.host.gas.burnt+429*op ∧
    (callAfter s op p).host.gas.promises=s.host.gas.promises ∧
    (callAfter s op p).host.gas.Credits rest := gasUnits_callAfter s op p rest hc

private def mask (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem mask_rebase (seed base host : NearState) (h : mask base host=base) : mask seed host=mask seed base := by
  have hh := congrArg (mask seed) h
  simpa only [mask] using hh
private theorem mask_charge (seed : NearState) (s : Store NearState) (cost : Nat) :
    mask seed (chargedStore s cost).host=mask seed s.host := rfl

theorem callAfter_functional_host (s : Store NearState) (op : Nat) (p : Layout) :
    {(callAfter s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h : mask (entered s op).host (after (entered s op) op p).host=(entered s op).host := after_functional_host (entered s op) op p
  have rebased := mask_rebase s.host (entered s op).host (after (entered s op) op p).host h
  have right : mask s.host (entered s op).host=s.host := by simp only [entered,mask_charge]; rfl
  simpa only [mask,callAfter] using rebased.trans right

theorem result_nonzero_and_span (p : Layout) (hn : Native p) :
    result p≠0 ∧ (result p).toNat+(words p).toNat*4≤p.memory.byteSize := by
  have r := AllocateSkip.result_nonzero_and_span (searchLayout p) hn.search
  have bound := (scratch_numbers p hn).2.2.1
  have m := writeI32_spec p.memory ((scratch p).toNat+12) (readI32 p.memory p.allocator.toNat) hn.wf (by omega)
  have width := (AllocateSkip.resultMemory_spec (searchLayout p) hn.search).2.1.trans m.2.1
  exact ⟨r.1,r.2.trans_eq width⟩
end WNear.Proofs.AllocatePositiveSkip
