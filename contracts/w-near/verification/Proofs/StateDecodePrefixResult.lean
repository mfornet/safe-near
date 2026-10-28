import Proofs.StateDecodePrefixHost
import Proofs.StateDecodePrefixFrame
import Proofs.StateDecodePrefixFinalMemoryFrame
import Proofs.StateDecodePrefixTag

/-! Complete actual316 typed-call memory, code, globals and exact gas endpoints. -/
namespace WNear.Proofs.StateDecodePrefix
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_charge)
attribute [local irreducible] callAfter after entered
private theorem entered_mems (s : Store NearState) (op : Nat) : (entered s op).mems=s.mems:=by unfold entered;rfl
private theorem entered_globals (s : Store NearState) (op : Nat) : (entered s op).globals=s.globals:=by unfold entered;rfl
private theorem entered_fields (s : Store NearState) (op : Nat) :
    (entered s op).funcs=s.funcs ∧(entered s op).modules=s.modules ∧(entered s op).tables=s.tables:=by unfold entered;exact ⟨rfl,rfl,rfl⟩

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q) := by
  have initial : (entered s cfg.regularOpCost).mems[p.memoryIndex]?=some p.memory := by rw[entered_mems];exact hm
  unfold callAfter
  exact after_memory cfg (entered s cfg.regularOpCost) p q hn hd initial

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout) :
    (callAfter cfg s p q).funcs=s.funcs ∧(callAfter cfg s p q).modules=s.modules ∧(callAfter cfg s p q).tables=s.tables := by
  have h:=after_fields cfg (entered s cfg.regularOpCost) p q
  have e:=entered_fields s cfg.regularOpCost
  unfold callAfter
  exact ⟨h.1.trans e.1,h.2.1.trans e.2.1,h.2.2.trans e.2.2⟩

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter cfg s p q).globals=s.globals := by
  have initial : (entered s cfg.regularOpCost).globals[p.globalIndex]?=some p.global := by rw[entered_globals];exact hg
  unfold callAfter
  exact (after_globals cfg (entered s cfg.regularOpCost) p q hn hd initial hv).trans (entered_globals s cfg.regularOpCost)

theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    GasUnits s (callAfter cfg s p q) cfg.regularOpCost (18*(count p).toNat+920) := by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only[Nat.one_mul] at one
  have start : GasUnits s (entered s cfg.regularOpCost) cfg.regularOpCost 13 := by
    simpa only[entered,Nat.reduceAdd] using one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 12)
  have tail:=after_gas cfg (entered s cfg.regularOpCost) p q hn hd
  unfold callAfter
  simpa only[bodyCost,show 13+(18*(count p).toNat+907)=18*(count p).toNat+920 by omega] using start.trans tail
end WNear.Proofs.StateDecodePrefix
