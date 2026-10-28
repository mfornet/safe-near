import Proofs.StateDecodeBorshCall
import Proofs.StateDecodeBorshFrame
import Proofs.StateDecodeBorshMemoryFrame
import Proofs.StateDecodeBorshGlobals
import Proofs.StateDecodeBorshHost
import Proofs.StateDecodeBorshHeader

/-! Complete actual425 typed-call memory, code, globals and exact gas endpoints. -/
namespace WNear.Proofs.StateDecodeBorsh
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
    (hn : Native p) (hd : AcceptedDomain p q) (hg : s.globals[p.globalIndex]?=some p.global425) (hv : p.global425.value=.i32 p.sp425) :
    (callAfter cfg s p q).globals=s.globals := by
  have initial : (entered s cfg.regularOpCost).globals[p.globalIndex]?=some p.global425 := by rw[entered_globals];exact hg
  unfold callAfter
  exact (after_globals cfg (entered s cfg.regularOpCost) p q hn hd initial hv).trans (entered_globals s cfg.regularOpCost)

theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) (q : StateDecodeVectorCopy.Layout)
    (hn : Native p) (hd : AcceptedDomain p q) :
    GasUnits s (callAfter cfg s p q) cfg.regularOpCost (18*(count p).toNat+1449) := by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only[Nat.one_mul] at one
  have start : GasUnits s (entered s cfg.regularOpCost) cfg.regularOpCost 15 := by
    simpa only[entered,Nat.reduceAdd] using one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 14)
  have tail:=after_gas cfg (entered s cfg.regularOpCost) p q hn hd
  unfold callAfter
  simpa only[bodyCost,show 15+(18*(count p).toNat+1434)=18*(count p).toNat+1449 by omega] using start.trans tail
private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_charge(seed:NearState)(s:Store NearState)(op:Nat):view seed (chargedStore s op).host=view seed s.host:=rfl

theorem callAfter_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(callAfter cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have h:=congrArg (view s.host) (after_functional_host cfg (entered s cfg.regularOpCost) p q)
  have a:view s.host (after cfg (entered s cfg.regularOpCost) p q).host=view s.host (entered s cfg.regularOpCost).host:=h
  change view s.host (callAfter cfg s p q).host=s.host
  rw[callAfter,a,entered,view_charge,view_charge]
  rfl

theorem callAfter_header_scalars(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:AcceptedDomain p q)(hm:s.mems[p.memoryIndex]?=some p.memory)
    (state:WNear.State)(hw:state.WF)(h:StateReadHeaderBytes.At p.memory p.pointer.toNat state)
    (hheap:(StateDecodeRaw.originalFinish q.toRaw).toNat+8≤(widePointer p).toNat)
    (hroot:(widePointer p).toNat+24≤q.allocator.toNat ∨q.allocator.toNat+4≤(widePointer p).toNat):
    (callAfter cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q) ∧
    readI32 (finalMemory p q) p.out425.toNat=0 ∧
    TotalSupply.U128At (finalMemory p q) (p.out425.toNat+8) state.totalSupply ∧
    readI64 (finalMemory p q) (p.out425.toNat+24)=UInt64.ofNat state.accountStorageUsage:=
  ⟨callAfter_memory cfg s p q hn hd hm,finalMemory_header_scalars p q hn hd state hw h hheap hroot⟩
end WNear.Proofs.StateDecodeBorsh
