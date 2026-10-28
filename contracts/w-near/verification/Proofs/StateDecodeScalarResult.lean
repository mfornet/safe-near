import Proofs.StateDecodeScalarCall
import Proofs.StateDecodeScalarSemantic
import Proofs.StateDecodeScalarSliceOutput

/-! Complete typed scalar-call endpoints and original-input semantic readback. -/
namespace WNear.Proofs.StateDecodeScalar
open Wasm Wasm.Near MeteredLogic
open AllocateSearch (GasUnits gasUnits_charge)
set_option maxRecDepth 16384
attribute [local irreducible] callAfter entered after

theorem callAfter_memory (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter wide cfg s p).mems[p.memoryIndex]?=some (finalMemory wide p) := by
  have am : (entered wide s cfg.regularOpCost).mems[p.memoryIndex]?=some p.memory := by unfold entered;exact hm
  unfold callAfter
  exact after_memory wide cfg _ p am

theorem callAfter_fields (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter wide cfg s p).funcs=s.funcs ∧ (callAfter wide cfg s p).modules=s.modules ∧
    (callAfter wide cfg s p).tables=s.tables := by
  unfold callAfter
  simpa only [entered,chargedStore] using after_fields wide cfg (entered wide s cfg.regularOpCost) p

theorem callAfter_globals (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout)
    (hg : s.globals[p.globalIndex]?=some p.global) (hv : p.global.value=.i32 p.sp) :
    (callAfter wide cfg s p).globals=s.globals := by
  have ag : (entered wide s cfg.regularOpCost).globals[p.globalIndex]?=some p.global := by unfold entered;exact hg
  unfold callAfter
  simpa only [entered,chargedStore] using after_globals wide cfg (entered wide s cfg.regularOpCost) p ag hv

theorem callAfter_functional_host (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter wide cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  have h:=congrArg (fun h : NearState=>{h with gas:=s.host.gas,gasProfile:=s.host.gasProfile})
    (after_functional_host wide cfg (entered wide s cfg.regularOpCost) p)
  simpa only [callAfter,entered,chargedStore,chargeHost] using h

theorem callAfter_gas (wide : Bool) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    GasUnits s (callAfter wide cfg s p) cfg.regularOpCost (if wide then 168 else 151) := by
  have first:=gasUnits_charge s cfg.regularOpCost 1
  simp only [Nat.one_mul] at first
  have entry:=first.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost (activationUnits wide))
  have start : GasUnits s (entered wide s cfg.regularOpCost) cfg.regularOpCost (1+activationUnits wide) := by
    simpa only [entered] using entry
  have body:=after_gas wide cfg (entered wide s cfg.regularOpCost) p
  have cost : GasUnits s (callAfter wide cfg s p) cfg.regularOpCost (1+activationUnits wide+(if wide then 154 else 138)) := by
    unfold callAfter
    exact start.trans body
  cases wide <;> simpa only [activationUnits,Bool.false_eq_true,ite_false,ite_true,Nat.reduceAdd] using cost

theorem call_ledger (wide : Bool) :
    bodyCost wide+activationUnits wide+1=(if wide then 168 else 151) ∧
    bodySteps wide+1=(if wide then 134 else 118) := by
  cases wide <;> exact ⟨rfl,rfl⟩

theorem callAfter_u128 (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native true p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) (value : Nat)
    (hs : p.slice.toNat+8≤p.out.toNat+8 ∨ p.out.toNat+24≤p.slice.toNat)
    (hv : TotalSupply.U128At p.memory p.pointer.toNat value) :
    (callAfter true cfg s p).mems[p.memoryIndex]?=some (finalMemory true p) ∧
    readI32 (finalMemory true p) p.out.toNat=0 ∧
    TotalSupply.U128At (finalMemory true p) (p.out.toNat+8) value :=
  ⟨callAfter_memory true cfg s p hm,finalMemory_tag true p hn,finalMemory_u128 p hn value hs hv⟩
end WNear.Proofs.StateDecodeScalar
