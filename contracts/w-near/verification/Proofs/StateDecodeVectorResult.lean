import Proofs.StateDecodeVectorCall
import Proofs.StateDecodeRawGas
import Proofs.StateDecodeRawHost

/-! Complete typed373 endpoints, exact gas, and functional host preservation. -/
namespace WNear.Proofs.StateDecodeVector
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
set_option maxRecDepth 16384
private theorem paid_funcs (s : Store NearState) (op n : Nat) : (paid s op n).funcs=s.funcs := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_modules (s : Store NearState) (op n : Nat) : (paid s op n).modules=s.modules := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem paid_tables (s : Store NearState) (op n : Nat) : (paid s op n).tables=s.tables := by
  induction n with |zero=>rfl|succ n ih=>exact ih
attribute [local irreducible] reserved arguments allocated after callAfter entered StateDecodeRaw.callAfterRaw

theorem after_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (after cfg s p).funcs=s.funcs ∧(after cfg s p).modules=s.modules ∧(after cfg s p).tables=s.tables := by
  have r:=StateDecodeRaw.callAfterRaw_fields cfg (arguments s cfg.regularOpCost p) p.toRaw
  have a : (allocated cfg s p).funcs=s.funcs ∧(allocated cfg s p).modules=s.modules ∧(allocated cfg s p).tables=s.tables := by
    have f : (arguments s cfg.regularOpCost p).funcs=s.funcs ∧(arguments s cfg.regularOpCost p).modules=s.modules ∧(arguments s cfg.regularOpCost p).tables=s.tables := by
      simp only [arguments,reserved,setGlobal,paid_funcs,paid_modules,paid_tables,and_self]
    unfold allocated
    exact ⟨r.1.trans f.1,r.2.1.trans f.2.1,r.2.2.trans f.2.2⟩
  have t:=tailAfter_fields (allocated cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memoryAllocated p) p.outVector (scratch p)
  rw [after_eq]
  exact ⟨t.1.trans a.1,t.2.1.trans a.2.1,t.2.2.trans a.2.2⟩

theorem callAfter_memory (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hm : s.mems[p.memoryIndex]?=some p.memory) :
    (callAfter cfg s p).mems[p.memoryIndex]?=some (finalMemory p) := by
  have initial : (entered s cfg.regularOpCost).mems[p.memoryIndex]?=some p.memory := by unfold entered;exact hm
  unfold callAfter
  exact after_memory cfg (entered s cfg.regularOpCost) p hn initial

theorem callAfter_fields (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    (callAfter cfg s p).funcs=s.funcs ∧(callAfter cfg s p).modules=s.modules ∧(callAfter cfg s p).tables=s.tables := by
  unfold callAfter
  simpa only [entered,chargedStore] using after_fields cfg (entered s cfg.regularOpCost) p

theorem callAfter_globals (cfg : WasmConfig) (s : Store NearState) (p : Layout) (hn : Native p)
    (hg : s.globals[p.globalIndex]?=some p.globalVector) (hv : p.globalVector.value=.i32 p.spVector) :
    (callAfter cfg s p).globals=s.globals := by
  have initial : (entered s cfg.regularOpCost).globals[p.globalIndex]?=some p.globalVector := by unfold entered;exact hg
  unfold callAfter
  simpa only [entered,chargedStore] using after_globals cfg (entered s cfg.regularOpCost) p hn initial hv
private theorem argument_units (s : Store NearState) (op : Nat) (p : Layout) : GasUnits s (arguments s op p) op 10 := by
  have reserve : GasUnits s (reserved s op p) op 5 := by
    unfold reserved
    exact (gasUnits_paid s op 5).host_eq rfl
  simpa only [arguments,Nat.reduceAdd] using reserve.trans (gasUnits_paid (reserved s op p) op 5)
private theorem tail_units (s : Store NearState) (op i g : Nat) (m : Memory) (out scratch : UInt32) :
    GasUnits s (tailAfter s op i g m out scratch) op 13 := (gasUnits_paid s op 13).host_eq rfl

theorem after_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) : GasUnits s (after cfg s p) cfg.regularOpCost 608 := by
  have allocation : GasUnits s (allocated cfg s p) cfg.regularOpCost 595 := by
    simpa only [allocated,Nat.reduceAdd] using (argument_units s cfg.regularOpCost p).trans
      (StateDecodeRaw.callAfterRaw_gas cfg (arguments s cfg.regularOpCost p) p.toRaw)
  rw [after_eq]
  simpa only [Nat.reduceAdd] using allocation.trans
    (tail_units (allocated cfg s p) cfg.regularOpCost p.memoryIndex p.globalIndex (memoryAllocated p) p.outVector (scratch p))

theorem callAfter_gas (cfg : WasmConfig) (s : Store NearState) (p : Layout) : GasUnits s (callAfter cfg s p) cfg.regularOpCost 620 := by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only [Nat.one_mul] at one
  have start : GasUnits s (entered s cfg.regularOpCost) cfg.regularOpCost 12 :=
    by simpa only [entered,Nat.reduceAdd] using one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 11)
  simpa only [callAfter,Nat.reduceAdd] using start.trans (after_gas cfg (entered s cfg.regularOpCost) p)

private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem view_global (seed : NearState) (s : Store NearState) (i : Nat) (v : Value) : view seed (setGlobal s i v).host=view seed s.host:=rfl
private theorem view_charge (seed : NearState) (s : Store NearState) (op : Nat) : view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_store32 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_store64 (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt64) : view seed (storeI64 s i a m v).host=view seed s.host:=rfl
private theorem view_raw (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : StateDecodeRaw.Layout) :
    view seed (StateDecodeRaw.callAfterRaw cfg s p).host=view seed s.host := by
  have h:=congrArg (view seed) (StateDecodeRaw.callAfterRaw_functional_host cfg s p)
  exact h
private theorem view_tail (seed : NearState) (s : Store NearState) (op i g : Nat) (m : Memory) (out scratch : UInt32) :
    view seed (tailAfter s op i g m out scratch).host=view seed s.host := by
  simp only [tailAfter,outputStore,zeroStore,StateDecodeScalar.store64Local,view_store32,view_store64,view_paid,view_global]
private theorem view_after (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    view seed (after cfg s p).host=view seed s.host := by
  rw [after_eq,view_tail,allocated,view_raw,arguments,view_paid,reserved,view_global,view_paid]

theorem after_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(after cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (after cfg s p).host=s.host
  rw [view_after];rfl

theorem callAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (p : Layout) :
    {(callAfter cfg s p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (callAfter cfg s p).host=s.host
  rw [callAfter,view_after,entered,view_charge,view_charge];rfl
end WNear.Proofs.StateDecodeVector
