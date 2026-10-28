import Proofs.StateDecodeRawRecordCall

/-! Exact actual770 record-call resources and accounting. All assertions follow
from the computed callee states, without assumed execution or future lookups. -/
namespace WNear.Proofs.StateDecodeRaw
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_charge)
set_option maxRecDepth 16384
private def fields (s : Store NearState) := (s.funcs,s.modules,s.tables)
private theorem fields_paid (s : Store NearState) (op n : Nat) : fields (paid s op n)=fields s := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem fields_charge (s : Store NearState) (op : Nat) : fields (chargedStore s op)=fields s:=rfl
private theorem fields_store (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : fields (storeI32 s i a m v)=fields s:=rfl
private theorem globals_paid (s : Store NearState) (op n : Nat) : (paid s op n).globals=s.globals := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem mems_paid (s : Store NearState) (op n : Nat) : (paid s op n).mems=s.mems := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem record_fields (s : Store NearState) (op i : Nat) (m : Memory) (out size pointer : UInt32) :
    fields (recordStore s op i m out size pointer)=fields s := by
  simp only [recordStore,AllocateRecord.recordStore,fields_store,fields_paid]
private theorem record_globals (s : Store NearState) (op i : Nat) (m : Memory) (out size pointer : UInt32) :
    (recordStore s op i m out size pointer).globals=s.globals := by
  simp only [recordStore,AllocateRecord.recordStore,storeI32_globals,globals_paid]
private theorem fields_from (s t : Store NearState)
    (h : t.funcs=s.funcs ∧ t.modules=s.modules ∧ t.tables=s.tables) : fields t=fields s :=
  Prod.ext h.1 (Prod.ext h.2.1 h.2.2)
private theorem fields_raw (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) :
    fields (AllocateRawForwardDirect.callAfter310 cfg s q)=fields s := by
  have h:=AllocateRawForwardDirect.callAfter310_fields cfg s q
  exact fields_from s _ h
private def view (seed host : NearState) := {host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_reset (seed old host : NearState) : view seed (view old host)=view seed host:=rfl
private theorem view_rebase (seed base host : NearState) (h : view base host=base) : view seed host=view seed base := by
  have eq:=congrArg (view seed) h
  simpa only [view_reset] using eq
private theorem view_paid (seed : NearState) (s : Store NearState) (op n : Nat) : view seed (paid s op n).host=view seed s.host := by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem view_charge (seed : NearState) (s : Store NearState) (op : Nat) : view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_store (seed : NearState) (s : Store NearState) (i a : Nat) (m : Memory) (v : UInt32) : view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_record (seed : NearState) (s : Store NearState) (op i : Nat) (m : Memory) (out size pointer : UInt32) :
    view seed (recordStore s op i m out size pointer).host=view seed s.host := by
  simp only [recordStore,AllocateRecord.recordStore,view_store,view_paid]
private theorem view_raw (seed : NearState) (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) :
    view seed (AllocateRawForwardDirect.callAfter310 cfg s q).host=view seed s.host :=
  view_rebase seed s.host _ (AllocateRawForwardDirect.callAfter310_functional_host cfg s q)

attribute [local irreducible] recordInput allocatedRecord AllocateRawForwardDirect.callAfter310
  AllocatePositive.finalMemory recordStore recordAfter

theorem recordCallAfter_memory (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32)
    (hm : s.mems[q.memoryIndex]?=some q.memory) :
    (recordCallAfter cfg s q out).mems[q.memoryIndex]?=some
      (writeI32 (writeI32 (AllocatePositive.finalMemory q) (out.toNat+4) q.size) out.toNat (AllocatePositive.result q)) := by
  unfold recordCallAfter recordAfter
  apply recordStore_memory
  rw [recordInput,mems_paid,allocatedRecord]
  apply AllocateRawForwardDirect.callAfter310_memory
  simpa only [mems_paid,recordEntered,chargedStore] using hm

theorem recordCallAfter_fields (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32) :
    (recordCallAfter cfg s q out).funcs=s.funcs ∧ (recordCallAfter cfg s q out).modules=s.modules ∧
    (recordCallAfter cfg s q out).tables=s.tables := by
  have eq : fields (recordCallAfter cfg s q out)=fields s := by
    simp only [recordCallAfter,recordAfter,record_fields,recordInput,fields_paid,allocatedRecord,fields_raw,recordEntered,fields_charge]
  exact ⟨congrArg (fun x=>x.1) eq,congrArg (fun x=>x.2.1) eq,congrArg (fun x=>x.2.2) eq⟩

theorem recordCallAfter_globals (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32)
    (hg : s.globals[q.globalIndex]?=some q.global) (hv : q.global.value=.i32 q.sp) :
    (recordCallAfter cfg s q out).globals=s.globals := by
  let before:=paid (paid (recordEntered s cfg.regularOpCost) cfg.regularOpCost 6) cfg.regularOpCost 2
  have g : before.globals[q.globalIndex]?=some q.global := by
    simpa only [before,globals_paid,recordEntered,chargedStore] using hg
  have eq:=AllocateRawForwardDirect.callAfter310_globals cfg before q g hv
  unfold recordCallAfter recordAfter
  rw [record_globals,recordInput,globals_paid,allocatedRecord,eq,globals_paid,globals_paid]
  rfl

theorem recordCallAfter_functional_host (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32) :
    {(recordCallAfter cfg s q out).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (recordCallAfter cfg s q out).host=s.host
  simp only [recordCallAfter,recordAfter,view_record,recordInput,view_paid,allocatedRecord,view_raw,recordEntered,view_charge]
  rfl

theorem recordCallAfter_gas (cfg : WasmConfig) (s : Store NearState) (q : AllocatePositive.Layout) (out : UInt32) :
    GasUnits s (recordCallAfter cfg s q out) cfg.regularOpCost 413 := by
  have one:=gasUnits_charge s cfg.regularOpCost 1
  simp only [Nat.one_mul] at one
  have enter : GasUnits s (recordEntered s cfg.regularOpCost) cfg.regularOpCost 11 :=
    one.trans (gasUnits_charge (chargedStore s cfg.regularOpCost) cfg.regularOpCost 10)
  exact enter.trans (recordAfter_gas cfg (recordEntered s cfg.regularOpCost) q out)
end WNear.Proofs.StateDecodeRaw
