import Proofs.VectorDropInsertCredits
import Proofs.DeallocateInsertResources
import Proofs.VectorDropPositiveGas

/-! Exact final heap memory, code/global/host frame and gas for the insertion
vector-drop branch. These effect identities introduce no execution assumptions. -/
namespace WNear.Proofs.VectorDropInsert
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open VectorDrop VectorDropPositive
open AllocateSearch (GasUnits gasUnits_charge gasUnits_paid)
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] readI32 readI64 writeI32 writeI64 DeallocateCore.zeroMemory DeallocateInsert.linkedMemory DeallocateInsert.finalMemory
attribute [local irreducible] bodyAfter callAfter VectorDropInsert237.callAfter
attribute [local irreducible] before237 before311 before777 before747
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem prefix_mems(s:Store NearState)(op:Nat):(before237 s op).mems=s.mems:=by
  have h:=congrArg (fun t:Store NearState=>t.mems) (before237_resources s op)
  exact h
private theorem prefix_fields(s:Store NearState)(op:Nat):
    (before237 s op).funcs=s.funcs ∧(before237 s op).modules=s.modules ∧
    (before237 s op).globals=s.globals ∧(before237 s op).tables=s.tables:=by
  have h:=before237_resources s op
  have a:=congrArg (fun t:Store NearState=>t.funcs) h
  have b:=congrArg (fun t:Store NearState=>t.modules) h
  have c:=congrArg (fun t:Store NearState=>t.globals) h
  have d:=congrArg (fun t:Store NearState=>t.tables) h
  exact ⟨a,b,c,d⟩
private theorem forward_memory(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout)(hm:s.mems[q.memoryIndex]?=some q.memory):
    (VectorDropInsert237.callAfter s op q).mems[q.memoryIndex]?=some (DeallocateInsert.finalMemory q):=by
  unfold VectorDropInsert237.callAfter VectorDropInsert237.after VectorDropInsert237.before582
  have initial:(paid (VectorDropInsert237.entered s op) op 4).mems[q.memoryIndex]?=some q.memory:=by
    rw[paid_mems];exact hm
  exact DeallocateInsert.callAfter_memory _ op q initial
private theorem forward_fields(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    (VectorDropInsert237.callAfter s op q).funcs=s.funcs ∧(VectorDropInsert237.callAfter s op q).modules=s.modules ∧
    (VectorDropInsert237.callAfter s op q).globals=s.globals ∧(VectorDropInsert237.callAfter s op q).tables=s.tables:=by
  unfold VectorDropInsert237.callAfter VectorDropInsert237.after VectorDropInsert237.before582
  have h:=DeallocateInsert.callAfter_fields (paid (VectorDropInsert237.entered s op) op 4) op q
  simpa only[paid_funcs,paid_modules,paid_globals,paid_tables,VectorDropInsert237.entered,chargedStore] using h

theorem bodyAfter_memory(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout)(hm:s.mems[q.memoryIndex]?=some q.memory):
    (bodyAfter s op q).mems[q.memoryIndex]?=some (DeallocateInsert.finalMemory q):=by
  have initial:(before237 s op).mems[q.memoryIndex]?=some q.memory:=by rw[prefix_mems];exact hm
  unfold bodyAfter
  exact forward_memory _ op q initial

theorem callAfter_memory(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout)(hm:s.mems[q.memoryIndex]?=some q.memory):
    (callAfter s op q).mems[q.memoryIndex]?=some (DeallocateInsert.finalMemory q):=by
  unfold callAfter
  exact bodyAfter_memory (entered s op) op q hm

theorem bodyAfter_fields(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    (bodyAfter s op q).funcs=s.funcs ∧(bodyAfter s op q).modules=s.modules ∧
    (bodyAfter s op q).globals=s.globals ∧(bodyAfter s op q).tables=s.tables:=by
  have h:=forward_fields (before237 s op) op q
  have e:=prefix_fields s op
  unfold bodyAfter
  exact ⟨h.1.trans e.1,h.2.1.trans e.2.1,h.2.2.1.trans e.2.2.1,h.2.2.2.trans e.2.2.2⟩

theorem callAfter_fields(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    (callAfter s op q).funcs=s.funcs ∧(callAfter s op q).modules=s.modules ∧
    (callAfter s op q).globals=s.globals ∧(callAfter s op q).tables=s.tables:=by
  unfold callAfter
  exact bodyAfter_fields (entered s op) op q

private theorem entry_units(s:Store NearState)(op n:Nat):GasUnits s (chargedStore (chargedStore s op) (n*op)) op (1+n):=by
  have one:=gasUnits_charge s op 1
  simp only[Nat.one_mul] at one
  exact one.trans (gasUnits_charge _ op n)
private theorem before_units(s:Store NearState)(op:Nat):GasUnits s (before237 s op) op 62:=by
  intro rest hc
  have h:=before237_gas s op rest hc
  exact ⟨h.1,h.2,before237_credits s op rest hc⟩
private theorem forward_units(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    GasUnits s (VectorDropInsert237.callAfter s op q) op 157:=by
  have e:GasUnits s (VectorDropInsert237.entered s op) op 11:=by
    simpa only[VectorDropInsert237.entered,Nat.reduceAdd] using entry_units s op 10
  simpa only[VectorDropInsert237.callAfter,VectorDropInsert237.after,VectorDropInsert237.before582,Nat.reduceAdd] using
    ((e.trans (gasUnits_paid _ op 4)).trans (DeallocateInsert.callAfter_gas _ op q))

theorem bodyAfter_gas(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):GasUnits s (bodyAfter s op q) op 220:=by
  have one:=gasUnits_charge (VectorDropInsert237.callAfter (before237 s op) op q) op 1
  simp only[Nat.one_mul] at one
  simpa only[bodyAfter,Nat.reduceAdd] using ((before_units s op).trans (forward_units _ op q)).trans one

theorem callAfter_gas(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):GasUnits s (callAfter s op q) op 230:=by
  have e:GasUnits s (entered s op) op 10:=by
    simpa only[entered,Nat.reduceAdd] using entry_units s op 9
  simpa only[callAfter,Nat.reduceAdd] using e.trans (bodyAfter_gas _ op q)

private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_charge(seed:NearState)(s:Store NearState)(op:Nat):view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_rebase(seed current host:NearState)(h:view current host=current):view seed host=view seed current:=by
  have r:=congrArg (view seed) h
  exact r
private theorem view_core(seed:NearState)(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    view seed (DeallocateInsert.callAfter s op q).host=view seed s.host:=
  view_rebase seed s.host _ (DeallocateInsert.callAfter_functional_host s op q)

private theorem view_body(seed:NearState)(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    view seed (bodyAfter s op q).host=view seed s.host:=by
  rw[bodyAfter,view_charge,VectorDropInsert237.callAfter,VectorDropInsert237.after,VectorDropInsert237.before582,
    view_core,view_paid,VectorDropInsert237.entered,view_charge,view_charge]
  exact view_rebase seed s.host _ (before237_functional_host s op)

theorem bodyAfter_functional_host(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    {(bodyAfter s op q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  exact view_body s.host s op q

theorem callAfter_functional_host(s:Store NearState)(op:Nat)(q:DeallocateCore.Layout):
    {(callAfter s op q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  change view s.host (callAfter s op q).host=s.host
  rw[callAfter,view_body,entered,view_charge,view_charge]
  rfl
end WNear.Proofs.VectorDropInsert
