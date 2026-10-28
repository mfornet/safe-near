import Proofs.DeallocateInsertPhases
import Proofs.DeallocateCoreFrame

/-! Exact insertion-branch memory and original code-array/host frames. -/
namespace WNear.Proofs.DeallocateInsert
open Wasm Wasm.Near MeteredLogic DeallocateCore
open StorePairCaller (paid)
set_option maxRecDepth 16384
attribute [local irreducible] readI32 readI64 writeI32 writeI64 linkedMemory finalMemory
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
private theorem store_funcs(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).funcs=s.funcs:=rfl
private theorem store_modules(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).modules=s.modules:=rfl
private theorem store_globals(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).globals=s.globals:=rfl
private theorem store_tables(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):(storeI32 s i a m v).tables=s.tables:=rfl

theorem neighborAfter_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some (zeroMemory p)):
    (neighborAfter s op p).mems[p.memoryIndex]?=some (finalMemory p):=by
  unfold neighborAfter finalMemory
  apply storeI32_memory
  rw[paid_mems]
  unfold linked linkedMemory
  apply storeI32_memory
  rw[paid_mems,selected,paid_mems];exact hm

theorem after_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (after s op p).mems[p.memoryIndex]?=some (finalMemory p):=by
  unfold after
  exact neighborAfter_memory _ op p (zeroed_memory s op p hm)

theorem callAfter_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (callAfter s op p).mems[p.memoryIndex]?=some (finalMemory p):=by
  unfold callAfter
  exact after_memory _ op p hm

private theorem zeroed_fields(s:Store NearState)(op:Nat)(p:Layout):
    (zeroed s op p).funcs=s.funcs ∧(zeroed s op p).modules=s.modules ∧
    (zeroed s op p).globals=s.globals ∧(zeroed s op p).tables=s.tables:=by
  simp only[DeallocateCore.zeroed,DeallocateCore.sized,Deallocate.sized,DeallocateListSize.after,
    DeallocateListSize.entered,DeallocateCore.marked,DeallocateCore.saved,DeallocateCore.aligned,
    Deallocate.aligned,DeallocateAlign.after570,DeallocateAlign.bodyAfter570,DeallocateAlign.entered570,
    DeallocateAlign.after568,DeallocateAlign.entered568,DeallocateCore.guarded,
    store_funcs,store_modules,store_globals,store_tables,paid_funcs,paid_modules,paid_globals,paid_tables,chargedStore,true_and]

theorem neighborAfter_fields(s:Store NearState)(op:Nat)(p:Layout):
    (neighborAfter s op p).funcs=s.funcs ∧(neighborAfter s op p).modules=s.modules ∧
    (neighborAfter s op p).globals=s.globals ∧(neighborAfter s op p).tables=s.tables:=by
  simp only[neighborAfter,linked,selected,store_funcs,store_modules,store_globals,store_tables,
    paid_funcs,paid_modules,paid_globals,paid_tables,true_and]

theorem after_fields(s:Store NearState)(op:Nat)(p:Layout):
    (after s op p).funcs=s.funcs ∧(after s op p).modules=s.modules ∧
    (after s op p).globals=s.globals ∧(after s op p).tables=s.tables:=by
  have h:=neighborAfter_fields (zeroed s op p) op p
  have z:=zeroed_fields s op p
  exact ⟨h.1.trans z.1,h.2.1.trans z.2.1,h.2.2.1.trans z.2.2.1,h.2.2.2.trans z.2.2.2⟩

theorem callAfter_fields(s:Store NearState)(op:Nat)(p:Layout):
    (callAfter s op p).funcs=s.funcs ∧(callAfter s op p).modules=s.modules ∧
    (callAfter s op p).globals=s.globals ∧(callAfter s op p).tables=s.tables:=by
  exact after_fields (entered s op) op p

theorem neighborAfter_code(s:Store NearState)(op inst:Nat)(p:Layout)(hc:DeallocateCore.Code s inst p):
    DeallocateCore.Code (neighborAfter s op p) inst p:=by
  have h:=neighborAfter_fields s op p
  exact hc.transport s (neighborAfter s op p) inst p h.1 h.2.1

theorem after_code(s:Store NearState)(op inst:Nat)(p:Layout)(hc:DeallocateCore.Code s inst p):
    DeallocateCore.Code (after s op p) inst p:=by
  have h:=after_fields s op p
  exact hc.transport s (after s op p) inst p h.1 h.2.1

theorem callAfter_code(s:Store NearState)(op inst:Nat)(p:Layout)(hc:DeallocateCore.Code s inst p):
    DeallocateCore.Code (callAfter s op p) inst p:=by
  have h:=callAfter_fields s op p
  exact hc.transport s (callAfter s op p) inst p h.1 h.2.1

private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_charge(seed:NearState)(s:Store NearState)(op:Nat):view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_store(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_zeroed(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (zeroed s op p).host=view seed s.host:=by
  simp only[DeallocateCore.zeroed,DeallocateCore.sized,Deallocate.sized,DeallocateListSize.after,
    DeallocateListSize.entered,DeallocateCore.marked,DeallocateCore.saved,DeallocateCore.aligned,
    Deallocate.aligned,DeallocateAlign.after570,DeallocateAlign.bodyAfter570,DeallocateAlign.entered570,
    DeallocateAlign.after568,DeallocateAlign.entered568,DeallocateCore.guarded,view_store,view_paid,view_charge]
private theorem view_after(seed:NearState)(s:Store NearState)(op:Nat)(p:Layout):view seed (after s op p).host=view seed s.host:=by
  rw[after,neighborAfter,view_store,view_paid,linked,view_store,view_paid,selected,view_paid,view_zeroed]

theorem after_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(after s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  exact view_after s.host s op p

theorem callAfter_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(callAfter s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  change view s.host (callAfter s op p).host=s.host
  rw[callAfter,view_after,entered,view_charge,view_charge]
  rfl
end WNear.Proofs.DeallocateInsert
