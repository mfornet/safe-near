import Proofs.StateDecodePrefixWrapperTailFrame

/-! Exact accepted315 tail endpoint, retaining both cached result fields. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
attribute [local irreducible] copied guarded cached tagged finished after lowMemory highMemory finalMemory

theorem after_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (after s op p).mems[p.index]?=some (finalMemory p):=by
  have initial:(guarded s op).mems[p.index]?=some p.memory:=by rw[guarded,cached,paid_mems,paid_mems];exact hm
  have cp: (copied (guarded s op) op p).mems[p.index]?=some (highMemory p):=copied_memory _ _ _ initial
  have tag:(tagged (copied (guarded s op) op p) op p).mems[p.index]?=some (finalMemory p):=by
    unfold tagged finalMemory
    apply storeI32_memory
    rw[paid_mems];exact cp
  simpa only[after,finished,setGlobal,paid_mems] using tag

theorem after_fields(s:Store NearState)(op:Nat)(p:Layout):
    (after s op p).funcs=s.funcs ∧(after s op p).modules=s.modules ∧(after s op p).tables=s.tables:=by
  have c:=copied_fields (guarded s op) op p
  simp only[after,finished,tagged,setGlobal,storeI32_funcs,storeI32_modules,storeI32_tables,paid_funcs,paid_modules,paid_tables]
  have f:(guarded s op).funcs=s.funcs:=by rw[guarded,cached,paid_funcs,paid_funcs]
  have m:(guarded s op).modules=s.modules:=by rw[guarded,cached,paid_modules,paid_modules]
  have t:(guarded s op).tables=s.tables:=by rw[guarded,cached,paid_tables,paid_tables]
  exact ⟨c.1.trans f,c.2.1.trans m,c.2.2.1.trans t⟩

theorem after_globals(s:Store NearState)(op:Nat)(p:Layout):
    (after s op p).globals=(setGlobal s p.globalIndex (.i32 (p.pointer+16))).globals:=by
  have c:=(copied_fields (guarded s op) op p).2.2.2
  have g:(guarded s op).globals=s.globals:=by rw[guarded,cached,paid_globals,paid_globals]
  have cg:(copied (guarded s op) op p).globals=s.globals:=c.trans g
  have generic:∀t:Store NearState,(finished t op p).globals=(setGlobal t p.globalIndex (.i32 (p.pointer+16))).globals:=by
    intro t
    simp only[finished,tagged,setGlobal,storeI32_globals,paid_globals]
  unfold after
  rw[generic]
  simp only[setGlobal,cg]

private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_charge(seed:NearState)(s:Store NearState)(op:Nat):view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_store32(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_store64(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):view seed (storeI64 s i a m v).host=view seed s.host:=rfl
private theorem view_global(seed:NearState)(s:Store NearState)(i:Nat)(v:Value):view seed (setGlobal s i v).host=view seed s.host:=rfl

theorem after_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(after s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  change view s.host (after s op p).host=s.host
  simp only[after,finished,tagged,copied,zeroed,copiedHigh,copiedLow,highRead,guarded,cached,
    view_global,view_store32,view_store64,view_charge,view_paid]
  rfl
end WNear.Proofs.StateDecodePrefixWrapper.Tail
