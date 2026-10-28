import Proofs.StateDecodePrefixWrapperTailState
import Proofs.AllocateSearchGasCost

/-! Pure memory/code/global and exact gas endpoints for the accepted315 tail. -/
namespace WNear.Proofs.StateDecodePrefixWrapper.Tail
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_fields(s:Store NearState)(op n:Nat):
    (paid s op n).funcs=s.funcs ∧(paid s op n).modules=s.modules ∧(paid s op n).tables=s.tables ∧(paid s op n).globals=s.globals:=by
  induction n with|zero=>exact ⟨rfl,rfl,rfl,rfl⟩|succ n ih=>exact ih
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=(paid_fields s op n).1
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=(paid_fields s op n).2.1
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=(paid_fields s op n).2.2.1
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=(paid_fields s op n).2.2.2
attribute [local irreducible] highRead copiedLow copiedHigh zeroed copied guarded cached tagged finished after

theorem copied_fields(s:Store NearState)(op:Nat)(p:Layout):
    (copied s op p).funcs=s.funcs ∧(copied s op p).modules=s.modules ∧(copied s op p).tables=s.tables ∧(copied s op p).globals=s.globals:=by
  simp only[copied,zeroed,copiedHigh,copiedLow,highRead,chargedStore,storeI32,storeI64,paid_funcs,paid_modules,paid_tables,paid_globals,and_self]

theorem copied_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (copied s op p).mems[p.index]?=some (highMemory p):=by
  have low:(copiedLow s op p).mems[p.index]?=some (lowMemory p):=by
    unfold copiedLow lowMemory
    apply storeI64_memory
    rw[paid_mems,highRead,paid_mems];exact hm
  have high:(copiedHigh s op p).mems[p.index]?=some (highMemory p):=by
    unfold copiedHigh highMemory
    apply storeI32_memory
    rw[paid_mems];exact low
  simpa only[copied,zeroed,chargedStore,paid_mems] using high

theorem copied_gas(s:Store NearState)(op:Nat)(p:Layout):GasUnits s (copied s op p) op 16:=by
  have first:GasUnits s (highRead s op) op 5:=by unfold highRead;exact gasUnits_paid s op 5
  have low:GasUnits (highRead s op) (copiedLow s op p) op 3:=by
    unfold copiedLow
    exact (gasUnits_paid (highRead s op) op 3).host_eq rfl
  have high:GasUnits (copiedLow s op p) (copiedHigh s op p) op 5:=by
    unfold copiedHigh
    exact (gasUnits_paid (copiedLow s op p) op 5).host_eq rfl
  have zero:GasUnits (copiedHigh s op p) (zeroed s op p) op 2:=by unfold zeroed;exact gasUnits_paid _ _ _
  have branch:GasUnits (zeroed s op p) (copied s op p) op 1:=by
    unfold copied
    simpa only[Nat.one_mul] using gasUnits_charge (zeroed s op p) op 1
  simpa only[Nat.reduceAdd] using (((first.trans low).trans high).trans zero).trans branch

theorem after_gas(s:Store NearState)(op:Nat)(p:Layout):GasUnits s (after s op p) op 33:=by
  have cache:GasUnits s (cached s op) op 5:=by unfold cached;exact gasUnits_paid _ _ _
  have guard:GasUnits (cached s op) (guarded s op) op 5:=by unfold guarded;exact gasUnits_paid _ _ _
  have tag:∀t:Store NearState,GasUnits t (tagged t op p) op 3:=by
    intro t;unfold tagged;exact (gasUnits_paid t op 3).host_eq rfl
  have finish:∀t:Store NearState,GasUnits (tagged t op p) (finished t op p) op 4:=by
    intro t;unfold finished;exact (gasUnits_paid (tagged t op p) op 4).host_eq rfl
  unfold after
  simpa only[Nat.reduceAdd] using (((cache.trans guard).trans (copied_gas (guarded s op) op p)).trans (tag _)).trans (finish _)

theorem guarded_credits(s:Store NearState)(op rest:Nat)(hc:s.host.gas.Credits (33*op+rest)):
    (guarded s op).host.gas.Credits (23*op+rest):=by
  unfold guarded cached
  exact StorePairCaller.paid_credits (paid s op 5) op 5 _
    (StorePairCaller.paid_credits s op 5 _ (hc.mono (by omega)))

theorem zeroed_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (15*op+rest)):
    (zeroed s op p).host.gas.Credits rest:=by
  have high: (highRead s op).host.gas.Credits (10*op+rest):=by
    unfold highRead;exact StorePairCaller.paid_credits s op 5 _ (hc.mono (by omega))
  have low: (copiedLow s op p).host.gas.Credits (7*op+rest):=by
    unfold copiedLow;rw[storeI64_host]
    exact StorePairCaller.paid_credits (highRead s op) op 3 _ (high.mono (by omega))
  have written: (copiedHigh s op p).host.gas.Credits (2*op+rest):=by
    unfold copiedHigh;rw[storeI32_host]
    exact StorePairCaller.paid_credits (copiedLow s op p) op 5 _ (low.mono (by omega))
  unfold zeroed
  exact StorePairCaller.paid_credits (copiedHigh s op p) op 2 rest written

theorem copied_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (16*op+rest)):
    (copied s op p).host.gas.Credits rest:=(copied_gas s op p rest hc).2.2

theorem after_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (33*op+rest)):
    (after s op p).host.gas.Credits rest:=(after_gas s op p rest hc).2.2
end WNear.Proofs.StateDecodePrefixWrapper.Tail
