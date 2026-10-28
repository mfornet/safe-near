import Proofs.StateDecodePrefixWrapperPhases
import Proofs.StateDecodePrefixWrapperTailResult

/-! Complete accepted315 body memory, code, globals, host and gas endpoints. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid)
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
attribute [local irreducible] after decoded arguments reserved tailLayout finalMemory

private theorem tail_index(p:Layout)(q:StateDecodeVectorCopy.Layout):(tailLayout p q).index=p.memoryIndex:=by unfold tailLayout;rfl
private theorem tail_memory(p:Layout)(q:StateDecodeVectorCopy.Layout):(tailLayout p q).memory=StateDecodePrefix.finalMemory p.toPrefix q:=by unfold tailLayout;rfl
private theorem tail_global(p:Layout)(q:StateDecodeVectorCopy.Layout):(tailLayout p q).globalIndex=p.globalIndex:=by unfold tailLayout;rfl

theorem after_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (after cfg s p q).mems[p.memoryIndex]?=some (finalMemory p q):=by
  have initial:(decoded cfg s p q).mems[(tailLayout p q).index]?=some (tailLayout p q).memory:=by
    rw[tail_index,tail_memory]
    exact decoded_memory cfg s p q hn hd hm
  unfold after finalMemory
  have h:=Tail.after_memory (decoded cfg s p q) cfg.regularOpCost (tailLayout p q) initial
  rw[tail_index] at h
  exact h

theorem after_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (after cfg s p q).funcs=s.funcs ∧(after cfg s p q).modules=s.modules ∧(after cfg s p q).tables=s.tables:=by
  have t:=Tail.after_fields (decoded cfg s p q) cfg.regularOpCost (tailLayout p q)
  have d:=decoded_fields cfg s p q
  unfold after
  exact ⟨t.1.trans d.1,t.2.1.trans d.2.1,t.2.2.trans d.2.2⟩

theorem decoded_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)(hg:s.globals[p.globalIndex]?=some p.wrapperGlobal):
    (decoded cfg s p q).globals=(reserved s cfg.regularOpCost p).globals:=by
  have ag:(arguments s cfg.regularOpCost p).globals[p.globalIndex]?=some p.global:=by
    rw[hn.childGlobal]
    simp only[arguments,reserved,paid_globals,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]
  have hv:p.global.value=.i32 p.sp:=by rw[hn.childGlobal,hn.childSP]
  unfold decoded
  rw[StateDecodePrefix.callAfter_globals cfg (arguments s cfg.regularOpCost p) p.toPrefix q hn.child hd ag hv]
  unfold arguments
  exact paid_globals _ _ _

theorem after_globals(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)(hg:s.globals[p.globalIndex]?=some p.wrapperGlobal)
    (hv:p.wrapperGlobal.value=.i32 p.wrapperSP):
    (after cfg s p q).globals=s.globals:=by
  have d:=decoded_globals cfg s p q hn hd hg
  have t:=Tail.after_globals (decoded cfg s p q) cfg.regularOpCost (tailLayout p q)
  have ptr:(tailLayout p q).pointer+16=p.wrapperSP:=by unfold tailLayout scratch;exact UInt32.sub_add_cancel _ _
  have restore:=StorePairCaller.setGlobal_restore s p.globalIndex (.i32 (scratch p)) p.wrapperGlobal hg
  unfold after
  rw[t]
  simp only[setGlobal,tail_global p q,ptr,d,reserved,paid_globals]
  simpa only[setGlobal,←hv] using restore

theorem decoded_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q):
    GasUnits s (decoded cfg s p q) cfg.regularOpCost (18*(StateDecodePrefix.count p.toPrefix).toNat+927):=by
  have r:GasUnits s (reserved s cfg.regularOpCost p) cfg.regularOpCost 5:=by
    unfold reserved;exact (gasUnits_paid s cfg.regularOpCost 5).host_eq rfl
  have a:GasUnits s (arguments s cfg.regularOpCost p) cfg.regularOpCost 7:=by
    unfold arguments;simpa only[Nat.reduceAdd] using r.trans (gasUnits_paid _ _ 2)
  have c:=StateDecodePrefix.callAfter_gas cfg (arguments s cfg.regularOpCost p) p.toPrefix q hn.child hd
  unfold decoded
  simpa only[show 7+(18*(StateDecodePrefix.count p.toPrefix).toNat+920)=18*(StateDecodePrefix.count p.toPrefix).toNat+927 by omega] using a.trans c

theorem after_gas(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q):
    GasUnits s (after cfg s p q) cfg.regularOpCost (bodyCost p):=by
  unfold after
  simpa only[bodyCost,show (18*(StateDecodePrefix.count p.toPrefix).toNat+927)+33=18*(StateDecodePrefix.count p.toPrefix).toNat+960 by omega] using
    (decoded_gas cfg s p q hn hd).trans (Tail.after_gas (decoded cfg s p q) cfg.regularOpCost (tailLayout p q))
private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_global(seed:NearState)(s:Store NearState)(i:Nat)(v:Value):view seed (setGlobal s i v).host=view seed s.host:=rfl
private theorem view_mask(seed original actual:NearState)
    (h:{actual with gas:=original.gas,gasProfile:=original.gasProfile}=original):view seed actual=view seed original:=by
  have e:=congrArg (view seed) h
  exact e

theorem after_functional_host(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    {(after cfg s p q).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  have tail:=view_mask s.host (decoded cfg s p q).host (Tail.after (decoded cfg s p q) cfg.regularOpCost (tailLayout p q)).host
    (Tail.after_functional_host (decoded cfg s p q) cfg.regularOpCost (tailLayout p q))
  have child:=view_mask s.host (arguments s cfg.regularOpCost p).host (StateDecodePrefix.callAfter cfg (arguments s cfg.regularOpCost p) p.toPrefix q).host
    (StateDecodePrefix.callAfter_functional_host cfg (arguments s cfg.regularOpCost p) p.toPrefix q)
  change view s.host (after cfg s p q).host=s.host
  rw[after,tail,decoded,child,arguments,view_paid,reserved,view_global,view_paid]
  rfl
end WNear.Proofs.StateDecodePrefixWrapper
