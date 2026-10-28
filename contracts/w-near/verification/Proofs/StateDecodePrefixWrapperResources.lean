import Proofs.StateDecodePrefixWrapperPrefix
import Proofs.StateDecodePrefixResult

/-! Concrete315 resources after its real316 call, derived from original arrays.
The memory snapshot is the full sequential316 result. -/
namespace WNear.Proofs.StateDecodePrefixWrapper
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_credits)
set_option maxRecDepth 16384
attribute [local irreducible] StateDecodePrefix.after StateDecodePrefix.finalMemory
private theorem paid_funcs(s:Store NearState)(op n:Nat):(paid s op n).funcs=s.funcs:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_modules(s:Store NearState)(op n:Nat):(paid s op n).modules=s.modules:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_tables(s:Store NearState)(op n:Nat):(paid s op n).tables=s.tables:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_mems(s:Store NearState)(op n:Nat):(paid s op n).mems=s.mems:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem paid_globals(s:Store NearState)(op n:Nat):(paid s op n).globals=s.globals:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem charged_mems(s:Store NearState)(n:Nat):(chargedStore s n).mems=s.mems:=rfl
private theorem charged_globals(s:Store NearState)(n:Nat):(chargedStore s n).globals=s.globals:=rfl
private theorem global_host(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).host=s.host:=rfl
private theorem global_mems(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).mems=s.mems:=rfl
private theorem global_funcs(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).funcs=s.funcs:=rfl
private theorem global_modules(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).modules=s.modules:=rfl
private theorem global_tables(s:Store NearState)(i:Nat)(v:Value):(setGlobal s i v).tables=s.tables:=rfl

theorem decoded_memory(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)(hm:s.mems[p.memoryIndex]?=some p.memory):
    (decoded cfg s p q).mems[p.memoryIndex]?=some (StateDecodePrefix.finalMemory p.toPrefix q):=by
  unfold decoded
  apply StateDecodePrefix.callAfter_memory cfg (arguments s cfg.regularOpCost p) p.toPrefix q hn.child hd
  simpa only[arguments,reserved,paid_mems,global_mems] using hm

theorem decoded_fields(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout):
    (decoded cfg s p q).funcs=s.funcs ∧(decoded cfg s p q).modules=s.modules ∧(decoded cfg s p q).tables=s.tables:=by
  have h:=StateDecodePrefix.callAfter_fields cfg (arguments s cfg.regularOpCost p) p.toPrefix q
  have fs:(arguments s cfg.regularOpCost p).funcs=s.funcs:=by simp only[arguments,reserved,paid_funcs,global_funcs]
  have ms:(arguments s cfg.regularOpCost p).modules=s.modules:=by simp only[arguments,reserved,paid_modules,global_modules]
  have ts:(arguments s cfg.regularOpCost p).tables=s.tables:=by simp only[arguments,reserved,paid_tables,global_tables]
  unfold decoded
  exact ⟨h.1.trans fs,h.2.1.trans ms,h.2.2.trans ts⟩

theorem decoded_global(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)(hg:s.globals[p.globalIndex]?=some p.wrapperGlobal):
    (decoded cfg s p q).globals[p.globalIndex]?=some p.global:=by
  let active:=arguments s cfg.regularOpCost p
  have ag:active.globals[p.globalIndex]?=some p.global:=by
    rw[hn.childGlobal]
    simp only[active,arguments,reserved,paid_globals,setGlobal,Array.getElem?_modify,hg,Option.map_some,ite_true]
  have hv:p.global.value=.i32 p.sp:=by rw[hn.childGlobal,hn.childSP]
  unfold decoded
  rw[StateDecodePrefix.callAfter_globals cfg active p.toPrefix q hn.child hd ag hv]
  exact ag

theorem decoded_credits(cfg:WasmConfig)(s:Store NearState)(p:Layout)(q:StateDecodeVectorCopy.Layout)
    (rest:Nat)(hn:Native p)(hd:StateDecodePrefix.AcceptedDomain p.toPrefix q)
    (hc:s.host.gas.Credits ((18*(StateDecodePrefix.count p.toPrefix).toNat+927)*cfg.regularOpCost+rest)):
    (decoded cfg s p q).host.gas.Credits rest:=by
  let op:=cfg.regularOpCost
  have cr:(reserved s op p).host.gas.Credits (2*op+((18*(StateDecodePrefix.count p.toPrefix).toNat+920)*op+rest)):=by
    simpa only[reserved,global_host] using paid_credits s op 5 (2*op+((18*(StateDecodePrefix.count p.toPrefix).toNat+920)*op+rest)) (hc.mono (by dsimp[op];simp only[Nat.add_mul];omega))
  have ca:=paid_credits (reserved s op p) op 2 _ cr
  exact StateDecodePrefix.callAfter_credits cfg (arguments s op p) p.toPrefix q rest hn.child hd ca
end WNear.Proofs.StateDecodePrefixWrapper
