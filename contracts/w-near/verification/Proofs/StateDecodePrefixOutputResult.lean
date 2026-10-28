import Proofs.StateDecodePrefixOutput
import Proofs.AllocateSearchGasCost

/-! Exact20-unit and resource effects of the actual316 output sequence. -/
namespace WNear.Proofs.StateDecodePrefix.Output
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid)
open AllocateSearch (GasUnits gasUnits_paid gasUnits_charge)
attribute [local irreducible] cached high low tagged described after

private def fields(s:Store NearState):=(s.funcs,s.modules,s.tables,s.globals)
private theorem fields_paid(s:Store NearState)(op n:Nat):fields (paid s op n)=fields s:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem fields_charge(s:Store NearState)(op:Nat):fields (chargedStore s op)=fields s:=rfl
private theorem fields_store32(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):fields (storeI32 s i a m v)=fields s:=rfl
private theorem fields_store64(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):fields (storeI64 s i a m v)=fields s:=rfl

theorem after_fields(s:Store NearState)(op:Nat)(p:Layout):
    (after s op p).funcs=s.funcs ∧(after s op p).modules=s.modules ∧(after s op p).tables=s.tables ∧(after s op p).globals=s.globals:=by
  have h:fields (after s op p)=fields s:=by
    simp only[after,fields_charge,described,StateDecodeScalar.store64Local,fields_store64,fields_paid,tagged,outputTagStore,fields_store32,
      low,outputLowStore,high,outputHighStore,cached]
  exact ⟨congrArg Prod.fst h,congrArg (fun q=>q.2.1) h,congrArg (fun q=>q.2.2.1) h,congrArg (fun q=>q.2.2.2) h⟩

theorem after_memory(s:Store NearState)(op:Nat)(p:Layout)(hm:s.mems[p.index]?=some p.memory):
    (after s op p).mems[p.index]?=some (finalMemory p):=by
  unfold after
  exact described_memory s op p hm

theorem after_credits(s:Store NearState)(op rest:Nat)(p:Layout)(hc:s.host.gas.Credits (20*op+rest)):
    (after s op p).host.gas.Credits rest:=by
  unfold after
  exact StorePair.charged_credits (described s op p) op rest (described_credits s op rest p hc)

private def view(seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid(seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with|zero=>rfl|succ n ih=>exact ih
private theorem view_charge(seed:NearState)(s:Store NearState)(op:Nat):view seed (chargedStore s op).host=view seed s.host:=rfl
private theorem view_store32(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt32):view seed (storeI32 s i a m v).host=view seed s.host:=rfl
private theorem view_store64(seed:NearState)(s:Store NearState)(i a:Nat)(m:Memory)(v:UInt64):view seed (storeI64 s i a m v).host=view seed s.host:=rfl

theorem after_functional_host(s:Store NearState)(op:Nat)(p:Layout):
    {(after s op p).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host:=by
  change view s.host (after s op p).host=s.host
  simp only[after,view_charge,described,StateDecodeScalar.store64Local,view_store64,view_paid,tagged,outputTagStore,view_store32,
    low,outputLowStore,high,outputHighStore,cached]
  rfl

theorem after_gas(s:Store NearState)(op:Nat)(p:Layout):GasUnits s (after s op p) op 20:=by
  have c:GasUnits s (cached s op) op 3:=by simpa only[cached] using gasUnits_paid s op 3
  have h:GasUnits (cached s op) (high s op p) op 6:=by
    have eq:(high s op p).host=(paid (cached s op) op 6).host:=by simp only[high,outputHighStore,storeI32_host]
    exact (gasUnits_paid (cached s op) op 6).host_eq eq
  have l:GasUnits (high s op p) (low s op p) op 4:=by
    have eq:(low s op p).host=(paid (high s op p) op 4).host:=by simp only[low,outputLowStore,storeI64_host]
    exact (gasUnits_paid (high s op p) op 4).host_eq eq
  have t:GasUnits (low s op p) (tagged s op p) op 3:=by
    have eq:(tagged s op p).host=(paid (low s op p) op 3).host:=by simp only[tagged,outputTagStore,storeI32_host]
    exact (gasUnits_paid (low s op p) op 3).host_eq eq
  have d:GasUnits (tagged s op p) (described s op p) op 3:=by
    have eq:(described s op p).host=(paid (tagged s op p) op 3).host:=by simp only[described,StateDecodeScalar.store64Local,storeI64_host]
    exact (gasUnits_paid (tagged s op p) op 3).host_eq eq
  have b:GasUnits (described s op p) (after s op p) op 1:=by simpa only[after,Nat.one_mul] using gasUnits_charge (described s op p) op 1
  exact ((((c.trans h).trans l).trans t).trans d).trans b
end WNear.Proofs.StateDecodePrefix.Output
