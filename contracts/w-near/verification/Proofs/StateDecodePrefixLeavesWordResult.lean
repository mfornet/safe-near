import Proofs.StateDecodePrefixLeavesWordCall

/-! No memory or functional host effect in765; exact packed length and metering. -/
namespace WNear.Proofs.StateDecodePrefixLeaves
open Wasm Wasm.Near MeteredLogic
open StorePairCaller (paid paid_gas)

theorem packedWord_nat (word : UInt32) : (packedWord word).toNat=word.toNat*256 := by
  have hb:=UInt32.toNat_lt word
  unfold packedWord
  simp only[UInt64.toNat_shiftLeft,UInt32.toNat_toUInt64,UInt64.toNat_ofNat,Nat.reducePow,Nat.reduceMod,Nat.shiftLeft_eq]
  apply Nat.mod_eq_of_lt
  omega

theorem packedWord_tag (word : UInt32) : (packedWord word).toNat%256=0 := by
  rw[packedWord_nat]
  omega

theorem packedWord_value (word : UInt32) : (packedWord word).toNat/256=word.toNat := by
  rw[packedWord_nat]
  omega

private theorem paid_resources (seed : NearState) (s : Store NearState) (op n : Nat) :
    {paid s op n with host:=seed}={s with host:=seed}:=by
  induction n with |zero=>rfl|succ n ih=>exact ih
private theorem charged_resources (seed : NearState) (s : Store NearState) (n : Nat) :
    {chargedStore s n with host:=seed}={s with host:=seed}:=rfl

theorem wordCallAfter_resources (cfg : WasmConfig) (s : Store NearState) :
    {wordCallAfter cfg s with host:=s.host}=s := by
  simp only[wordCallAfter,paid_resources,recordEntered,charged_resources]

private theorem memory_of_resources (seed : NearState) (s t : Store NearState) (i : Nat) (m : Memory)
    (hr:{t with host:=seed}=s) (hm:s.mems[i]?=some m) : t.mems[i]?=some m := by
  have h:=congrArg (fun x : Store NearState=>x.mems[i]?) hr
  exact h.trans hm

theorem wordCallAfter_memory (cfg : WasmConfig) (s : Store NearState) (i : Nat) (m : Memory)
    (hm:s.mems[i]?=some m) : (wordCallAfter cfg s).mems[i]?=some m :=
  memory_of_resources s.host s (wordCallAfter cfg s) i m (wordCallAfter_resources cfg s) hm

private theorem fields_of_resources (seed : NearState) (s t : Store NearState) (hr:{t with host:=seed}=s) :
    t.funcs=s.funcs ∧t.modules=s.modules ∧t.tables=s.tables ∧t.globals=s.globals := by
  have a:=congrArg (fun x : Store NearState=>x.funcs) hr
  have b:=congrArg (fun x : Store NearState=>x.modules) hr
  have c:=congrArg (fun x : Store NearState=>x.tables) hr
  have d:=congrArg (fun x : Store NearState=>x.globals) hr
  exact ⟨a,b,c,d⟩

theorem wordCallAfter_fields (cfg : WasmConfig) (s : Store NearState) :
    (wordCallAfter cfg s).funcs=s.funcs ∧(wordCallAfter cfg s).modules=s.modules ∧
    (wordCallAfter cfg s).tables=s.tables ∧(wordCallAfter cfg s).globals=s.globals :=
  fields_of_resources s.host s (wordCallAfter cfg s) (wordCallAfter_resources cfg s)

private def view (seed host:NearState):={host with gas:=seed.gas,gasProfile:=seed.gasProfile}
private theorem view_paid (seed:NearState)(s:Store NearState)(op n:Nat):view seed (paid s op n).host=view seed s.host:=by
  induction n with |zero=>rfl|succ n ih=>exact ih

theorem wordCallAfter_host (cfg : WasmConfig) (s : Store NearState) :
    {(wordCallAfter cfg s).host with gas:=s.host.gas,gasProfile:=s.host.gasProfile}=s.host := by
  change view s.host (wordCallAfter cfg s).host=s.host
  rw[wordCallAfter,view_paid]
  rfl

theorem wordCallAfter_gas (cfg : WasmConfig) (s : Store NearState) (rest : Nat)
    (hc:s.host.gas.Credits (26*cfg.regularOpCost+rest)) :
    (wordCallAfter cfg s).host.gas.burnt=s.host.gas.burnt+26*cfg.regularOpCost ∧
    (wordCallAfter cfg s).host.gas.promises=s.host.gas.promises ∧
    (wordCallAfter cfg s).host.gas.Credits rest := by
  let op:=cfg.regularOpCost
  have first:s.host.gas.Credits (op+(9*op+(16*op+rest))):=hc.mono (by dsimp[op];omega)
  have b0:=GasCounter.burn_credits s.host.gas op (9*op+(16*op+rest)) first
  have c0:(chargedStore s op).host.gas.Credits (9*op+(16*op+rest)):=b0.2.2.2
  have b1:=GasCounter.burn_credits (chargedStore s op).host.gas (9*op) (16*op+rest) c0
  have ca:(recordEntered s op).host.gas.Credits (16*op+rest):=b1.2.2.2
  have e0:(chargedStore s op).host.gas.burnt=s.host.gas.burnt+op:=b0.2.1
  have e1:(recordEntered s op).host.gas.burnt=(chargedStore s op).host.gas.burnt+9*op:=b1.2.1
  have ep:(recordEntered s op).host.gas.promises=s.host.gas.promises:=b1.2.2.1.trans b0.2.2.1
  have hg:=paid_gas (recordEntered s op) op 16 rest ca
  refine ⟨?_,hg.2.trans ep,wordCallAfter_credits cfg s rest hc⟩
  change (paid (recordEntered s op) op 16).host.gas.burnt=s.host.gas.burnt+26*op
  rw[hg.1,e1,e0]
  omega
end WNear.Proofs.StateDecodePrefixLeaves
