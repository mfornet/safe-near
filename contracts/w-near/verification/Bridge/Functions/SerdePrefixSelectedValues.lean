import Bridge.Functions.SerdePrefixSelectedKey

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeRead (wsLen)

theorem Prefix.value_no_later_start {bs : List UInt8} {start i i' v e : Nat} {key key' : String}
    {pre pre' : Batches} {saved saved' savedNext : Bool} {seg : Segment}
    (hnext : Prefix bs start (.member false) e (pre ++ [seg]) savedNext)
    (h' : Prefix bs start (.value key') i' pre' saved')
    (he : v ≤ e) (hi' : i' < v) (hlt : pre.length < pre'.length) : False := by
  have ht := hnext.canonical_trace
  have ht' := h'.canonical_trace
  simp only [reduceCtorEq, ite_false, Nat.add_zero, List.length_append, List.length_singleton] at ht ht'
  have hle : pre.length + 1 ≤ pre'.length := by omega
  rcases lt_or_eq_of_le hle with hl | heq
  · have hc := h'.before_index _ _ (by simpa using hl) ht
    dsimp only at hc
    omega
  · rw [heq] at ht
    have heq := Option.some.inj (ht.symm.trans ht')
    have hecur := congrArg (fun x => x.2.1) heq
    dsimp only at hecur
    omega

theorem Prefix.value_start_unique {bs : List UInt8} {start i i' v e e' : Nat} {key key' : String}
    {pre pre' : Batches} {saved saved' savedNext savedNext' : Bool} {seg seg' : Segment}
    (h : Prefix bs start (.value key) i pre saved) (h' : Prefix bs start (.value key') i' pre' saved')
    (hnext : Prefix bs start (.member false) e (pre ++ [seg]) savedNext)
    (hnext' : Prefix bs start (.member false) e' (pre' ++ [seg']) savedNext')
    (he : v ≤ e) (he' : v ≤ e') (hi : i < v) (hi' : i' < v) :
    key = key' ∧ i = i' ∧ pre = pre' ∧ saved = saved' := by
  have hn : pre.length = pre'.length := by
    rcases lt_trichotomy pre.length pre'.length with hl | hh | hr
    · exact False.elim (Prefix.value_no_later_start (key := key) (i := i) (saved := saved) hnext h' he hi' hl)
    · exact hh
    · exact False.elim (Prefix.value_no_later_start (key := key') (i := i') (saved := saved') hnext' h he' hi hr)
  have ht := h.canonical_trace
  have ht' := h'.canonical_trace
  simp only [reduceCtorEq, ite_false, Nat.add_zero] at ht ht'
  rw [hn] at ht
  have heq := Option.some.inj (ht.symm.trans ht')
  exact ⟨Phase.value.inj (congrArg Prod.fst heq), congrArg (fun x => x.2.1) heq,
    congrArg (fun x => x.2.2.1) heq, congrArg (fun x => x.2.2.2) heq⟩

structure ValueWitness (bs : List UInt8) (start v : Nat) where
  cursor : Nat
  account : WNear.AccountId
  rest : List UInt8
  history : Batches
  prefixModel : Prefix bs start (.value "account_id") cursor history false
  colon : bs[cursor + wsLen (bs.drop cursor)]? = some 0x3A
  valueStart : v = cursor + wsLen (bs.drop cursor) + 1
  model : WNear.SerdeStructModel.valueAs WNear.account (bs.drop v) = some (account, rest)

theorem ValueWitness.next {bs : List UInt8} {start v : Nat} (w : ValueWitness bs start v) :
    v ≤ bs.length - w.rest.length ∧
    Prefix bs start (.member false) (bs.length - w.rest.length)
      (w.history ++ [.append (ParseStrSuccess.appendChunks (bs.drop (v + wsLen (bs.drop v) + 1)) [])]) true := by
  obtain ⟨j, hj, hq, hs⟩ := SerdeStructObjValueState.account_model w.model
  have hcolon := SerdeNextKey.getElem_lt w.colon
  have hlen := (JsonSuffix.valueAs_suf WNear.account w.model).length_le
  simp only [List.length_drop] at hlen
  have hv : v ≤ bs.length := by rw [w.valueStart]; omega
  have hr := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
  refine ⟨by omega, ?_⟩
  have hsegment : SerdeObjectMixedTrace.ValueSegment bs "account_id" (bs.drop v)
      (bs.length - w.rest.length) (.append (ParseStrSuccess.appendChunks (bs.drop (j + 1)) [])) :=
    .account v j w.account rfl rfl hj hq (by simpa only [hr] using w.model) (by simpa only [hr] using hs)
  have ht := Prefix.value (e := bs.length - w.rest.length) w.prefixModel (fun _ => rfl) w.colon (by rw [← w.valueStart]; omega) (by omega)
    (by simpa only [w.valueStart] using hsegment)
  simpa only [hj, Bool.false_or, beq_self_eq_true] using ht

theorem ValueWitness.history_unique {bs : List UInt8} {start v : Nat} (w w' : ValueWitness bs start v) :
    w.history = w'.history := by
  obtain ⟨he, hn⟩ := w.next
  obtain ⟨he', hn'⟩ := w'.next
  have hi : w.cursor < v := by have := w.valueStart; omega
  have hi' : w'.cursor < v := by have := w'.valueStart; omega
  exact (Prefix.value_start_unique w.prefixModel w'.prefixModel hn hn' he he' hi hi').2.2.1

noncomputable def selectedValueCost (cfg : WasmConfig) (bs : List UInt8) (start baseF v : Nat) : Nat := by
  classical
  exact if h : Nonempty (ValueWitness bs start v) then
    let w := Classical.choice h
    SerdeValueReuse.valueCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history)
      bs w.account.val.toUTF8.toList w.rest v (v + wsLen (bs.drop v))
  else 0

theorem selectedValueCost_of_witness (cfg : WasmConfig) (bs : List UInt8) (start baseF v : Nat)
    (w : ValueWitness bs start v) :
    SerdeValueReuse.valueCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history)
      bs w.account.val.toUTF8.toList w.rest v (v + wsLen (bs.drop v)) = selectedValueCost cfg bs start baseF v := by
  classical
  unfold selectedValueCost
  rw [dif_pos ⟨w⟩]
  let other := Classical.choice (show Nonempty (ValueWitness bs start v) from ⟨w⟩)
  change _ = SerdeValueReuse.valueCost cfg (endFreeBound baseF 0 other.history) (endCap 0 other.history)
    bs other.account.val.toUTF8.toList other.rest v (v + wsLen (bs.drop v))
  have hhistory := w.history_unique other
  have hmodel := Option.some.inj (w.model.symm.trans other.model)
  have ha := congrArg Prod.fst hmodel
  have hr := congrArg Prod.snd hmodel
  dsimp only at ha hr
  rw [hhistory, ha, hr]

theorem Bound.selected_value_charges (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat) :
    ValueGasCharges cfg bs (Bound bs start baseHL baseF false) (selectedValueCost cfg bs start baseF) := by
  intro i j a rest hl F cap hi hcolon hj hq hs hm hb hc hal hp
  obtain ⟨pre, hprefix, hcap, hfree, hlo, hhi⟩ := hb
  subst cap F
  have heq := selectedValueCost_of_witness cfg bs start baseF (i + wsLen (bs.drop i) + 1)
    ⟨i, a, rest, pre, hprefix, hcolon, rfl, hm⟩
  simpa only [hj] using Nat.le_of_eq heq

structure IgnoreWitness (bs : List UInt8) (start v : Nat) where
  key : String
  cursor : Nat
  saved : Bool
  rest : List UInt8
  ops : List Bool
  history : Batches
  prefixModel : Prefix bs start (.value key) cursor history saved
  unknown : key ≠ "account_id"
  colon : bs[cursor + wsLen (bs.drop cursor)]? = some 0x3A
  valueStart : v = cursor + wsLen (bs.drop cursor) + 1
  model : SerdeIgnMachineTrace.trace (bs.drop v) = some (rest, ops)

theorem IgnoreWitness.next {bs : List UInt8} {start v : Nat} (w : IgnoreWitness bs start v) :
    v ≤ bs.length - w.rest.length ∧
    Prefix bs start (.member false) (bs.length - w.rest.length) (w.history ++ [.frames w.ops]) w.saved := by
  have hskip : WNear.IgnoreModel.vSkip (bs.drop v) = some w.rest := by
    rw [← SerdeIgnMachineTrace.erase_trace, w.model]
    rfl
  have hcolon := SerdeNextKey.getElem_lt w.colon
  have hlen := WNear.IgnoreModel.vSkip_length hskip
  simp only [List.length_drop] at hlen
  have hv : v ≤ bs.length := by rw [w.valueStart]; omega
  have hr := JsonSuffix.drop_suf' (IgnoreShallow.vSkip_suf hskip)
  refine ⟨by omega, ?_⟩
  have hsegment : SerdeObjectMixedTrace.ValueSegment bs w.key (bs.drop v)
      (bs.length - w.rest.length) (.frames w.ops) :=
    .ignored v w.ops w.unknown rfl (by simpa only [hr] using w.model)
  have hdup : w.key = "account_id" → w.saved = false := fun heq => False.elim (w.unknown heq)
  have ht := Prefix.value (e := bs.length - w.rest.length) w.prefixModel hdup w.colon
    (by rw [← w.valueStart]; omega) (by omega) (by simpa only [w.valueStart] using hsegment)
  have hk : (w.key == "account_id") = false := by simp [w.unknown]
  simpa only [hk, Bool.or_false] using ht

theorem IgnoreWitness.history_unique {bs : List UInt8} {start v : Nat} (w w' : IgnoreWitness bs start v) :
    w.history = w'.history := by
  obtain ⟨he, hn⟩ := w.next
  obtain ⟨he', hn'⟩ := w'.next
  have hi : w.cursor < v := by have := w.valueStart; omega
  have hi' : w'.cursor < v := by have := w'.valueStart; omega
  exact (Prefix.value_start_unique w.prefixModel w'.prefixModel hn hn' he he' hi hi').2.2.1

noncomputable def selectedIgnoreCost (cfg : WasmConfig) (bs : List UInt8) (start baseF v : Nat) : Nat := by
  classical
  exact if h : Nonempty (IgnoreWitness bs start v) then
    let w := Classical.choice h
    (166 + 470 * (bs.length - w.rest.length - v)) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history) 0 w.ops
  else 0

theorem selectedIgnoreCost_of_witness (cfg : WasmConfig) (bs : List UInt8) (start baseF v : Nat)
    (w : IgnoreWitness bs start v) :
    (166 + 470 * (bs.length - w.rest.length - v)) * cfg.regularOpCost +
      SerdeIgnTrace.extraCost cfg (endFreeBound baseF 0 w.history) (endCap 0 w.history) 0 w.ops =
      selectedIgnoreCost cfg bs start baseF v := by
  classical
  unfold selectedIgnoreCost
  rw [dif_pos ⟨w⟩]
  let other := Classical.choice (show Nonempty (IgnoreWitness bs start v) from ⟨w⟩)
  change _ = (166 + 470 * (bs.length - other.rest.length - v)) * cfg.regularOpCost +
    SerdeIgnTrace.extraCost cfg (endFreeBound baseF 0 other.history) (endCap 0 other.history) 0 other.ops
  have hhistory := w.history_unique other
  have hmodel := Option.some.inj (w.model.symm.trans other.model)
  have hr := congrArg Prod.fst hmodel
  have ho := congrArg Prod.snd hmodel
  dsimp only at hr ho
  rw [hhistory, hr, ho]

theorem Bound.selected_ignore_charges (cfg : WasmConfig) (bs : List UInt8) (start baseHL baseF : Nat)
    (saved : Bool) : IgnoreGasCharges cfg bs (Bound bs start baseHL baseF saved)
      (selectedIgnoreCost cfg bs start baseF) := by
  intro key i hl F cap rest ops hkey hb hc hi hcolon ht hal hp
  obtain ⟨pre, hprefix, hcap, hfree, hlo, hhi⟩ := hb
  subst cap F
  exact Nat.le_of_eq (selectedIgnoreCost_of_witness cfg bs start baseF (i + wsLen (bs.drop i) + 1)
    ⟨key, i, saved, rest, ops, pre, hprefix, hkey, hcolon, rfl, ht⟩)

end WNear.Binary.SerdeObjectPrefix
namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near WNear.Binary WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeIgnObject (ignored)
open WNear.Binary.SerdeObjectMixedTrace
open NearInterface ContractModel in
theorem fully_selected_refines_init (cfg : WNear.Config) (size : Nat)
    (codeOf : List UInt8 → Near.ContractCode) (raw : RawStorage) (ctx : Context) (S : WNear.State) (a : WNear.AccountId) (bs rest : List UInt8) (N : Nat)
    (hlen : bs.length ≤ 4194304)
    (hp : WProtocol ctx.protocol) (hwf : ctx.WF raw)
    (hm : ctx.method = "ft_balance_of") (hl : FtTotalSupplyMethod.LimitsV86 ctx.protocol)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hend : bs.length - rest.length + wsLen (bs.drop (bs.length - rest.length)) = bs.length)
    (hbudget : BalanceOf297AbsentCall.ProviderModelBudget cfg size raw (some S) ctx S a
      (ledgerParserCost ctx.protocol.wasm (selectedKeyCost ctx.protocol.wasm bs (wsLen bs + 1) 1) (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1) (selectedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) bs rest N) 44)
    (hargs : ctx.args = bs) (hrep : (WNear.wnear cfg).Represents raw (some S))
    (ha : a ∉ S.registered) :
    let r := Near.Boundary.nearRuntime.exec (wCode size codeOf) raw ctx
    let res := (WNear.wnear cfg).step ctx (some S) (.ftBalanceOf a)
    (∀ msg, r.outcome ≠ .error (.executionIssue msg)) ∧
    ((WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a) ≤ ctx.gasLimit →
      ctx.ProofRoom ((WNear.wnear cfg).proofBound ctx (some S) (.ftBalanceOf a)) →
      Matches (WNear.wnear cfg) ctx raw r res ∧ r.usedGas ≤ (WNear.wnear cfg).gas ctx (some S) (.ftBalanceOf a)) ∧
    (Matches (WNear.wnear cfg) ctx raw r res ∨
      (ResourceFailure r ∧ RolledBack ctx raw r ∧ r.logs <+: res.logs)) := by
  exact selected_key_refines_init cfg size codeOf raw ctx S a bs rest N (selectedValueCost ctx.protocol.wasm bs (wsLen bs + 1) 1) (selectedIgnoreCost ctx.protocol.wasm bs (wsLen bs + 1) 1) hlen hp hwf hm hl
    (fun len _ => Bound.selected_value_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1)
    (fun len _ => Bound.selected_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 false)
    (fun len _ => Bound.selected_ignore_charges ctx.protocol.wasm bs (wsLen bs + 1) len 1 true)
    ho hloop hend hbudget hargs hrep ha

end WNear.Binary.SerdeObjectPrefix
