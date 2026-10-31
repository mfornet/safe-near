import Bridge.Functions.SerdeTraceCost
import Bridge.Methods.FtBalanceOfArrayCase
import Bridge.Functions.SerdeWeightedBundled
import Bridge.Methods.FtBalanceOfWeightedLinearGas
set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open WNear.Binary.ScratchMixedTrace

theorem mixed_growth_structural_budget (cfg : WasmConfig) (batches : Batches)
    (hv : Valid 0 batches) (hp : peak 0 batches ≤ 4194304)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    extraCost cfg 1 0 batches ≤ 36 * peak 0 batches * cfg.regularOpCost + 200000000000 := by
  have hg := ScratchMixedTrace.growth_v86 batches hv hp
  have he := extraCost_budget cfg 1 0 batches hv
  have hgg := Nat.mul_le_mul hg hg
  have hwalk : 1 * growthCount 0 batches + growthCount 0 batches * growthCount 0 batches - growthCount 0 batches ≤ 441 := by omega
  have hpage : (4 * peak 0 batches + 16 + 66066 * growthCount 0 batches) / 65536 ≤ 278 := by omega
  have hgbase := Nat.mul_le_mul hg hbase
  have hunitcost := Nat.mul_le_mul hunit hpage
  have hregular := Nat.mul_le_mul (show 1790 * growthCount 0 batches +
      (1 * growthCount 0 batches + growthCount 0 batches * growthCount 0 batches - growthCount 0 batches) * 320 + 144 ≤ 178854 by omega) hop
  unfold budget at he
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc] at he hregular ⊢
  omega

end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeKeyReuse
open Wasm Wasm.Near
open WNear.Binary.ParseStr
open WNear.Binary.ParseStrSuccess
theorem ignored_member_regular_budget_credit (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs : List UInt8) (q : Nat) (key : String) (rest : List UInt8) (m : Nat)
    (hlen : bs.length < 2 ^ 24) (hm : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    (942 + 166 + 470 * m) * cfg.regularOpCost + SerdeKey.cost194 * cfg.regularOpCost +
      bundledCost cfg F cap bs key.toUTF8.toList rest q +
      (36 * ((bs.drop q).length - rest.length) - 340) * cfg.regularOpCost ≤
    470 * (((bs.drop q).length - rest.length) + m + 3) * cfg.regularOpCost +
      ScratchGrow.extraCost cfg F cap 0 (appendChunks (bs.drop q) []) := by
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hm
  have hs := SerdeDeStrEsc.strRun_size (bs.drop q) [] key.toUTF8.toList rest hok
  simp only [List.length_nil, Nat.zero_add] at hs
  by_cases hb : borrowed (bs.drop q)
  · have hkey := bundledCost_borrowed_tight cfg F cap bs q key rest hb hok hu
    have hops : 942 + 166 + 470 * m + (if key.toUTF8.toList.length = 10 then 642 else 380) +
        130 * ((bs.drop q).length - rest.length) + (36 * ((bs.drop q).length - rest.length) - 340) ≤ 470 * (((bs.drop q).length - rest.length) + m + 3) := by
      split <;> omega
    have hmul := Nat.mul_le_mul_right cfg.regularOpCost hops
    simp only [Nat.add_mul, Nat.mul_assoc] at hkey hmul ⊢
    omega
  · have hmin := copied_consumed cfg (bs.drop q) key.toUTF8.toList rest (by simp only [List.length_drop]; omega) hok hb
    have hkey := bundledCost_growth_tight cfg F cap bs q key rest hlen hm
    have hops : 942 + 166 + 470 * m + (if key.toUTF8.toList.length = 10 then 642 else 380) +
        433 * ((bs.drop q).length - rest.length) + (36 * ((bs.drop q).length - rest.length) - 340) ≤ 470 * (((bs.drop q).length - rest.length) + m + 3) := by
      split <;> omega
    have hmul := Nat.mul_le_mul_right cfg.regularOpCost hops
    simp only [Nat.add_mul, Nat.mul_assoc] at hkey hmul ⊢
    omega

end WNear.Binary.SerdeKeyReuse

namespace WNear.Binary.ScratchMixedTrace
open Wasm Wasm.Near
open WNear.Binary

def Segment.workCredit (cap : UInt32) : Segment → Nat
  | .append ks => 36 * Segment.peak cap (.append ks) - 2304
  | .frames ops => 74 * SerdeIgnTrace.pushCount ops

def workCredit (cap : UInt32) : Batches → Nat
  | [] => 0
  | seg :: rest => Segment.workCredit cap seg + workCredit (Segment.next cap seg) rest

theorem Segment.peak_credit (cap : UInt32) (seg : Segment) :
    36 * Segment.peak cap seg ≤ Segment.workCredit cap seg + 2304 := by
  cases seg with
  | append ks => simp only [Segment.workCredit]; omega
  | frames ops =>
    have hp := SerdeIgnTrace.peak_le 0 ops
    simp only [Segment.peak, Segment.workCredit]
    omega

theorem peak_credit (cap : UInt32) (batches : Batches) :
    36 * peak cap batches ≤ workCredit cap batches + 2304 := by
  induction batches generalizing cap with
  | nil => simp [peak, workCredit]
  | cons seg rest ih =>
    have hh := Segment.peak_credit cap seg
    have ht := ih (Segment.next cap seg)
    simp only [peak, workCredit]
    omega

end WNear.Binary.ScratchMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open WNear.Binary.ScratchMixedTrace

theorem mixed_growth_credit_budget (cfg : WasmConfig) (batches : Batches)
    (hv : Valid 0 batches) (hp : peak 0 batches ≤ 4194304)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    extraCost cfg 1 0 batches ≤ workCredit 0 batches * cfg.regularOpCost + 202000000000 := by
  have he := mixed_growth_structural_budget cfg batches hv hp hop hbase hunit
  have hc := Nat.mul_le_mul_right cfg.regularOpCost (peak_credit 0 batches)
  have hfixed := Nat.mul_le_mul_left 2304 hop
  simp only [Nat.add_mul, Nat.mul_assoc] at he hc
  omega

end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near NearInterface.Json
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectPrefix

theorem account_workCredit_zero (bs : List UInt8) (j e : Nat) (cap : UInt32) (a : WNear.AccountId)
    (hlen : bs.length ≤ 4194304) (hcap : cap.toNat < 2 ^ 25)
    (hs : stringBody (bs.drop (j + 1)) [] = some (some a.val, bs.drop e)) :
    Segment.workCredit cap (.append (ParseStrSuccess.appendChunks (bs.drop (j + 1)) [])) = 0 := by
  obtain ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hs
  have hp := ParseStrSuccess.appendChunks_valid cap [] (bs.drop (j + 1)) a.val.toUTF8.toList (bs.drop e)
    hok (by simp) (by omega) (by simp only [List.length_nil, Nat.zero_add, List.length_drop]; omega)
  have hv := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hv
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hv
  simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hp
  simp only [Segment.workCredit, Segment.peak]
  omega

end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near NearInterface.Json
open WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeKeyEsc (KeySample)
open WNear.Binary.SerdeObjectPrefix
open WNear.Binary.ScratchMixedTrace

theorem ValueSegment.selected_weighted_charge {bs : List UInt8} {start i e : Nat} {key : String}
    {pre : Batches} {saved : Bool} {seg : Segment}
    (cfg : WasmConfig) (hlen : bs.length ≤ 4194304)
    (hp : Prefix bs start (.value key) i pre saved)
    (hdup : key = "account_id" → saved = false)
    (hcolon : bs[i + wsLen (bs.drop i)]? = some 0x3A)
    (he : i + wsLen (bs.drop i) + 1 ≤ e) (heb : e ≤ bs.length)
    (hv : ValueSegment bs key (bs.drop (i + wsLen (bs.drop i) + 1)) e seg)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    (if key = "account_id" then selectedValueCost cfg bs start 1 (i + wsLen (bs.drop i) + 1)
      else selectedWeightedIgnoreCost cfg bs start 1 (i + wsLen (bs.drop i) + 1)) +
      Segment.workCredit (endCap 0 pre) seg * cfg.regularOpCost ≤
      (166 + 470 * (e - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost +
      (if key = "account_id" then 500000000000 else 0) +
      Segment.extraCost cfg (endFreeBound 1 0 pre) (endCap 0 pre) seg := by
  have hrest : bs.length - (bs.drop e).length = e := by simp only [List.length_drop]; omega
  cases hv with
  | account v j a hk hin hj hq hm hs =>
    have hsave := hdup hk
    subst key saved
    rw [← hin] at hm
    let w : ValueWitness bs start (i + wsLen (bs.drop i) + 1) :=
      ⟨i, a, bs.drop e, pre, hp, hcolon, rfl, hm⟩
    have hb := selectedValueCost_account_bound cfg bs start _ w hlen hop hbase hunit
    dsimp only [w] at hb
    rw [hrest] at hb
    have hcap := (batches_bounds bs pre 0 hlen (by decide) hp.models).2.1
    have hcredit := account_workCredit_zero bs j e (endCap 0 pre) a hlen hcap hs
    simp only [ite_true, hrest, hcredit, Nat.zero_mul, Nat.add_zero]
    omega
  | ignored v ops hk hin ht =>
    rw [← hin] at ht
    let w : IgnoreWitness bs start (i + wsLen (bs.drop i) + 1) :=
      ⟨key, i, saved, bs.drop e, ops, pre, hp, hk, hcolon, rfl, ht⟩
    have heq := selectedWeightedIgnoreCost_of_witness cfg bs start 1 _ w
    dsimp only [w] at heq
    simp only [hrest] at heq
    simp only [if_neg hk, Nat.add_zero, Segment.extraCost]
    have hskip : WNear.IgnoreModel.vSkip (bs.drop (i + wsLen (bs.drop i) + 1)) = some (bs.drop e) := by
      rw [← SerdeIgnMachineTrace.erase_trace, ht]
      rfl
    obtain ⟨other, hother, _, _, hpush, _⟩ := SerdeIgnMachineTrace.trace_some hskip
    have heops : other = ops := (Prod.mk.inj (Option.some.inj (hother.symm.trans ht))).2
    subst other
    simp only [List.length_drop] at hpush
    have hsub : 74 * SerdeIgnTrace.pushCount ops ≤ 166 + 470 * (e - (i + wsLen (bs.drop i) + 1)) := by omega
    have hmul := congrArg (fun z => z * cfg.regularOpCost) (Nat.sub_add_cancel hsub)
    simp only [Nat.add_mul] at hmul
    simp only [Segment.workCredit, Nat.add_mul] at heq hmul ⊢
    omega


end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near NearInterface.Json
open WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeKeyEsc (KeySample)
open WNear.Binary.SerdeObjectPrefix
open WNear.Binary.ScratchMixedTrace

theorem member_selected_weighted_charge {bs : List UInt8} {start i q e : Nat} {first saved : Bool}
    {key : String} {r1 r2 : List UInt8} {pre : Batches} {seg : Segment}
    (cfg : WasmConfig) (hlen : bs.length ≤ 4194304)
    (hp : Prefix bs start (.member first) i pre saved)
    (hq : SerdeNextKey.keyQ first bs i = some q)
    (hs : stringBody (bs.drop q) [] = some (some key, r1))
    (hc : colonAt r1 = some r2) (he : bs.length - r2.length ≤ e) (heb : e ≤ bs.length)
    (hv : ValueSegment bs key r2 e seg) (hdup : key = "account_id" → saved = false)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    (942 + 96 * (SerdeNextKey.keyWs first bs i + wsLen (bs.drop (bs.length - r1.length))) + SerdeKey.cost194) * cfg.regularOpCost +
      selectedBundledKeyCost cfg bs start 1 q +
      (if key = "account_id" then selectedValueCost cfg bs start 1 (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)
        else selectedWeightedIgnoreCost cfg bs start 1 (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)) +
      workCredit (endCap 0 pre) [.append (ParseStrSuccess.appendChunks (bs.drop q) []), seg] * cfg.regularOpCost ≤
    470 * (e - i + (if first then 1 else 0)) * cfg.regularOpCost +
      (if key = "account_id" then 500000000000 else 0) +
      extraCost cfg (endFreeBound 1 0 pre) (endCap 0 pre)
        [.append (ParseStrSuccess.appendChunks (bs.drop q) []), seg] := by
  have hr1 := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
  have hc' : colonAt (bs.drop (bs.length - r1.length)) = some r2 := by rw [hr1]; exact hc
  have hcolon := colon_at_byte hc'
  have hr2 := SerdeObjectCoverage.colon_result hc'
  have hvlt := SerdeNextKey.getElem_lt hcolon
  have hve : bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1 ≤ e := by
    rw [hr2] at he
    simp only [List.length_drop] at he
    omega
  have hval := hv
  rw [hr2] at hval
  have hvbound := hval.selected_weighted_charge cfg hlen (Prefix.key hp hq hs) hdup hcolon hve heb hop hbase hunit
  have hsmall : bs.length < 2 ^ 24 := by omega
  have hkey := SerdeKeyReuse.ignored_member_regular_budget_credit cfg (endFreeBound 1 0 pre) (endCap 0 pre)
    bs q key r1 (e - (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)) hsmall hs
  rw [selectedBundledKeyCost_of_witness cfg bs start 1 q ⟨first, i, key, r1, pre, saved, hp, hq, hs⟩] at hkey
  obtain ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hs
  have hcappre := (batches_bounds bs pre 0 hlen (by decide) hp.models).2.1
  have hkeytrace := ParseStrSuccess.appendChunks_valid (endCap 0 pre) [] (bs.drop q) key.toUTF8.toList r1
    hok (by simp) (by omega) (by simp only [List.length_nil, Nat.zero_add, List.length_drop]; omega)
  have hkeysize := SerdeDeStrEsc.strRun_size (bs.drop q) [] key.toUTF8.toList r1 hok
  simp only [List.length_nil, Nat.zero_add, show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hkeytrace hkeysize
  have hcredit : Segment.workCredit (endCap 0 pre) (.append (ParseStrSuccess.appendChunks (bs.drop q) [])) ≤
      36 * ((bs.drop q).length - r1.length) - 340 := by
    simp only [Segment.workCredit, Segment.peak]
    omega
  have hcreditmul := Nat.mul_le_mul_right cfg.regularOpCost hcredit
  have hpartition := member_consumed_exact hq hs hc he heb
  have hwork : 470 * (((bs.drop q).length - r1.length) +
      (e - (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)) + 3) +
      96 * (SerdeNextKey.keyWs first bs i + wsLen (bs.drop (bs.length - r1.length))) ≤
      470 * (e - i + (if first then 1 else 0)) := by
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hpartition ⊢ <;> omega
  have hm := Nat.mul_le_mul_right cfg.regularOpCost hwork
  simp only [Ledger.free_append, Ledger.endCap_append, endFreeBound, endCap,
    Segment.endFreeBound, Segment.next] at hvbound
  simp only [Segment.extraCost] at hvbound
  simp only [extraCost, workCredit, Segment.extraCost, Segment.endFreeBound, Segment.next, Nat.add_zero]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hkey hvbound hm hcreditmul ⊢
  omega


end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near NearInterface.Json
open WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeKeyEsc (KeySample)
open WNear.Binary.SerdeObjectPrefix
open WNear.Binary.ScratchMixedTrace

theorem CallTrace.selected_weighted_cost_le {bs : List UInt8} {start i stop accounts : Nat} {first saved : Bool}
    {keys : List KeySample} {batches pre : Batches}
    (ht : CallTrace bs i first keys batches stop accounts)
    (cfg : WasmConfig) (hlen : bs.length ≤ 4194304)
    (hp : Prefix bs start (.member first) i pre saved)
    (hslots : accounts + (if saved then 1 else 0) ≤ 1)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    traceCost cfg.regularOpCost (selectedBundledKeyCost cfg bs start 1)
      (selectedValueCost cfg bs start 1) (selectedWeightedIgnoreCost cfg bs start 1) bs i first keys +
      workCredit (endCap 0 pre) batches * cfg.regularOpCost ≤
      470 * (stop - i + (if first then 1 else 0)) * cfg.regularOpCost +
      500000000000 * accounts + extraCost cfg (endFreeBound 1 0 pre) (endCap 0 pre) batches := by
  induction ht generalizing pre saved with
  | done i hb =>
    simp only [traceCost, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.mul_zero, Nat.zero_mul, extraCost, workCredit]
    have hwork : 300 + 96 * wsLen (bs.drop i) ≤ 470 * (i + wsLen (bs.drop i) + 1 - i) := by omega
    exact Nat.mul_le_mul_right cfg.regularOpCost hwork
  | member i q e stop first key r1 r2 keys value batches accounts hq hs hc he heb hv ht ih =>
    have hdup : key = "account_id" → saved = false := by intro hk; cases saved <;> simp_all
    have htail : accounts + (if saved || key == "account_id" then 1 else 0) ≤ 1 := by
      by_cases hk : key = "account_id"
      · have hsave := hdup hk
        simp only [hsave, hk, ite_true, Bool.false_or, beq_self_eq_true] at hslots ⊢
        omega
      · have hfalse : (key == "account_id") = false := by simp [hk]
        simpa only [if_neg hk, Nat.zero_add, hfalse, Bool.or_false] using hslots
    have hr1 := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
    have hc' : colonAt (bs.drop (bs.length - r1.length)) = some r2 := by rw [hr1]; exact hc
    have hcolon := colon_at_byte hc'
    have hr2 := SerdeObjectCoverage.colon_result hc'
    have hvlt := SerdeNextKey.getElem_lt hcolon
    have hve : bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1 ≤ e := by
      rw [hr2] at he
      simp only [List.length_drop] at he
      omega
    have hval := hv
    rw [hr2] at hval
    have hnext := Prefix.value (Prefix.key hp hq hs) hdup hcolon hve heb hval
    have hrest := ih hnext htail
    have hmember := member_selected_weighted_charge cfg hlen hp hq hs hc he heb hv hdup hop hbase hunit
    have hend := hv.end_eq heb
    simp only [traceCost, hc, hend]
    have hie := (SerdeObjectCoverage.key_charge hq hs hc he).1
    have hes := ht.input_work.1
    have hsplit : stop - i + (if first then 1 else 0) =
        (e - i + (if first then 1 else 0)) + (stop - e) := by omega
    rw [hsplit]
    simp only [Ledger.free_append, Ledger.endCap_append, endFreeBound, endCap] at hrest
    simp only [extraCost, workCredit, Nat.add_zero] at hmember ⊢
    simp only [Nat.add_mul, Nat.mul_add] at hrest hmember ⊢
    by_cases hk : key = "account_id" <;> simp only [hk, Bool.false_eq_true, if_pos, if_neg, ite_true, ite_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at hslots hrest hmember ⊢ <;> omega


end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near NearInterface.Json
open WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeKeyEsc (KeySample)
open WNear.Binary.SerdeObjectPrefix
open WNear.Binary.ScratchMixedTrace

open WNear.SerdeStructLoop
theorem loop_selected_weighted_cost_le (cfg : WasmConfig) (bs : List UInt8) (N i : Nat)
    (a : WNear.AccountId) (rest : List UInt8) (hlen : bs.length ≤ 4194304) (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N true none (bs.drop i) = some (some a, rest))
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    ∃ batches accounts keys, CallTrace bs i true keys batches (bs.length - rest.length) accounts ∧ accounts ≤ 1 ∧
      SerdeStructObj.objCost cfg.regularOpCost (selectedBundledKeyCost cfg bs i 1)
        (selectedValueCost cfg bs i 1) (selectedWeightedIgnoreCost cfg bs i 1) (valueAs WNear.account) SerdeIgnObject.ignored bs N true i + workCredit 0 batches * cfg.regularOpCost ≤
      470 * (bs.length - rest.length - i + 1) * cfg.regularOpCost +
        500000000000 + extraCost cfg 1 0 batches := by
  obtain ⟨keys, hw, hf, hc⟩ := loop_keys_fuel_account bs N true i none a rest hi hloop
  obtain ⟨batches, accounts, ht⟩ := expand_key_walk hw
  have haccounts := call_trace_accounts ht
  have ha : accounts ≤ 1 := by simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hc; omega
  have hslots : accounts + (if false then 1 else 0) ≤ 1 := by simpa using ha
  have hg := ht.selected_weighted_cost_le cfg hlen (Prefix.initial (bs := bs) (start := i)) hslots hop hbase hunit
  rw [← ht.objCost_eq cfg.regularOpCost _ _ _ N hf] at hg
  simp only [ite_true, endFreeBound, endCap] at hg
  have hfixed := Nat.mul_le_mul_left 500000000000 ha
  exact ⟨batches, accounts, keys, ht, ha, by omega⟩

/-- Full selected parser cost, retaining exactly the complete mixed-growth term. -/
theorem selected_weighted_parser_cost_le (cfg : WasmConfig) (bs : List UInt8) (N : Nat)
    (a : WNear.AccountId) (rest : List UInt8) (hlen : bs.length ≤ 4194304)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    ∃ batches, (∀ seg ∈ batches, SegmentModel bs seg) ∧
      ledgerParserCost cfg (selectedBundledKeyCost cfg bs (wsLen bs + 1) 1)
        (selectedValueCost cfg bs (wsLen bs + 1) 1) (selectedWeightedIgnoreCost cfg bs (wsLen bs + 1) 1) bs rest N + workCredit 0 batches * cfg.regularOpCost ≤
      (2215 + 470 * bs.length) * cfg.regularOpCost + 500000000000 + extraCost cfg 1 0 batches := by
  have hstart := SerdeNextKey.getElem_lt ho
  have hloop' : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N true none (bs.drop (wsLen bs + 1)) = some (some a, rest) := by
    simpa only [loopRes, ite_true] using hloop
  obtain ⟨batches, accounts, keys, ht, ha, hg⟩ := loop_selected_weighted_cost_le cfg bs N (wsLen bs + 1) a rest hlen (by omega) hloop' hop hbase hunit
  have hrest := ht.input_work.1
  have hws := SerdeRead.wsLen_le (bs.drop (bs.length - rest.length))
  simp only [List.length_drop] at hws
  refine ⟨batches, call_trace_models ht, ?_⟩
  unfold ledgerParserCost SerdeStructObj.costObj
  simp only [List.drop_zero, Nat.zero_add]
  have hwork : 2215 + 96 * wsLen bs + 96 * wsLen (bs.drop (bs.length - rest.length)) +
      470 * (bs.length - rest.length - (wsLen bs + 1) + 1) ≤ 2215 + 470 * bs.length := by omega
  have hm := Nat.mul_le_mul_right cfg.regularOpCost hwork
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hg hm ⊢
  omega


end WNear.Binary.SerdeObjectMixedTrace

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeObjectPrefix
open WNear.Binary.ScratchMixedTrace

theorem selected_weighted_parser_linear_full (cfg : WasmConfig) (bs rest : List UInt8) (N : Nat)
    (a : WNear.AccountId) (hlen : bs.length ≤ 4194304)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    SelectedWeightedParserLinearBudget cfg bs rest N := by
  obtain ⟨batches, hm, he⟩ := selected_weighted_parser_cost_le cfg bs N a rest hlen ho hloop hop hbase hunit
  obtain ⟨hv, _, hp⟩ := batches_bounds bs batches 0 hlen (by decide) hm
  have hg := mixed_growth_credit_budget cfg batches hv (hp.trans hlen) hop hbase hunit
  unfold SelectedWeightedParserLinearBudget
  omega

end WNear.Binary.SerdeObjectMixedTrace
