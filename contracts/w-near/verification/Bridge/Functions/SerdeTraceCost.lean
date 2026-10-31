import Bridge.Exported
import Bridge.Methods.FtBalanceOfProviderLinearGas
import Bridge.Functions.SerdeBundledKeyState
import Bridge.Functions.SerdeMixedPrefix
import Bridge.Functions.SerdeBundledRate
import Bridge.Functions.SerdeAccountBudget


set_option maxRecDepth 100000

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near NearInterface.Json
open WNear.JsonFuel WNear.SerdeStructModel
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeKeyEsc (KeySample)
open WNear.Binary.SerdeObjectPrefix
open WNear.Binary.ScratchMixedTrace

def traceCost (c : Nat) (Kkey Kvalue Kignore : Nat → Nat) (bs : List UInt8) :
    Nat → Bool → List KeySample → Nat
  | i, _, [] => (300 + 96 * wsLen (bs.drop i)) * c
  | i, first, (q, key, rest) :: keys =>
    let j := bs.length - rest.length
    let v := j + wsLen (bs.drop j) + 1
    match colonAt rest with
    | none => 0
    | some input =>
      match valueEnd bs key input with
      | none => 0
      | some e =>
        (942 + 96 * (SerdeNextKey.keyWs first bs i + wsLen (bs.drop j)) + SerdeKey.cost194) * c +
          Kkey q + ((if key = "account_id" then Kvalue v else Kignore v) +
            traceCost c Kkey Kvalue Kignore bs e false keys)

theorem keyQ_not_brace {bs : List UInt8} {i q : Nat} {first : Bool}
    (hq : SerdeNextKey.keyQ first bs i = some q) :
    bs[i + wsLen (bs.drop i)]? ≠ some 0x7D := by
  cases first <;> simp only [SerdeNextKey.keyQ, Bool.false_eq_true, ite_false, ite_true] at hq
  · split at hq
    · rename_i hh
      rw [hh]; decide
    · simp at hq
  · split at hq
    · rename_i hh
      rw [hh]; decide
    · simp at hq

/-- The original costObj recurrence is exactly the cost of its complete actual trace. -/
theorem CallTrace.objCost_eq {bs : List UInt8} {i stop accounts : Nat} {first : Bool}
    {keys : List KeySample} {batches : ScratchMixedTrace.Batches}
    (ht : CallTrace bs i first keys batches stop accounts)
    (c : Nat) (Kkey Kvalue Kignore : Nat → Nat) (N : Nat) (hN : keys.length ≤ N) :
    SerdeStructObj.objCost c Kkey Kvalue Kignore (valueAs WNear.account) SerdeIgnObject.ignored bs N first i =
      traceCost c Kkey Kvalue Kignore bs i first keys := by
  induction ht generalizing N with
  | done i hb =>
    rw [SerdeStructObj.objCost_end c Kkey Kvalue Kignore _ _ bs hb]
    rfl
  | member i q e stop first key r1 r2 keys value batches accounts hq hs hc he heb hv ht ih =>
    cases N with
    | zero => simp at hN
    | succ N =>
      have htail : keys.length ≤ N := by simpa using hN
      have hnot := keyQ_not_brace hq
      have hr1 := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
      have hc' : colonAt (bs.drop (bs.length - r1.length)) = some r2 := by rw [hr1]; exact hc
      have hr2 := SerdeObjectCoverage.colon_result hc'
      have hvend := hv.end_eq heb
      simp only [traceCost, hc, hvend]
      rw [SerdeStructObj.objCost.eq_def]
      simp only [if_neg hnot, hq, hs]
      by_cases hk : key = "account_id"
      · simp only [valueEnd, if_pos hk] at hvend
        obtain ⟨ar, har, heq⟩ := Option.map_eq_some_iff.mp hvend
        obtain ⟨a, rest⟩ := ar
        simp only at heq
        rw [hr2] at har
        simp only [if_pos hk, har]
        rw [heq, ih N htail]
      · simp only [valueEnd, if_neg hk] at hvend
        obtain ⟨ar, har, heq⟩ := Option.map_eq_some_iff.mp hvend
        obtain ⟨u, rest⟩ := ar
        simp only at heq
        rw [hr2] at har
        simp only [if_neg hk, har]
        rw [heq, ih N htail]

/-- Both exact receipt-selected value charges admit one common byte/growth sum. -/
theorem ValueSegment.selected_charge {bs : List UInt8} {start i e : Nat} {key : String}
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
      else selectedIgnoreCost cfg bs start 1 (i + wsLen (bs.drop i) + 1)) ≤
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
    simp only [ite_true, hrest]
    omega
  | ignored v ops hk hin ht =>
    rw [← hin] at ht
    let w : IgnoreWitness bs start (i + wsLen (bs.drop i) + 1) :=
      ⟨key, i, saved, bs.drop e, ops, pre, hp, hk, hcolon, rfl, ht⟩
    have heq := selectedIgnoreCost_of_witness cfg bs start 1 _ w
    dsimp only [w] at heq
    simp only [hrest] at heq
    simp only [if_neg hk, Nat.add_zero, Segment.extraCost]
    exact Nat.le_of_eq heq.symm

/-- One actual member's exact selected charges fit its disjoint bytes and retained growth. -/
theorem member_selected_charge {bs : List UInt8} {start i q e : Nat} {first saved : Bool}
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
        else selectedIgnoreCost cfg bs start 1 (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)) ≤
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
  have hvbound := hval.selected_charge cfg hlen (Prefix.key hp hq hs) hdup hcolon hve heb hop hbase hunit
  have hsmall : bs.length < 2 ^ 24 := by omega
  have hkey := SerdeKeyReuse.ignored_member_regular_budget_470 cfg (endFreeBound 1 0 pre) (endCap 0 pre)
    bs q key r1 (e - (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)) hsmall hs
  rw [selectedBundledKeyCost_of_witness cfg bs start 1 q ⟨first, i, key, r1, pre, saved, hp, hq, hs⟩] at hkey
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
  simp only [extraCost, Segment.extraCost, Segment.endFreeBound, Segment.next, Nat.add_zero]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hkey hvbound hm ⊢
  omega

/-- Sum exact selected charges along the full retained trace; account reserve is charged once. -/
theorem CallTrace.selected_cost_le {bs : List UInt8} {start i stop accounts : Nat} {first saved : Bool}
    {keys : List KeySample} {batches pre : Batches}
    (ht : CallTrace bs i first keys batches stop accounts)
    (cfg : WasmConfig) (hlen : bs.length ≤ 4194304)
    (hp : Prefix bs start (.member first) i pre saved)
    (hslots : accounts + (if saved then 1 else 0) ≤ 1)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    traceCost cfg.regularOpCost (selectedBundledKeyCost cfg bs start 1)
      (selectedValueCost cfg bs start 1) (selectedIgnoreCost cfg bs start 1) bs i first keys ≤
      470 * (stop - i + (if first then 1 else 0)) * cfg.regularOpCost +
      500000000000 * accounts + extraCost cfg (endFreeBound 1 0 pre) (endCap 0 pre) batches := by
  induction ht generalizing pre saved with
  | done i hb =>
    simp only [traceCost, Bool.false_eq_true, ite_false, Nat.add_zero, Nat.mul_zero, extraCost]
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
    have hmember := member_selected_charge cfg hlen hp hq hs hc he heb hv hdup hop hbase hunit
    have hend := hv.end_eq heb
    simp only [traceCost, hc, hend]
    have hie := (SerdeObjectCoverage.key_charge hq hs hc he).1
    have hes := ht.input_work.1
    have hsplit : stop - i + (if first then 1 else 0) =
        (e - i + (if first then 1 else 0)) + (stop - e) := by omega
    rw [hsplit]
    simp only [Ledger.free_append, Ledger.endCap_append, endFreeBound, endCap] at hrest
    simp only [extraCost, Nat.add_zero] at hmember ⊢
    simp only [Nat.add_mul, Nat.mul_add] at hrest hmember ⊢
    by_cases hk : key = "account_id" <;> simp only [hk, Bool.false_eq_true, if_pos, if_neg, ite_true, ite_false, Nat.mul_one, Nat.mul_zero, Nat.add_zero] at hslots hrest hmember ⊢ <;> omega

open WNear.SerdeStructLoop
open WNear.Binary.SerdeObjectCoverage (KeyWalk)
theorem loop_keys_fuel_account (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8)
    (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys, KeyWalk bs i first keys (bs.length - rest.length) ∧ keys.length ≤ N ∧ accountCount keys + (if seen.isSome then 1 else 0) ≤ 1 := by
  induction N generalizing first i seen with
  | zero =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_, by simp, by cases seen <;> simp [accountCount]⟩
      have he : bs.length - rest.length = i + wsLen (bs.drop i) + 1 := by rw [hr, List.length_drop]; omega
      rw [he]
      exact .done i hb
    · obtain ⟨n, _, _, _, hn, _⟩ := loop_member "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      omega
  | succ N ih =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_, by simp, by cases seen <;> simp [accountCount]⟩
      have he : bs.length - rest.length = i + wsLen (bs.drop i) + 1 := by rw [hr, List.length_drop]; omega
      rw [he]
      exact .done i hb
    · obtain ⟨n, q, k, r1, hn, hq, hs, hdup, r2, hc, hv⟩ :=
        loop_member "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hn' : n = N := by omega
      subst n
      have hsuf1 := (JsonSuffix.stringBody_suf' hs).trans (List.drop_suffix q bs)
      have hsuf2 := (JsonSuffix.colonAt_suf hc).trans hsuf1
      rcases hv with ⟨hk, a', r3, hv, ht⟩ | ⟨hk, r3, hv, ht⟩
      · have hnone : seen = none := by
          cases seen with
          | none => rfl
          | some a => simp [hk] at hdup
        subst seen
        have h3 := JsonSuffix.valueAs_suf WNear.account hv
        have hsuf3 := h3.trans hsuf2
        have hd3 := JsonSuffix.drop_suf hsuf3
        have hie : bs.length - r3.length ≤ bs.length := by omega
        rw [← hd3] at ht
        obtain ⟨keys, hkeys, hfuel, hcount⟩ := ih false (bs.length - r3.length) (some a') hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inl ⟨hk, a', by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys, by simpa using Nat.succ_le_succ hfuel, by simp only [accountCount, hk, ite_true, Option.isSome_none, Bool.false_eq_true, ite_false]; simp only [Option.isSome_some, ite_true] at hcount; omega⟩
      · have hv' : WNear.IgnoreModel.vSkip r2 = some r3 := by simpa [SerdeIgnObject.ignored] using hv
        have h3 := IgnoreShallow.vSkip_suf hv'
        have hsuf3 := h3.trans hsuf2
        have hd3 := JsonSuffix.drop_suf hsuf3
        have hie : bs.length - r3.length ≤ bs.length := by omega
        rw [← hd3] at ht
        obtain ⟨keys, hkeys, hfuel, hcount⟩ := ih false (bs.length - r3.length) seen hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inr ⟨hk, by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys, by simpa using Nat.succ_le_succ hfuel, by simpa only [accountCount, hk, ite_false, Nat.zero_add] using hcount⟩



/-- The actual initial costObj is bounded by disjoint input, one account reserve and one retained growth history. -/
theorem loop_selected_cost_le (cfg : WasmConfig) (bs : List UInt8) (N i : Nat)
    (a : WNear.AccountId) (rest : List UInt8) (hlen : bs.length ≤ 4194304) (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N true none (bs.drop i) = some (some a, rest))
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    ∃ batches accounts keys, CallTrace bs i true keys batches (bs.length - rest.length) accounts ∧ accounts ≤ 1 ∧
      SerdeStructObj.objCost cfg.regularOpCost (selectedBundledKeyCost cfg bs i 1)
        (selectedValueCost cfg bs i 1) (selectedIgnoreCost cfg bs i 1) (valueAs WNear.account) SerdeIgnObject.ignored bs N true i ≤
      470 * (bs.length - rest.length - i + 1) * cfg.regularOpCost +
        500000000000 + extraCost cfg 1 0 batches := by
  obtain ⟨keys, hw, hf, hc⟩ := loop_keys_fuel_account bs N true i none a rest hi hloop
  obtain ⟨batches, accounts, ht⟩ := expand_key_walk hw
  have haccounts := call_trace_accounts ht
  have ha : accounts ≤ 1 := by simp only [Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero] at hc; omega
  have hslots : accounts + (if false then 1 else 0) ≤ 1 := by simpa using ha
  have hg := ht.selected_cost_le cfg hlen (Prefix.initial (bs := bs) (start := i)) hslots hop hbase hunit
  rw [← ht.objCost_eq cfg.regularOpCost _ _ _ N hf] at hg
  simp only [ite_true, endFreeBound, endCap] at hg
  have hfixed := Nat.mul_le_mul_left 500000000000 ha
  exact ⟨batches, accounts, keys, ht, ha, by omega⟩

/-- Full selected parser cost, retaining exactly the complete mixed-growth term. -/
theorem selected_parser_cost_le (cfg : WasmConfig) (bs : List UInt8) (N : Nat)
    (a : WNear.AccountId) (rest : List UInt8) (hlen : bs.length ≤ 4194304)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    ∃ batches, (∀ seg ∈ batches, SegmentModel bs seg) ∧
      ledgerParserCost cfg (selectedBundledKeyCost cfg bs (wsLen bs + 1) 1)
        (selectedValueCost cfg bs (wsLen bs + 1) 1) (selectedIgnoreCost cfg bs (wsLen bs + 1) 1) bs rest N ≤
      (2215 + 470 * bs.length) * cfg.regularOpCost + 500000000000 + extraCost cfg 1 0 batches := by
  have hstart := SerdeNextKey.getElem_lt ho
  have hloop' : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N true none (bs.drop (wsLen bs + 1)) = some (some a, rest) := by
    simpa only [loopRes, ite_true] using hloop
  obtain ⟨batches, accounts, keys, ht, ha, hg⟩ := loop_selected_cost_le cfg bs N (wsLen bs + 1) a rest hlen (by omega) hloop' hop hbase hunit
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

/-- A scoped mixed-history reserve; no large-input growth claim is made. -/
theorem mixed_growth_small_budget (cfg : WasmConfig) (bs : List UInt8) (batches : Batches)
    (hlen : bs.length ≤ 10000) (hm : ∀ seg ∈ batches, SegmentModel bs seg)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) : extraCost cfg 1 0 batches ≤ 500000000000 := by
  have hfull : bs.length ≤ 4194304 := by omega
  obtain ⟨hv, _, hp⟩ := batches_bounds bs batches 0 hfull (by decide) hm
  have hpeak : peak 0 batches ≤ 10000 := by omega
  have hg := growth_v86 batches hv (by omega)
  have he := extraCost_budget cfg 1 0 batches hv
  have hgg := Nat.mul_le_mul hg hg
  have hwork : 1790 * growthCount 0 batches +
      (1 * growthCount 0 batches + growthCount 0 batches * growthCount 0 batches - growthCount 0 batches) * 320 +
      18 * (2 * peak 0 batches + 8) ≤ 538854 := by omega
  have hreg := Nat.mul_le_mul hwork hop
  have hlin := Nat.mul_le_mul hg hbase
  have hpages : (4 * peak 0 batches + 16 + 66066 * growthCount 0 batches) / 65536 ≤ 21 := by omega
  have hmem := Nat.mul_le_mul hunit hpages
  unfold budget at he
  omega

/-- Exact selected parsing is funded for every successful general object up to 10000 bytes. -/
theorem selected_parser_linear_small (cfg : WasmConfig) (bs : List UInt8) (N : Nat)
    (a : WNear.AccountId) (rest : List UInt8) (hlen : bs.length ≤ 10000)
    (ho : bs[wsLen bs]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none (bs.drop (wsLen bs + 1)) = some (some a, rest))
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) : SelectedParserLinearBudget cfg bs rest N := by
  have hfull : bs.length ≤ 4194304 := by omega
  obtain ⟨batches, hm, hc⟩ := selected_parser_cost_le cfg bs N a rest hfull ho hloop hop hbase hunit
  have hg := mixed_growth_small_budget cfg bs batches hlen hm hop hbase hunit
  unfold SelectedParserLinearBudget
  omega

end WNear.Binary.SerdeObjectMixedTrace
