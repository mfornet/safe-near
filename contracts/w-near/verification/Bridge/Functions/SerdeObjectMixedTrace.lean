import Bridge.Functions.ScratchMixedGrowth
import Bridge.Functions.SerdeObjectKeyCoverage
import Bridge.Functions.SerdeIgnRoom

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near
open NearInterface.Json
open WNear.Binary.ScratchMixedTrace

/-- Successful raw models identify every actual scratch segment. -/
inductive SegmentModel (bs : List UInt8) : Segment → Prop
  | string (q : Nat) (key : String) (rest : List UInt8)
      (h : stringBody (bs.drop q) [] = some (some key, rest)) :
      SegmentModel bs (.append (ParseStrSuccess.appendChunks (bs.drop q) []))
  | ignored (q : Nat) (rest : List UInt8) (ops : List Bool)
      (h : SerdeIgnMachineTrace.trace (bs.drop q) = some (rest, ops)) :
      SegmentModel bs (.frames ops)

theorem segment_bounds (bs : List UInt8) (seg : Segment) (cap : UInt32)
    (hlen : bs.length ≤ 4194304) (hcap : cap.toNat < 2 ^ 25) (hm : SegmentModel bs seg) :
    Segment.Valid cap seg ∧ (Segment.next cap seg).toNat < 2 ^ 25 ∧ Segment.peak cap seg ≤ bs.length := by
  cases hm with
  | string q key rest hs =>
    obtain ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hs
    have hv := ParseStrSuccess.appendChunks_valid cap [] (bs.drop q) key.toUTF8.toList rest
      hok (by simp) (by omega) (by simp only [List.length_nil, Nat.zero_add, List.length_drop]; omega)
    have hc := SerdeObjectState.parsed_capacity bs key.toUTF8.toList rest q cap (by omega) hcap hok
    have hp := SerdeDeStrEsc.strRun_size (bs.drop q) [] key.toUTF8.toList rest hok
    simp only [List.length_nil, Nat.zero_add, List.length_drop] at hp
    simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hv
    refine ⟨hv.1, hc, ?_⟩
    dsimp only [Segment.peak]
    omega
  | ignored q rest ops ht =>
    have hskip : WNear.IgnoreModel.vSkip (bs.drop q) = some rest := by
      rw [← SerdeIgnMachineTrace.erase_trace, ht]
      rfl
    obtain ⟨os, ho, hv, _, _, hp⟩ := SerdeIgnMachineTrace.trace_valid cap (by omega)
      (by simp only [List.length_drop]; omega) hskip
    have he : ops = os := (Prod.mk.inj (Option.some.inj (ht.symm.trans ho))).2
    subst os
    have hc := SerdeIgnExecution.trace_end_cap_v86 (bs.drop q) rest ops cap
      (by simp only [List.length_drop]; omega) hcap ht
    refine ⟨hv, hc, ?_⟩
    dsimp only [Segment.peak]
    simp only [List.length_drop] at hp
    omega

theorem batches_bounds (bs : List UInt8) (batches : Batches) (cap : UInt32)
    (hlen : bs.length ≤ 4194304) (hcap : cap.toNat < 2 ^ 25)
    (hm : ∀ seg ∈ batches, SegmentModel bs seg) :
    Valid cap batches ∧ (endCap cap batches).toNat < 2 ^ 25 ∧ peak cap batches ≤ bs.length := by
  induction batches generalizing cap with
  | nil => exact ⟨by dsimp only [Valid]; omega, hcap, by simp [peak]⟩
  | cons seg batches ih =>
    obtain ⟨hv, hc, hp⟩ := segment_bounds bs seg cap hlen hcap (hm seg (by simp))
    obtain ⟨hvs, hcs, hps⟩ := ih (Segment.next cap seg) hc (fun seg hs => hm seg (by simp [hs]))
    exact ⟨⟨by omega, hv, hvs⟩, hcs, max_le hp hps⟩

/-- One bound across all successful key/frame/account-string segments, without per-member resets. -/
theorem scratch_pages (bs : List UInt8) (batches : Batches) (hlen : bs.length ≤ 4194304)
    (hm : ∀ seg ∈ batches, SegmentModel bs seg) :
    65536 * pages 0 batches ≤ 18164618 := by
  obtain ⟨hv, _, hp⟩ := batches_bounds bs batches 0 hlen (by decide) hm
  exact pages_v86 batches hv (by omega)


open WNear.SerdeStructModel
open WNear.Binary.SerdeKeyEsc (KeySample)
open WNear.Binary.SerdeObjectCoverage (KeyWalk)

/-- One actual field/ignored reader and its scratch segment at the exact input endpoint. -/
inductive ValueSegment (bs : List UInt8) (key : String) (input : List UInt8) (e : Nat) : Segment → Prop
  | account (v j : Nat) (a : WNear.AccountId) (hk : key = "account_id")
      (hin : input = bs.drop v) (hj : j = v + SerdeRead.wsLen (bs.drop v))
      (hq : bs[j]? = some 0x22)
      (hv : valueAs WNear.account (bs.drop v) = some (a, bs.drop e))
      (hs : stringBody (bs.drop (j + 1)) [] = some (some a.val, bs.drop e)) :
      ValueSegment bs key input e (.append (ParseStrSuccess.appendChunks (bs.drop (j + 1)) []))
  | ignored (v : Nat) (ops : List Bool) (hk : key ≠ "account_id") (hin : input = bs.drop v)
      (ht : SerdeIgnMachineTrace.trace (bs.drop v) = some (bs.drop e, ops)) :
      ValueSegment bs key input e (.frames ops)

inductive CallTrace (bs : List UInt8) : Nat → Bool → List KeySample → Batches → Nat → Nat → Prop
  | done (i : Nat) (hb : bs[i + SerdeRead.wsLen (bs.drop i)]? = some 0x7D) :
      CallTrace bs i false [] [] (i + SerdeRead.wsLen (bs.drop i) + 1) 0
  | member (i q e stop : Nat) (first : Bool) (key : String) (r1 r2 : List UInt8)
      (keys : List KeySample) (value : Segment) (batches : Batches) (accounts : Nat)
      (hq : SerdeNextKey.keyQ first bs i = some q)
      (hs : stringBody (bs.drop q) [] = some (some key, r1))
      (hc : WNear.JsonFuel.colonAt r1 = some r2)
      (he : bs.length - r2.length ≤ e) (heb : e ≤ bs.length)
      (hv : ValueSegment bs key r2 e value)
      (tail : CallTrace bs e false keys batches stop accounts) :
      CallTrace bs i first ((q, key, r1) :: keys)
        (.append (ParseStrSuccess.appendChunks (bs.drop q) []) :: value :: batches) stop
        ((if key = "account_id" then 1 else 0) + accounts)

theorem expand_key_walk {bs : List UInt8} {i stop : Nat} {first : Bool} {keys : List KeySample}
    (hw : KeyWalk bs i first keys stop) : ∃ batches accounts, CallTrace bs i first keys batches stop accounts := by
  induction hw with
  | done i hb => exact ⟨[], 0, .done i hb⟩
  | member i q e stop first key r1 r2 keys hq hs hc hv he heb ht ih =>
    obtain ⟨batches, accounts, htail⟩ := ih
    have hr1 := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
    have hc' : WNear.JsonFuel.colonAt (bs.drop (bs.length - r1.length)) = some r2 := by rw [hr1]; exact hc
    have hr2 := SerdeObjectCoverage.colon_result hc'
    rcases hv with ⟨hk, a, hv⟩ | ⟨hk, hv⟩
    · rw [hr2] at hv
      obtain ⟨j, hj, hquote, hstr⟩ := SerdeStructObjValueState.account_model hv
      exact ⟨_, _, .member i q e stop first key r1 r2 keys _ batches accounts hq hs hc he heb
        (.account _ j a hk hr2 hj hquote hv hstr) htail⟩
    · have hskip : WNear.IgnoreModel.vSkip (bs.drop (bs.length - r1.length + SerdeRead.wsLen (bs.drop (bs.length - r1.length)) + 1)) = some (bs.drop e) := by
        rw [← hr2]
        simpa [SerdeIgnObject.ignored] using hv
      obtain ⟨ops, htrace, _, _, _, _⟩ := SerdeIgnMachineTrace.trace_some hskip
      exact ⟨_, _, .member i q e stop first key r1 r2 keys _ batches accounts hq hs hc he heb
        (.ignored _ ops hk hr2 htrace) htail⟩

theorem value_segment_model {bs : List UInt8} {key : String} {input : List UInt8} {e : Nat} {seg : Segment}
    (hv : ValueSegment bs key input e seg) : SegmentModel bs seg := by
  cases hv with
  | account v j a hk hin hj hq hv hs => exact .string (j + 1) a.val (bs.drop e) hs
  | ignored v ops hk hin ht => exact .ignored v (bs.drop e) ops ht

theorem call_trace_models {bs : List UInt8} {i stop accounts : Nat} {first : Bool}
    {keys : List KeySample} {batches : Batches} (ht : CallTrace bs i first keys batches stop accounts) :
    ∀ seg ∈ batches, SegmentModel bs seg := by
  induction ht with
  | done i hb => simp
  | member i q e stop first key r1 r2 keys value batches accounts hq hs hc he heb hv ht ih =>
    intro seg hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact .string q key r1 hs
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact value_segment_model hv
    · exact ih seg hmem

/-- Every successful object-loop model supplies a complete ordered scratch trace and its global page bound. -/
theorem loop_scratch_pages (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8)
    (hlen : bs.length ≤ 4194304) (hi : i ≤ bs.length)
    (hloop : WNear.SerdeStructLoop.loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys batches accounts, CallTrace bs i first keys batches (bs.length - rest.length) accounts ∧
      65536 * pages 0 batches ≤ 18164618 := by
  obtain ⟨keys, hw⟩ := SerdeObjectCoverage.loop_keys bs N first i seen a rest hi hloop
  obtain ⟨batches, accounts, ht⟩ := expand_key_walk hw
  exact ⟨keys, batches, accounts, ht, scratch_pages bs batches hlen (call_trace_models ht)⟩


def accountCount : List KeySample → Nat
  | [] => 0
  | key :: keys => (if key.2.1 = "account_id" then 1 else 0) + accountCount keys

open WNear.SerdeStructLoop
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeObjectCoverage (loop_keys keyQ_strict)

theorem loop_keys_account (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8)
    (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys, KeyWalk bs i first keys (bs.length - rest.length) ∧ accountCount keys + (if seen.isSome then 1 else 0) ≤ 1 := by
  induction N generalizing first i seen with
  | zero =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_, by cases seen <;> simp [accountCount]⟩
      have he : bs.length - rest.length = i + wsLen (bs.drop i) + 1 := by rw [hr, List.length_drop]; omega
      rw [he]
      exact .done i hb
    · obtain ⟨n, _, _, _, hn, _⟩ := loop_member "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      omega
  | succ N ih =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_, by cases seen <;> simp [accountCount]⟩
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
        obtain ⟨keys, hkeys, hcount⟩ := ih false (bs.length - r3.length) (some a') hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inl ⟨hk, a', by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys, by simp only [accountCount, hk, ite_true, Option.isSome_none, Bool.false_eq_true, ite_false]; simp only [Option.isSome_some, ite_true] at hcount; omega⟩
      · have hv' : WNear.IgnoreModel.vSkip r2 = some r3 := by simpa [SerdeIgnObject.ignored] using hv
        have h3 := IgnoreShallow.vSkip_suf hv'
        have hsuf3 := h3.trans hsuf2
        have hd3 := JsonSuffix.drop_suf hsuf3
        have hie : bs.length - r3.length ≤ bs.length := by omega
        rw [← hd3] at ht
        obtain ⟨keys, hkeys, hcount⟩ := ih false (bs.length - r3.length) seen hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inr ⟨hk, by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys, by simpa only [accountCount, hk, ite_false, Nat.zero_add] using hcount⟩


theorem call_trace_accounts {bs : List UInt8} {i stop accounts : Nat} {first : Bool}
    {keys : List KeySample} {batches : Batches} (ht : CallTrace bs i first keys batches stop accounts) :
    accounts = accountCount keys := by
  induction ht with
  | done i hb => rfl
  | member i q e stop first key r1 r2 keys value batches accounts hq hs hc he heb hv ht ih =>
    simpa only [accountCount, ih]

theorem loop_total_pages (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8)
    (hlen : bs.length ≤ 4194304) (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys batches accounts, CallTrace bs i first keys batches (bs.length - rest.length) accounts ∧
      accounts ≤ 1 ∧ 65536 * pages 0 batches + 65536 * accounts ≤ 18230154 := by
  obtain ⟨keys, hw, hc⟩ := loop_keys_account bs N first i seen a rest hi hloop
  obtain ⟨batches, accounts, ht⟩ := expand_key_walk hw
  have he := call_trace_accounts ht
  have hp := scratch_pages bs batches hlen (call_trace_models ht)
  exact ⟨keys, batches, accounts, ht, by omega, by omega⟩


theorem account_id_page (a : WNear.AccountId) :
    (AllocNewCell.cellPages (AllocAlloc.wordsOf (UInt32.ofNat a.val.toUTF8.toList.length)) 1).toNat ≤ 1 := by
  have hsize := a.utf8ByteSize_le
  change a.val.utf8ByteSize ≤ 64 at hsize
  have hlen : a.val.toUTF8.toList.length ≤ 64 := by rw [Wasm.ByteEncoding.string_utf8_length]; exact hsize
  apply account_page
  change a.val.toUTF8.toList.length % 4294967296 ≤ 64
  omega



end WNear.Binary.SerdeObjectMixedTrace
