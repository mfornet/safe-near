import Bridge.Functions.SerdeObjectPrefix

namespace WNear.Binary.SerdeObjectMixedTrace
open Wasm Wasm.Near NearInterface.Json
open WNear.JsonFuel
open WNear.Binary.ScratchMixedTrace
open WNear.Binary.SerdeObjectPrefix
open WNear.Binary.SerdeStructObjPhase (Phase)
open WNear.Binary.SerdeRead (wsLen)

theorem colon_at_byte {bs : List UInt8} {i : Nat} {rest : List UInt8}
    (hc : colonAt (bs.drop i) = some rest) : bs[i + wsLen (bs.drop i)]? = some 0x3A := by
  unfold colonAt at hc
  split at hc
  · rename_i r hs
    exact (WNear.SerdeStructLoop.skip_drop_cons hs).1
  · simp at hc

/-- Every complete actual call trace extends its retained prefix through the closing brace. -/
theorem CallTrace.prefix_end {bs : List UInt8} {start i stop accounts : Nat} {first : Bool}
    {keys : List SerdeKeyEsc.KeySample} {batches pre : Batches} {saved : Bool}
    (h : CallTrace bs i first keys batches stop accounts)
    (hp : Prefix bs start (.member first) i pre saved)
    (hslots : accounts + (if saved then 1 else 0) ≤ 1) :
    ∃ savedFinal, Prefix bs start .done stop (pre ++ batches) savedFinal := by
  induction h generalizing pre saved with
  | done i hb =>
    exact ⟨saved, by simpa using Prefix.close hp hb⟩
  | member i q e stop first key r1 r2 keys value batches accounts hq hs hc he heb hv ht ih =>
    have hr1 := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
    have hc' : colonAt (bs.drop (bs.length - r1.length)) = some r2 := by rw [hr1]; exact hc
    have hcolon := colon_at_byte hc'
    have hr2 := SerdeObjectCoverage.colon_result hc'
    have hvle := SerdeNextKey.getElem_lt hcolon
    have heValue : bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1 ≤ e := by
      rw [hr2] at he
      simp only [List.length_drop] at he
      omega
    have hdup : key = "account_id" → saved = false := by
      intro hk
      cases saved <;> simp_all
    have hslotsTail : accounts + (if saved || key == "account_id" then 1 else 0) ≤ 1 := by
      by_cases hk : key = "account_id"
      · have hsave := hdup hk
        simp only [hsave, hk, ite_true, Bool.false_or, beq_self_eq_true] at hslots ⊢
        omega
      · have hkfalse : (key == "account_id") = false := by simp [hk]
        simpa only [if_neg hk, Nat.zero_add, hkfalse, Bool.or_false] using hslots
    rw [hr2] at hv
    have hkprefix := Prefix.key hp hq hs
    have hvprefix := Prefix.value (e := e) (seg := value) hkprefix hdup hcolon heValue heb hv
    obtain ⟨savedFinal, hfinal⟩ := ih hvprefix hslotsTail
    exact ⟨savedFinal, by simpa [List.append_assoc] using hfinal⟩

theorem keyQ_offset {bs : List UInt8} {first : Bool} {i q : Nat}
    (hq : SerdeNextKey.keyQ first bs i = some q) :
    q = i + SerdeNextKey.keyWs first bs i + (if first then 1 else 2) := by
  cases first <;> simp only [SerdeNextKey.keyQ, SerdeNextKey.keyWs, Bool.false_eq_true, ite_false, ite_true] at hq ⊢
  · split at hq
    · split at hq <;> simp_all <;> omega
    · simp at hq
  · split at hq <;> simp_all <;> omega

/-- The actual key, colon, value and whitespace slices exactly partition a member's input. -/
theorem member_consumed_exact {bs : List UInt8} {first : Bool} {i q e : Nat}
    {key : String} {r1 r2 : List UInt8}
    (hq : SerdeNextKey.keyQ first bs i = some q)
    (hs : stringBody (bs.drop q) [] = some (some key, r1))
    (hc : colonAt r1 = some r2) (he : bs.length - r2.length ≤ e) (heb : e ≤ bs.length) :
    ((bs.drop q).length - r1.length) +
      (e - (bs.length - r1.length + wsLen (bs.drop (bs.length - r1.length)) + 1)) +
      SerdeNextKey.keyWs first bs i + wsLen (bs.drop (bs.length - r1.length)) +
      (if first then 2 else 3) = e - i := by
  have hoff := keyQ_offset hq
  have hql := SerdeStructObj.keyQ_le hq
  have hslen := (JsonSuffix.stringBody_suf' hs).length_le
  have hr1 := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
  have hc' : colonAt (bs.drop (bs.length - r1.length)) = some r2 := by rw [hr1]; exact hc
  have hcolon := colon_at_byte hc'
  have hv := SerdeNextKey.getElem_lt hcolon
  have hr2 := SerdeObjectCoverage.colon_result hc'
  rw [hr2] at he
  simp only [List.length_drop] at hslen he ⊢
  cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true] at hoff ⊢ <;> omega

def valueEnd (bs : List UInt8) (key : String) (input : List UInt8) : Option Nat :=
  if key = "account_id" then (WNear.SerdeStructModel.valueAs WNear.account input).map (fun p => bs.length - p.2.length)
  else (SerdeIgnObject.ignored input).map (fun p => bs.length - p.2.length)

theorem ValueSegment.end_eq {bs : List UInt8} {key : String} {input : List UInt8} {e : Nat} {seg : Segment}
    (h : ValueSegment bs key input e seg) (he : e ≤ bs.length) : valueEnd bs key input = some e := by
  cases h with
  | account v j a hk hin hj hq hm hs =>
    subst key
    simp only [valueEnd, ite_true, hin, hm, Option.map_some, List.length_drop]
    congr 1
    omega
  | ignored v ops hk hin ht =>
    have hskip : WNear.IgnoreModel.vSkip (bs.drop v) = some (bs.drop e) := by
      rw [← SerdeIgnMachineTrace.erase_trace, ht]
      rfl
    simp only [valueEnd, if_neg hk, hin, SerdeIgnObject.ignored, hskip, Option.map_some, List.length_drop]
    congr 1
    omega

/-- Exact consumed-byte work following the actual successful key/value path, including whitespace and punctuation. -/
def inputWork (bs : List UInt8) : Nat → Bool → List SerdeKeyEsc.KeySample → Nat
  | i, _, [] => wsLen (bs.drop i) + 1
  | i, first, (q, key, rest) :: keys =>
    let j := bs.length - rest.length
    let v := j + wsLen (bs.drop j) + 1
    match colonAt rest with
    | none => 0
    | some input =>
      match valueEnd bs key input with
      | none => 0
      | some e =>
        ((bs.drop q).length - rest.length) + (e - v) + SerdeNextKey.keyWs first bs i +
          wsLen (bs.drop j) + (if first then 2 else 3) + inputWork bs e false keys

/-- The complete call trace's key, value, whitespace and structural slices partition its consumed input. -/
theorem CallTrace.input_work {bs : List UInt8} {i stop accounts : Nat} {first : Bool}
    {keys : List SerdeKeyEsc.KeySample} {batches : Batches}
    (h : CallTrace bs i first keys batches stop accounts) :
    i ≤ stop ∧ inputWork bs i first keys = stop - i := by
  induction h with
  | done i hb =>
    simp only [inputWork]
    omega
  | member i q e stop first key r1 r2 keys value batches accounts hq hs hc he heb hv ht ih =>
    have hie := (SerdeObjectCoverage.key_charge hq hs hc he).1
    refine ⟨by omega, ?_⟩
    have hvEnd := hv.end_eq heb
    simp only [inputWork, hc, hvEnd]
    rw [member_consumed_exact hq hs hc he heb, ih.2]
    omega

/-- Every successful initial object loop supplies a complete retained prefix and exact consumed-byte partition. -/
theorem loop_prefix_input (bs : List UInt8) (N i : Nat) (a : WNear.AccountId) (rest : List UInt8)
    (hlen : bs.length ≤ 4194304) (hi : i ≤ bs.length)
    (hloop : WNear.SerdeStructLoop.loopRes "account_id" (WNear.SerdeStructModel.valueAs WNear.account)
      SerdeIgnObject.ignored N true none (bs.drop i) = some (some a, rest)) :
    ∃ keys batches accounts saved, CallTrace bs i true keys batches (bs.length - rest.length) accounts ∧
      accounts ≤ 1 ∧ Prefix bs i .done (bs.length - rest.length) batches saved ∧
      inputWork bs i true keys = bs.length - rest.length - i ∧
      65536 * pages 0 batches + 65536 * accounts ≤ 18230154 := by
  obtain ⟨keys, batches, accounts, ht, ha, hp⟩ := loop_total_pages bs N true i none a rest hlen hi hloop
  have hslots : accounts + (if false then 1 else 0) ≤ 1 := by simpa using ha
  obtain ⟨saved, hend⟩ := ht.prefix_end (Prefix.initial (bs := bs) (start := i)) hslots
  exact ⟨keys, batches, accounts, saved, ht, ha, by simpa using hend, ht.input_work.2, hp⟩

end WNear.Binary.SerdeObjectMixedTrace
