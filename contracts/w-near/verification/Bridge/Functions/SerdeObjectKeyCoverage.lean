import Bridge.Functions.SerdeIgnObject
import Bridge.Functions.SerdeKeyArgumentGas

namespace WNear.Binary.SerdeObjectCoverage
open Wasm Wasm.Near
open NearInterface.Json WNear.JsonFuel WNear.SerdeStructModel
open WNear.SerdeStructLoop
open WNear.Binary.SerdeRead (wsLen)
open WNear.Binary.SerdeNextKey (keyQ)
open WNear.Binary.SerdeKeyEsc (KeySample consumed)

/-- The actual ordered key/cursor path, retaining the colon and value endpoint. -/
inductive KeyWalk (bs : List UInt8) : Nat → Bool → List KeySample → Nat → Prop
  | done (i : Nat) (hb : bs[i + wsLen (bs.drop i)]? = some 0x7D) :
      KeyWalk bs i false [] (i + wsLen (bs.drop i) + 1)
  | member (i q e stop : Nat) (first : Bool) (k : String) (r1 r2 : List UInt8) (keys : List KeySample)
      (hq : keyQ first bs i = some q)
      (hs : stringBody (bs.drop q) [] = some (some k, r1))
      (hc : colonAt r1 = some r2)
      (hv : (k = "account_id" ∧ ∃ a, valueAs WNear.account r2 = some (a, bs.drop e)) ∨
        (k ≠ "account_id" ∧ SerdeIgnObject.ignored r2 = some ((), bs.drop e)))
      (he : bs.length - r2.length ≤ e) (heb : e ≤ bs.length)
      (tail : KeyWalk bs e false keys stop) :
      KeyWalk bs i first ((q, k, r1) :: keys) stop

theorem keyQ_strict {first : Bool} {bs : List UInt8} {i q : Nat}
    (hq : keyQ first bs i = some q) : i < q := by
  unfold keyQ at hq
  split at hq
  · split at hq <;> simp_all <;> omega
  · split at hq
    · split at hq <;> simp_all <;> omega
    · simp at hq

theorem key_charge {first : Bool} {bs : List UInt8} {i q e : Nat} {k : String} {r1 r2 : List UInt8}
    (hq : keyQ first bs i = some q) (hs : stringBody (bs.drop q) [] = some (some k, r1))
    (hc : colonAt r1 = some r2) (he : bs.length - r2.length ≤ e) :
    i ≤ e ∧ (bs.drop q).length - r1.length + 2 ≤ e - i := by
  have hq0 := keyQ_strict hq
  have hq1 := SerdeStructObj.keyQ_le hq
  have h1 := (JsonSuffix.stringBody_suf' hs).length_le
  have h2 := WNear.SerdeStructModel.colonAt_len hc
  simp only [List.length_drop] at h1 ⊢
  omega

theorem key_walk_coverage {bs : List UInt8} {i stop : Nat} {first : Bool} {keys : List KeySample}
    (h : KeyWalk bs i first keys stop) :
    i ≤ stop ∧ consumed bs keys + 2 * keys.length ≤ stop - i := by
  induction h with
  | done i hb => simp [consumed]; omega
  | member i q e stop first k r1 r2 keys hq hs hc hv he heb ht ih =>
    have hc := key_charge hq hs hc he
    simp only [consumed, List.length_cons]
    exact ⟨by omega, by omega⟩

theorem key_walk_models {bs : List UInt8} {i stop : Nat} {first : Bool} {keys : List KeySample}
    (h : KeyWalk bs i first keys stop) :
    ∀ sample ∈ keys, stringBody (bs.drop sample.1) [] = some (some sample.2.1, sample.2.2) := by
  induction h with
  | done i hb => simp
  | member i q e stop first k r1 r2 keys hq hs hc hv he heb ht ih =>
    intro sample hmem
    rcases List.mem_cons.mp hmem with rfl | hmem
    · exact hs
    · exact ih sample hmem

/-- Every successful full object-loop model produces a disjoint key path. -/
theorem loop_keys (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8)
    (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys, KeyWalk bs i first keys (bs.length - rest.length) := by
  induction N generalizing first i seen with
  | zero =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_⟩
      have he : bs.length - rest.length = i + wsLen (bs.drop i) + 1 := by rw [hr, List.length_drop]; omega
      rw [he]
      exact .done i hb
    · obtain ⟨n, _, _, _, hn, _⟩ := loop_member "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      omega
  | succ N ih =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_⟩
      have he : bs.length - rest.length = i + wsLen (bs.drop i) + 1 := by rw [hr, List.length_drop]; omega
      rw [he]
      exact .done i hb
    · obtain ⟨n, q, k, r1, hn, hq, hs, _, r2, hc, hv⟩ :=
        loop_member "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hn' : n = N := by omega
      subst n
      have hsuf1 := (JsonSuffix.stringBody_suf' hs).trans (List.drop_suffix q bs)
      have hsuf2 := (JsonSuffix.colonAt_suf hc).trans hsuf1
      rcases hv with ⟨hk, a', r3, hv, ht⟩ | ⟨hk, r3, hv, ht⟩
      · have h3 := JsonSuffix.valueAs_suf WNear.account hv
        have hsuf3 := h3.trans hsuf2
        have hd3 := JsonSuffix.drop_suf hsuf3
        have hie : bs.length - r3.length ≤ bs.length := by omega
        rw [← hd3] at ht
        obtain ⟨keys, hkeys⟩ := ih false (bs.length - r3.length) (some a') hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inl ⟨hk, a', by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys⟩
      · have hv' : WNear.IgnoreModel.vSkip r2 = some r3 := by simpa [SerdeIgnObject.ignored] using hv
        have h3 := IgnoreShallow.vSkip_suf hv'
        have hsuf3 := h3.trans hsuf2
        have hd3 := JsonSuffix.drop_suf hsuf3
        have hie : bs.length - r3.length ≤ bs.length := by omega
        rw [← hd3] at ht
        obtain ⟨keys, hkeys⟩ := ih false (bs.length - r3.length) seen hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inr ⟨hk, by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys⟩

/-- The actual accepted loop keys instantiate the existing original-allowance key budget. -/
theorem loop_key_argument_budget (cfg : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 cfg)
    (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8)
    (hlen : bs.length ≤ 4194304) (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys, KeyWalk bs i first keys (bs.length - rest.length) ∧
      (∀ sample ∈ keys, stringBody (bs.drop sample.1) [] = some (some sample.2.1, sample.2.2)) ∧
      consumed bs keys + 2 * keys.length ≤ bs.length - rest.length - i ∧
      SerdeKeyEsc.seriesCost cfg.wasm 1 0 bs keys ≤
        200000000000 + WNear.argumentByteGas * (consumed bs keys + 2 * keys.length) ∧
      SerdeKeyEsc.seriesCost cfg.wasm 1 0 bs keys ≤
        200000000000 + WNear.argumentByteGas * (bs.length - rest.length - i) := by
  obtain ⟨keys, hw⟩ := loop_keys bs N first i seen a rest hi hloop
  have hm := key_walk_models hw
  have hcov := (key_walk_coverage hw).2
  have hgas := SerdeKeyEsc.seriesCost_argument_gas cfg hc bs keys hlen hm
  have hmono := Nat.mul_le_mul_left WNear.argumentByteGas hcov
  exact ⟨keys, hw, hm, hcov, hgas, by omega⟩

/-- The same key coverage is available at the complete object's real opening cursor. -/
theorem object_keys (bs : List UInt8) (i N : Nat) (a : WNear.AccountId) (rest : List UInt8)
    (hb : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rest)) :
    ∃ keys, KeyWalk bs (i + wsLen (bs.drop i) + 1) true keys (bs.length - rest.length) := by
  apply loop_keys bs N true (i + wsLen (bs.drop i) + 1) none a rest
  · have hh := SerdeNextKey.getElem_lt hb
    omega
  · simpa only [loopRes, ite_true] using hloop


theorem loop_keys_fuel (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8)
    (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys, KeyWalk bs i first keys (bs.length - rest.length) ∧ keys.length ≤ N := by
  induction N generalizing first i seen with
  | zero =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_, by simp⟩
      have he : bs.length - rest.length = i + wsLen (bs.drop i) + 1 := by rw [hr, List.length_drop]; omega
      rw [he]
      exact .done i hb
    · obtain ⟨n, _, _, _, hn, _⟩ := loop_member "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      omega
  | succ N ih =>
    by_cases hb : bs[i + wsLen (bs.drop i)]? = some 0x7D
    · obtain ⟨rfl, _, hr⟩ := loop_end "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hj := SerdeNextKey.getElem_lt hb
      refine ⟨[], ?_, by simp⟩
      have he : bs.length - rest.length = i + wsLen (bs.drop i) + 1 := by rw [hr, List.length_drop]; omega
      rw [he]
      exact .done i hb
    · obtain ⟨n, q, k, r1, hn, hq, hs, _, r2, hc, hv⟩ :=
        loop_member "account_id" (valueAs WNear.account) SerdeIgnObject.ignored hloop hb
      have hn' : n = N := by omega
      subst n
      have hsuf1 := (JsonSuffix.stringBody_suf' hs).trans (List.drop_suffix q bs)
      have hsuf2 := (JsonSuffix.colonAt_suf hc).trans hsuf1
      rcases hv with ⟨hk, a', r3, hv, ht⟩ | ⟨hk, r3, hv, ht⟩
      · have h3 := JsonSuffix.valueAs_suf WNear.account hv
        have hsuf3 := h3.trans hsuf2
        have hd3 := JsonSuffix.drop_suf hsuf3
        have hie : bs.length - r3.length ≤ bs.length := by omega
        rw [← hd3] at ht
        obtain ⟨keys, hkeys, hcount⟩ := ih false (bs.length - r3.length) (some a') hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inl ⟨hk, a', by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys, by simp only [List.length_cons]; omega⟩
      · have hv' : WNear.IgnoreModel.vSkip r2 = some r3 := by simpa [SerdeIgnObject.ignored] using hv
        have h3 := IgnoreShallow.vSkip_suf hv'
        have hsuf3 := h3.trans hsuf2
        have hd3 := JsonSuffix.drop_suf hsuf3
        have hie : bs.length - r3.length ≤ bs.length := by omega
        rw [← hd3] at ht
        obtain ⟨keys, hkeys, hcount⟩ := ih false (bs.length - r3.length) seen hie ht
        exact ⟨(q, k, r1) :: keys, .member i q _ _ first k r1 r2 keys hq hs hc
          (Or.inr ⟨hk, by simpa only [hd3] using hv⟩) (by have := h3.length_le; omega) hie hkeys, by simp only [List.length_cons]; omega⟩


def keyCharge (K : Nat → Nat) : List KeySample → Nat
  | [] => 0
  | sample :: keys => K sample.1 + keyCharge K keys

theorem keyQ_not_end {first : Bool} {bs : List UInt8} {i q : Nat}
    (hq : keyQ first bs i = some q) : bs[i + wsLen (bs.drop i)]? ≠ some 0x7D := by
  intro hb
  cases first <;> simp [keyQ, hb] at hq

theorem colon_result {bs : List UInt8} {i : Nat} {rest : List UInt8}
    (hc : colonAt (bs.drop i) = some rest) : rest = bs.drop (i + wsLen (bs.drop i) + 1) := by
  unfold colonAt at hc
  split at hc
  · rename_i r hs
    have he := Option.some.inj hc
    subst r
    exact (skip_drop_cons hs).2
  · simp at hc

/-- Exact separation of the actual key allowance calls from the other object-loop charges. -/
theorem objCost_key_component (c : Nat) (K K169 K81 : Nat → Nat) (bs : List UInt8)
    (i stop N : Nat) (first : Bool) (keys : List KeySample)
    (hw : KeyWalk bs i first keys stop) (hn : keys.length ≤ N) :
    SerdeStructObj.objCost c K K169 K81 (valueAs WNear.account) SerdeIgnObject.ignored bs N first i =
      keyCharge K keys +
        SerdeStructObj.objCost c (fun _ => 0) K169 K81 (valueAs WNear.account) SerdeIgnObject.ignored bs N first i := by
  induction hw generalizing N with
  | done i hb =>
    rw [SerdeStructObj.objCost_end c K K169 K81 _ _ bs hb,
      SerdeStructObj.objCost_end c (fun _ => 0) K169 K81 _ _ bs hb]
    simp only [keyCharge, Nat.zero_add]
  | member i q e stop first k r1 r2 keys hq hs hc hv he heb ht ih =>
    have hb := keyQ_not_end hq
    have hr1 := JsonSuffix.drop_suf' (JsonSuffix.stringBody_suf' hs)
    have hc' : colonAt (bs.drop (bs.length - r1.length)) = some r2 := by rw [hr1]; exact hc
    have hr2 := colon_result hc'
    have hrec : bs.length - (bs.drop e).length = e := by simp only [List.length_drop]; omega
    cases N with
    | zero => simp only [List.length_cons] at hn; omega
    | succ N =>
      have htail := ih N (by simp only [List.length_cons] at hn; omega)
      rcases hv with ⟨hk, a, hd⟩ | ⟨hk, hd⟩
      · rw [hr2] at hd
        rw [SerdeStructObj.objCost_field c K K169 K81 _ _ bs hb hq hs hk hd,
          SerdeStructObj.objCost_field c (fun _ => 0) K169 K81 _ _ bs hb hq hs hk hd]
        simp only [hrec, keyCharge]
        omega
      · rw [hr2] at hd
        rw [SerdeStructObj.objCost_ign c K K169 K81 _ _ bs hb hq hs hk hd,
          SerdeStructObj.objCost_ign c (fun _ => 0) K169 K81 _ _ bs hb hq hs hk hd]
        simp only [hrec, keyCharge]
        omega


/-- The successful model supplies the exact key-charge component of its real cost recurrence. -/
theorem loop_keys_cost (c : Nat) (K K169 K81 : Nat → Nat) (bs : List UInt8) (N : Nat) (first : Bool) (i : Nat)
    (seen : Option WNear.AccountId) (a : WNear.AccountId) (rest : List UInt8) (hi : i ≤ bs.length)
    (hloop : loopRes "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N first seen (bs.drop i) = some (some a, rest)) :
    ∃ keys, KeyWalk bs i first keys (bs.length - rest.length) ∧ keys.length ≤ N ∧
      (∀ sample ∈ keys, stringBody (bs.drop sample.1) [] = some (some sample.2.1, sample.2.2)) ∧
      consumed bs keys + 2 * keys.length ≤ bs.length - rest.length - i ∧
      SerdeStructObj.objCost c K K169 K81 (valueAs WNear.account) SerdeIgnObject.ignored bs N first i =
        keyCharge K keys + SerdeStructObj.objCost c (fun _ => 0) K169 K81 (valueAs WNear.account) SerdeIgnObject.ignored bs N first i := by
  obtain ⟨keys, hw, hn⟩ := loop_keys_fuel bs N first i seen a rest hi hloop
  exact ⟨keys, hw, hn, key_walk_models hw, (key_walk_coverage hw).2,
    objCost_key_component c K K169 K81 bs i _ N first keys hw hn⟩

/-- Exact key/residual decomposition of the complete deployed object-cost interface. -/
theorem object_key_cost (cfg : WasmConfig) (K K169 K81 : Nat → Nat) (bs : List UInt8) (i N : Nat)
    (a : WNear.AccountId) (rest : List UInt8) (hb : bs[i + wsLen (bs.drop i)]? = some 0x7B)
    (hloop : objLoop "account_id" (valueAs WNear.account) SerdeIgnObject.ignored N none
      (bs.drop (i + wsLen (bs.drop i) + 1)) = some (some a, rest)) :
    ∃ keys, KeyWalk bs (i + wsLen (bs.drop i) + 1) true keys (bs.length - rest.length) ∧
      (∀ sample ∈ keys, stringBody (bs.drop sample.1) [] = some (some sample.2.1, sample.2.2)) ∧
      consumed bs keys + 2 * keys.length ≤ bs.length - rest.length - (i + wsLen (bs.drop i) + 1) ∧
      SerdeStructObj.costObj cfg K K169 K81 (valueAs WNear.account) SerdeIgnObject.ignored bs N i =
        keyCharge K keys + SerdeStructObj.costObj cfg (fun _ => 0) K169 K81 (valueAs WNear.account) SerdeIgnObject.ignored bs N i := by
  have hi := SerdeNextKey.getElem_lt hb
  obtain ⟨keys, hw, _, hm, hcover, he⟩ := loop_keys_cost cfg.regularOpCost K K169 K81 bs N true
    (i + wsLen (bs.drop i) + 1) none a rest (by omega) (by simpa only [loopRes, ite_true] using hloop)
  refine ⟨keys, hw, hm, hcover, ?_⟩
  unfold SerdeStructObj.costObj
  omega


end WNear.Binary.SerdeObjectCoverage
