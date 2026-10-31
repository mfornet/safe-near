import Bridge.Functions.ScratchMixedGrowth
import Bridge.Functions.SerdeBundledWork
import Bridge.Functions.SerdePrefixBounds
import Bridge.Functions.SerdePrefixSelectedValues

namespace WNear.Binary.SerdeObjectPrefix
open Wasm Wasm.Near
open SerdeRead (wsLen)

theorem account_growth_budget_le (cfg : WasmConfig) (F G N : Nat)
    (hF : F ≤ 43) (hG : G ≤ 21) (hN : N ≤ 64)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    ParseStrSuccess.growthBudget cfg F G N ≤ 400000000000 := by
  have hFG := Nat.mul_le_mul hF hG
  have hGG := Nat.mul_le_mul hG hG
  have hwork : 1790 * G + (F * G + G * G - G) * 320 + 36 * N + 144 ≤ 470118 := by omega
  have hreg := Nat.mul_le_mul hwork hop
  have hlin := Nat.mul_le_mul hG hbase
  have hpages : (4 * N + 16 + 66066 * G) / 65536 ≤ 21 := by omega
  have hmem := Nat.mul_le_mul hunit hpages
  unfold ParseStrSuccess.growthBudget
  split <;> omega

theorem account_owned_copy_budget_le (cfg : WasmConfig) (F : Nat) (c : UInt32)
    (hF : F ≤ 85) (hN : c.toNat ≤ 64)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    SerdeString.cost618 cfg F c ≤ 30000000000 := by
  have hp := ScratchMixedTrace.account_page c hN
  have hm : MemCpy.cost c.toNat ≤ 1158 := by unfold MemCpy.cost; split <;> omega
  have hf := Nat.mul_le_mul_left 320 hF
  have hwork : 100 + MemCpy.cost c.toNat + 240 + 15 + 15 + 320 * F + 330 + 610 ≤ 29668 := by omega
  have hreg := Nat.mul_le_mul hwork hop
  have hmem := Nat.mul_le_mul hunit hp
  simp only [SerdeString.cost618, SerdeString.costA, AllocWalk.cost310W, AllocWalk.walkCost, AllocWalk.wc]
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hreg ⊢
  omega

/-- The mixed growth count composes along retained capacities. -/
theorem mixed_growth_append (cap : UInt32) (pre post : ScratchMixedTrace.Batches) :
    ScratchMixedTrace.growthCount cap (pre ++ post) = ScratchMixedTrace.growthCount cap pre +
      ScratchMixedTrace.growthCount (ScratchMixedTrace.endCap cap pre) post := by
  induction pre generalizing cap with
  | nil => simp [ScratchMixedTrace.growthCount, ScratchMixedTrace.endCap]
  | cons seg pre ih => simp only [List.cons_append, ScratchMixedTrace.growthCount, ScratchMixedTrace.endCap, ih, Nat.add_assoc]

/-- Actual prefix and successful value models supply both allocator bounds used below. -/
theorem Bound.account_resources {bs : List UInt8} {start baseHL i hl F j : Nat}
    {cap : UInt32} {value : String} {rest : List UInt8}
    (hlen : bs.length ≤ 4194304)
    (hb : Bound bs start baseHL 1 false (.value "account_id") i hl F cap)
    (hm : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some value, rest)) :
    F ≤ 43 ∧ ScratchGrow.growthCount cap 0 (ParseStrSuccess.appendChunks (bs.drop (j + 1)) []) ≤ 21 := by
  obtain ⟨pre, hp, rfl, rfl, _, _⟩ := hb
  have hmodels : ∀ seg ∈ pre ++ [ScratchMixedTrace.Segment.append (ParseStrSuccess.appendChunks (bs.drop (j + 1)) [])],
      SerdeObjectMixedTrace.SegmentModel bs seg := by
    intro seg hs
    rcases List.mem_append.mp hs with hs | hs
    · exact hp.models seg hs
    · have he := List.mem_singleton.mp hs
      subst seg
      exact .string _ _ _ hm
  obtain ⟨hv, _, hpeak⟩ := SerdeObjectMixedTrace.batches_bounds bs _ 0 hlen (by decide) hmodels
  have hg := ScratchMixedTrace.growth_v86 _ hv (by omega)
  rw [mixed_growth_append] at hg
  simp only [ScratchMixedTrace.growthCount, ScratchMixedTrace.Segment.growthCount, Nat.add_zero] at hg
  rw [ScratchMixedTrace.endFreeBound_eq]
  omega

/-- One successful account value, including its scratch and owned-copy allocation.
The actual prefix must still supply the explicit free-list and growth bounds. -/
theorem account_value_charge_le (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs bytes rest : List UInt8) (i j : Nat)
    (hlen : bs.length < 2 ^ 24) (hj : j = i + wsLen (bs.drop i)) (hq : j < bs.length)
    (hok : ParseStr.strRun (bs.drop (j + 1)) [] = .ok bytes rest)
    (hu : Utf8.utf8Ok bytes = true) (hF : F ≤ 43) (hN : bytes.length ≤ 64)
    (hG : ScratchGrow.growthCount cap 0 (ParseStrSuccess.appendChunks (bs.drop (j + 1)) []) ≤ 21)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    SerdeValueReuse.valueCost cfg F cap bs bytes rest i j ≤
      (166 + 470 * (bs.length - rest.length - i)) * cfg.regularOpCost + 500000000000 := by
  have hv := SerdeValueReuse.valueCost_le cfg F cap bs bytes rest i j hq hok hu
  have hg := account_growth_budget_le cfg F _ bytes.length hF hG hN hop hbase hunit
  have hfree : ScratchGrow.endFreeBound F cap 0 (ParseStrSuccess.appendChunks (bs.drop (j + 1)) []) ≤ 85 := by
    rw [ScratchGrow.endFreeBound_eq]
    omega
  have h32 : (UInt32.ofNat bytes.length).toNat ≤ 64 := by simp; omega
  have hc := account_owned_copy_budget_le cfg _ (UInt32.ofNat bytes.length) hfree h32 hop hbase hunit
  have hsmall : ([] : List UInt8).length + (bs.drop (j + 1)).length < 2 ^ 27 := by simp; omega
  have hr := (ParseStrSuccess.costRun_growth_tight cfg F cap [] (bs.drop (j + 1)) bytes rest bs.length hok hsmall).1
  simp only [List.length_drop] at hr
  have hm : bs.length - rest.length - i = wsLen (bs.drop i) + 1 + ((bs.drop (j + 1)).length - rest.length) := by
    simp only [List.length_drop]
    omega
  have ha : AccountIdValid.cost554 bytes.length ≤ 3940 := by unfold AccountIdValid.cost554; omega
  have hwork : 400 + AccountIdValid.cost554 bytes.length + 910 + 96 * wsLen (bs.drop i) +
      470 * ((bs.drop (j + 1)).length - rest.length) ≤
      166 + 470 * (bs.length - rest.length - i) + 6000 := by omega
  have hw := Nat.mul_le_mul_right cfg.regularOpCost hwork
  have hextra := Nat.mul_le_mul_left 6000 hop
  unfold SerdeDeStrEsc.costCopied at hv
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] at hv hw hextra ⊢
  omega

/-- No hypothetical allocator bounds remain for an actual pending account value. -/
theorem Bound.account_value_charge {bs : List UInt8} {start baseHL i hl F j : Nat}
    {cap : UInt32} {a : WNear.AccountId} {rest : List UInt8}
    (cfg : WasmConfig) (hlen : bs.length ≤ 4194304)
    (hb : Bound bs start baseHL 1 false (.value "account_id") i hl F cap)
    (hj : j = i + wsLen (bs.drop i) + 1 + wsLen (bs.drop (i + wsLen (bs.drop i) + 1)))
    (hq : bs[j]? = some 0x22)
    (hm : NearInterface.Json.stringBody (bs.drop (j + 1)) [] = some (some a.val, rest))
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    SerdeValueReuse.valueCost cfg F cap bs a.val.toUTF8.toList rest (i + wsLen (bs.drop i) + 1) j ≤
      (166 + 470 * (bs.length - rest.length - (i + wsLen (bs.drop i) + 1))) * cfg.regularOpCost + 500000000000 := by
  obtain ⟨hF, hG⟩ := hb.account_resources hlen hm
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hm
  have hv := a.toNear.property
  change validAccountIdBytes a.val.toUTF8.toList = true at hv
  simp only [validAccountIdBytes, Bool.and_eq_true, decide_eq_true_eq] at hv
  have hs : a.val.toUTF8.toList.length ≤ 64 := by omega
  have hsmall : bs.length < 2 ^ 24 := by omega
  have hjl := SerdeNextKey.getElem_lt hq
  exact account_value_charge_le cfg F cap bs a.val.toUTF8.toList rest _ j hsmall hj hjl hok hu hF hs hG hop hbase hunit

/-- The same exact account charge selected by the full receipt has the concrete bound. -/
theorem selectedValueCost_account_bound (cfg : WasmConfig) (bs : List UInt8) (start v : Nat)
    (w : ValueWitness bs start v) (hlen : bs.length ≤ 4194304)
    (hop : cfg.regularOpCost ≤ 822756) (hbase : cfg.linearOpBaseCost ≤ 26328192)
    (hunit : cfg.linearOpUnitCost ≤ 822756) :
    selectedValueCost cfg bs start 1 v ≤
      (166 + 470 * (bs.length - w.rest.length - v)) * cfg.regularOpCost + 500000000000 := by
  obtain ⟨j, hj, hq, hs⟩ := SerdeStructObjValueState.account_model w.model
  have hb : Bound bs start 0 1 false (.value "account_id") w.cursor 0
      (ScratchMixedTrace.endFreeBound 1 0 w.history) (ScratchMixedTrace.endCap 0 w.history) :=
    ⟨w.history, w.prefixModel, rfl, rfl, le_refl _, Nat.zero_le _⟩
  have h := hb.account_value_charge cfg hlen (by simpa only [w.valueStart] using hj) hq hs hop hbase hunit
  rw [← w.valueStart] at h
  rw [hj] at h
  rwa [selectedValueCost_of_witness cfg bs start 1 v w] at h

end WNear.Binary.SerdeObjectPrefix
