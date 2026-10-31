import Bridge.Functions.SerdeKeyEsc
import Bridge.Functions.ScratchReuseTrace

/-! Reusable parser growth charges and checked accepted-input domain bounds.
General parser instances and the pinned protocol ceiling remain separate obligations. -/

namespace WNear.Binary.SerdeKeyEsc
open Wasm Wasm.Near
open WNear.Binary

abbrev KeySample := Nat × String × List UInt8

def keyBatches (bs : List UInt8) (keys : List KeySample) : ScratchReuseTrace.Batches :=
  keys.map (fun k => ParseStrSuccess.appendChunks (bs.drop k.1) [])

def seriesCost (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs : List UInt8) : List KeySample → Nat
  | [] => 0
  | k :: keys => tracedCost cfg F cap bs k.1 +
      seriesCost cfg (ScratchGrow.endFreeBound F cap 0 (ParseStrSuccess.appendChunks (bs.drop k.1) []))
        (ScratchReuseTrace.next cap (ParseStrSuccess.appendChunks (bs.drop k.1) [])) bs keys

def seriesWork (bs : List UInt8) : List KeySample → Nat
  | [] => 0
  | k :: keys => 500 + 433 * ((bs.drop k.1).length - k.2.2.length) + seriesWork bs keys

theorem tracedCost_growth (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs : List UInt8) (k : KeySample) (hlen : bs.length < 2 ^ 24)
    (hmodel : NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    tracedCost cfg F cap bs k.1 ≤
      (500 + 433 * ((bs.drop k.1).length - k.2.2.length)) * cfg.regularOpCost +
        ScratchGrow.extraCost cfg F cap 0 (ParseStrSuccess.appendChunks (bs.drop k.1) []) := by
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  have hsmall : ([] : List UInt8).length + (bs.drop k.1).length < 2 ^ 27 := by simp; omega
  have hb := (ParseStrSuccess.costRun_growth_sharp cfg F cap [] (bs.drop k.1) k.2.1.toUTF8.toList k.2.2 bs.length hok hsmall).2
  simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl, Nat.mul_zero, Nat.add_zero] at hb
  unfold tracedCost
  simp only [Nat.add_mul] at hb ⊢
  omega

/-- Successive keys retain the same capacity and evolving free-list bound between clears. -/
theorem seriesCost_growth (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs : List UInt8)
    (keys : List KeySample) (hlen : bs.length < 2 ^ 24)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    seriesCost cfg F cap bs keys ≤ seriesWork bs keys * cfg.regularOpCost +
      ScratchReuseTrace.extraCost cfg F cap (keyBatches bs keys) := by
  induction keys generalizing F cap with
  | nil => simp [seriesCost, seriesWork, ScratchReuseTrace.extraCost, keyBatches]
  | cons k keys ih =>
    have h1 := tracedCost_growth cfg F cap bs k hlen (hmodels k (by simp))
    have h2 := ih (ScratchGrow.endFreeBound F cap 0 (ParseStrSuccess.appendChunks (bs.drop k.1) []))
      (ScratchReuseTrace.next cap (ParseStrSuccess.appendChunks (bs.drop k.1) []))
      (fun k hk => hmodels k (by simp [hk]))
    simp only [seriesCost, seriesWork, keyBatches, List.map_cons, ScratchReuseTrace.extraCost]
    simp only [keyBatches, Nat.add_mul] at h1 h2 ⊢
    omega

/-- Growth is charged globally by peak scratch use, not again from capacity zero for every key. -/
theorem seriesCost_budget (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs : List UInt8)
    (keys : List KeySample) (hlen : bs.length < 2 ^ 24)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2))
    (hv : ScratchReuseTrace.Valid cap (keyBatches bs keys)) :
    seriesCost cfg F cap bs keys ≤ seriesWork bs keys * cfg.regularOpCost +
      ScratchReuseTrace.budget cfg F (ScratchReuseTrace.growthCount cap (keyBatches bs keys))
        (ScratchReuseTrace.peak cap (keyBatches bs keys)) := by
  exact (seriesCost_growth cfg F cap bs keys hlen hmodels).trans
    (Nat.add_le_add_left (ScratchReuseTrace.extraCost_budget cfg F cap (keyBatches bs keys) hv) _)

end WNear.Binary.SerdeKeyEsc

namespace WNear.Binary.SerdeKeyEsc
open Wasm Wasm.Near
open WNear.Binary

/-- Every bounded model-decoded key sequence supplies the arithmetic validity of its actual appends. -/
theorem keyBatches_valid (cap : UInt32) (bs : List UInt8) (keys : List KeySample)
    (hlen : bs.length < 2 ^ 24) (hcap : cap.toNat < 2 ^ 28)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    ScratchReuseTrace.Valid cap (keyBatches bs keys) := by
  induction keys generalizing cap with
  | nil => exact hcap
  | cons k keys ih =>
    obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ (hmodels k (by simp))
    have hsmall : ([] : List UInt8).length + (bs.drop k.1).length < 2 ^ 27 := by simp; omega
    have h1 := ParseStrSuccess.appendChunks_valid cap [] (bs.drop k.1) k.2.1.toUTF8.toList k.2.2
      hok (by simp) hcap hsmall
    refine ⟨hcap, h1.1, ?_⟩
    exact ih (ScratchReuseTrace.next cap (ParseStrSuccess.appendChunks (bs.drop k.1) [])) h1.2.2
      (fun k hk => hmodels k (by simp [hk]))

theorem keyBatches_peak (cap : UInt32) (bs : List UInt8) (keys : List KeySample)
    (hlen : bs.length < 2 ^ 24) (hcap : cap.toNat < 2 ^ 28)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    ScratchReuseTrace.peak cap (keyBatches bs keys) ≤ bs.length := by
  induction keys generalizing cap with
  | nil => simp [keyBatches, ScratchReuseTrace.peak]
  | cons k keys ih =>
    obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ (hmodels k (by simp))
    have hsmall : ([] : List UInt8).length + (bs.drop k.1).length < 2 ^ 27 := by simp; omega
    have h1 := ParseStrSuccess.appendChunks_valid cap [] (bs.drop k.1) k.2.1.toUTF8.toList k.2.2
      hok (by simp) hcap hsmall
    have hs := SerdeDeStrEsc.strRun_size (bs.drop k.1) [] k.2.1.toUTF8.toList k.2.2 hok
    simp only [List.length_nil, Nat.zero_add, List.length_drop] at hs
    have h2 := ih (ScratchReuseTrace.next cap (ParseStrSuccess.appendChunks (bs.drop k.1) [])) h1.2.2
      (fun k hk => hmodels k (by simp [hk]))
    simp only [keyBatches, List.map_cons, ScratchReuseTrace.peak]
    have hh := h1.2.1
    simp only [keyBatches] at h2
    simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hh
    omega

/-- The key-only sequence has a global allocation budget under concrete model/length premises.
It does not assume a fresh scratch buffer or an independent free-list bound at each member. -/
theorem seriesCost_budget_model (cfg : WasmConfig) (F : Nat) (cap : UInt32) (bs : List UInt8)
    (keys : List KeySample) (hlen : bs.length < 2 ^ 24) (hcap : cap.toNat < 2 ^ 28)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    seriesCost cfg F cap bs keys ≤ seriesWork bs keys * cfg.regularOpCost +
      ScratchReuseTrace.budget cfg F (ScratchReuseTrace.growthCount cap (keyBatches bs keys)) bs.length := by
  have hv := keyBatches_valid cap bs keys hlen hcap hmodels
  have hp := keyBatches_peak cap bs keys hlen hcap hmodels
  exact (seriesCost_budget cfg F cap bs keys hlen hmodels hv).trans
    (Nat.add_le_add_left (ScratchReuseTrace.budget_mono_peak cfg F _ _ _ hp) _)

theorem keyBatches_growthCount (cap : UInt32) (bs : List UInt8) (keys : List KeySample)
    (hlen : bs.length < 2 ^ 24) (hcap : cap.toNat < 2 ^ 28)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    ScratchReuseTrace.growthCount cap (keyBatches bs keys) = 0 ∨
      8 * 2 ^ (ScratchReuseTrace.growthCount cap (keyBatches bs keys) - 1) ≤ 2 * bs.length + 8 := by
  have hv := keyBatches_valid cap bs keys hlen hcap hmodels
  have hp := keyBatches_peak cap bs keys hlen hcap hmodels
  rcases ScratchReuseTrace.growthCount_peak cap (keyBatches bs keys) hv with hz | hg
  · exact Or.inl hz
  · right; omega

end WNear.Binary.SerdeKeyEsc
