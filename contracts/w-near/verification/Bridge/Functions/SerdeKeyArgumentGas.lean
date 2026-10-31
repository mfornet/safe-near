import Bridge.Functions.SerdeKeyTraceCost
import Bridge.Methods.FtTotalSupplyGas

/-! The key-only reserve fits a slice of the unchanged argument-byte gas allowance.
Whole-object coverage, other parser operations and runtime charges remain separate. -/

namespace WNear.Binary.SerdeKeyEsc
open Wasm Wasm.Near
open WNear.Binary

theorem keyBatches_growthCount_v86 (cap : UInt32) (bs : List UInt8) (keys : List KeySample)
    (hlen : bs.length ≤ 4194304) (hcap : cap.toNat < 2 ^ 28)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    ScratchReuseTrace.growthCount cap (keyBatches bs keys) ≤ 21 := by
  have hg := keyBatches_growthCount cap bs keys (by omega) hcap hmodels
  rcases hg with hz | hp
  · omega
  · by_contra hn
    have he : 21 ≤ ScratchReuseTrace.growthCount cap (keyBatches bs keys) - 1 := by omega
    have hpow := Nat.pow_le_pow_right (n := 2) (by decide) he
    have hp8 := Nat.mul_le_mul_left 8 hpow
    change 16777216 ≤ 8 * 2 ^ (ScratchReuseTrace.growthCount cap (keyBatches bs keys) - 1) at hp8
    omega

def consumed (bs : List UInt8) : List KeySample → Nat
  | [] => 0
  | k :: keys => (bs.drop k.1).length - k.2.2.length + consumed bs keys

theorem seriesWork_eq (bs : List UInt8) (keys : List KeySample) :
    seriesWork bs keys = 500 * keys.length + 433 * consumed bs keys := by
  induction keys with
  | nil => simp [seriesWork, consumed]
  | cons k keys ih => simp only [seriesWork, consumed, ih, List.length_cons]; omega

theorem keyBatches_peak_consumed (cap : UInt32) (bs : List UInt8) (keys : List KeySample)
    (hlen : bs.length < 2 ^ 24) (hcap : cap.toNat < 2 ^ 28)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    ScratchReuseTrace.peak cap (keyBatches bs keys) ≤ consumed bs keys := by
  induction keys generalizing cap with
  | nil => simp [keyBatches, ScratchReuseTrace.peak, consumed]
  | cons k keys ih =>
    obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ (hmodels k (by simp))
    have hsmall : ([] : List UInt8).length + (bs.drop k.1).length < 2 ^ 27 := by simp; omega
    have hv := ParseStrSuccess.appendChunks_valid cap [] (bs.drop k.1) k.2.1.toUTF8.toList k.2.2
      hok (by simp) hcap hsmall
    have hs := SerdeDeStrEsc.strRun_size (bs.drop k.1) [] k.2.1.toUTF8.toList k.2.2 hok
    have ht := ih (ScratchReuseTrace.next cap (ParseStrSuccess.appendChunks (bs.drop k.1) [])) hv.2.2
      (fun k hk => hmodels k (by simp [hk]))
    have hh := hv.2.1
    simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl] at hh
    simp only [List.length_nil, Nat.zero_add] at hs
    simp only [keyBatches, List.map_cons, ScratchReuseTrace.peak, consumed]
    simp only [keyBatches] at ht
    omega

theorem reserve_budget_v86 (cfg : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 cfg)
    (G P : Nat) (hg : G ≤ 21) :
    ScratchReuseTrace.budget cfg.wasm 1 G P ≤ 200000000000 + 37 * 822756 * P := by
  have hsq : G * G ≤ 441 := (Nat.mul_le_mul hg hg)
  have hw : 1 * G + G * G - G ≤ 441 := by omega
  have hwork : 1790 * G + (1 * G + G * G - G) * 320 + 18 * (2 * P + 8) ≤ 178854 + 36 * P := by omega
  have hr := Nat.mul_le_mul hwork hc.regularOp
  have hb := Nat.mul_le_mul hg hc.linearBase
  have hp : (4 * P + 16 + 66066 * G) / 65536 ≤ P + 22 := by omega
  have hu := Nat.mul_le_mul hc.linearUnit hp
  unfold ScratchReuseTrace.budget
  simp only [Nat.add_mul, Nat.mul_add] at hr hu ⊢
  omega

theorem seriesCost_argument_slice (cfg : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 cfg)
    (bs : List UInt8) (keys : List KeySample) (hlen : bs.length ≤ 4194304)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    seriesCost cfg.wasm 1 0 bs keys ≤
      200000000000 + 400000000 * (consumed bs keys + 2 * keys.length) := by
  have hv := keyBatches_valid 0 bs keys (by omega) (by decide) hmodels
  have hp := keyBatches_peak_consumed 0 bs keys (by omega) (by decide) hmodels
  have hg := keyBatches_growthCount_v86 0 bs keys hlen (by decide) hmodels
  have he := seriesCost_budget cfg.wasm 1 0 bs keys (by omega) hmodels hv
  have hr := reserve_budget_v86 cfg hc (ScratchReuseTrace.growthCount 0 (keyBatches bs keys))
    (ScratchReuseTrace.peak 0 (keyBatches bs keys)) hg
  have hm := Nat.mul_le_mul_left (37 * 822756) hp
  have hw := Nat.mul_le_mul_left (seriesWork bs keys) hc.regularOp
  rw [seriesWork_eq] at he hw
  simp only [Nat.add_mul, Nat.mul_add] at he hw ⊢
  omega

/-- The key-reader component uses the actual unchanged model argument-byte allowance.
Whole-object coverage of this slice and other parser/runtime costs are separate. -/
theorem seriesCost_argument_gas (cfg : RuntimeConfig) (hc : FtTotalSupplyMethod.CostsV86 cfg)
    (bs : List UInt8) (keys : List KeySample) (hlen : bs.length ≤ 4194304)
    (hmodels : ∀ k ∈ keys, NearInterface.Json.stringBody (bs.drop k.1) [] = some (some k.2.1, k.2.2)) :
    seriesCost cfg.wasm 1 0 bs keys ≤
      200000000000 + WNear.argumentByteGas * (consumed bs keys + 2 * keys.length) := by
  change seriesCost cfg.wasm 1 0 bs keys ≤ 200000000000 + 400000000 * (consumed bs keys + 2 * keys.length)
  exact seriesCost_argument_slice cfg hc bs keys hlen hmodels

end WNear.Binary.SerdeKeyEsc
