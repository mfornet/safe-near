import Bridge.Functions.SerdeFieldPrecise
import Bridge.Functions.StrGrowthTight

set_option maxRecDepth 100000

namespace WNear.Binary.SerdeKeyReuse
open Wasm Wasm.Near
open WNear.Binary.ParseStr (borrowed strRun)
open WNear.Binary.ParseStrSuccess (appendChunks)
set_option maxRecDepth 100000
theorem preciseCost_growth_tight (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs : List UInt8) (q : Nat) (key : String) (rest : List UInt8)
    (hlen : bs.length < 2 ^ 24)
    (hmodel : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    preciseCost cfg F cap bs key.toUTF8.toList rest q ≤
      (300 + 433 * ((bs.drop q).length - rest.length)) * cfg.regularOpCost +
        ScratchGrow.extraCost cfg F cap 0 (appendChunks (bs.drop q) []) := by
  obtain ⟨hok, hu⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hmodel
  by_cases hb : borrowed (bs.drop q)
  · have he := keyCost_borrowed cfg F cap bs key.toUTF8.toList rest q hb hok hu
    simp only [keyCost, if_pos hb] at he
    simp only [preciseCost, if_pos hb, he]
    have hh := Nat.mul_le_mul_right cfg.regularOpCost
      (show 300 + 130 * ((bs.drop q).length - rest.length) ≤ 300 + 433 * ((bs.drop q).length - rest.length) by omega)
    omega
  · have hsmall : ([] : List UInt8).length + (bs.drop q).length < 2 ^ 27 := by simp; omega
    have he := (ParseStrSuccess.costRun_growth_tight cfg F cap [] (bs.drop q) key.toUTF8.toList rest bs.length hok hsmall).2
    simp only [List.length_nil, show UInt32.ofNat 0 = (0 : UInt32) from rfl, Nat.mul_zero, Nat.add_zero] at he
    simp only [preciseCost, if_neg hb, SerdeKeyEsc.tracedCost]
    simp only [Nat.add_mul] at he ⊢
    omega


theorem bundledCost_growth_tight (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs : List UInt8) (q : Nat) (key : String) (rest : List UInt8) (hlen : bs.length < 2 ^ 24)
    (hm : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest)) :
    SerdeKey.cost194 * cfg.regularOpCost + bundledCost cfg F cap bs key.toUTF8.toList rest q ≤
      ((if key.toUTF8.toList.length = 10 then 642 else 380) + 433 * ((bs.drop q).length - rest.length)) * cfg.regularOpCost +
        ScratchGrow.extraCost cfg F cap 0 (appendChunks (bs.drop q) []) := by
  have hraw := preciseCost_growth_tight cfg F cap bs q key rest hlen hm
  have hc : SerdeKey.cost194 = 342 := by decide
  have hbase : SerdeKey.cost194 ≤ 300 + 433 * ((bs.drop q).length - rest.length) + SerdeKeyTight.fieldCost key.toUTF8.toList := by
    rw [hc]
    unfold SerdeKeyTight.fieldCost
    split <;> omega
  have hbase' := Nat.mul_le_mul_right cfg.regularOpCost hbase
  unfold bundledCost
  by_cases hk : key.toUTF8.toList.length = 10
  · simp only [SerdeKeyTight.fieldCost, if_pos hk, hc, Nat.add_mul] at hraw hbase' ⊢
    omega
  · simp only [SerdeKeyTight.fieldCost, if_neg hk, hc, Nat.add_mul] at hraw hbase' ⊢
    omega

/-- Complete unknown-member regular work fits its byte slice; actual retained growth is separate. -/
theorem ignored_member_regular_budget (cfg : WasmConfig) (F : Nat) (cap : UInt32)
    (bs : List UInt8) (q : Nat) (key : String) (rest : List UInt8) (m : Nat)
    (hlen : bs.length < 2 ^ 24) (hm : NearInterface.Json.stringBody (bs.drop q) [] = some (some key, rest))
    (hmpos : 1 ≤ m) :
    (942 + 166 + 470 * m) * cfg.regularOpCost + SerdeKey.cost194 * cfg.regularOpCost +
      bundledCost cfg F cap bs key.toUTF8.toList rest q ≤
    486 * (((bs.drop q).length - rest.length) + m + 3) * cfg.regularOpCost +
      ScratchGrow.extraCost cfg F cap 0 (appendChunks (bs.drop q) []) := by
  obtain ⟨hok, _⟩ := SerdeAccountIdEsc.strRun_of_stringBody _ _ _ hm
  have hs := SerdeDeStrEsc.strRun_size (bs.drop q) [] key.toUTF8.toList rest hok
  simp only [List.length_nil, Nat.zero_add] at hs
  have hkey := bundledCost_growth_tight cfg F cap bs q key rest hlen hm
  have hops : 942 + 166 + 470 * m + (if key.toUTF8.toList.length = 10 then 642 else 380) +
      433 * ((bs.drop q).length - rest.length) ≤ 486 * (((bs.drop q).length - rest.length) + m + 3) := by
    split <;> omega
  have hmul := Nat.mul_le_mul_right cfg.regularOpCost hops
  simp only [Nat.add_mul, Nat.mul_assoc] at hkey hmul ⊢
  omega

end WNear.Binary.SerdeKeyReuse
namespace WNear.Binary.SerdeKeyReuse
/-- The existing reviewed operation bound funds 486 regular operations per model input byte. -/
theorem regular_byte_rate (op : Nat) (hop : op ≤ 822756) : 486 * op ≤ 400000000 := by omega
end WNear.Binary.SerdeKeyReuse
