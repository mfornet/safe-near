import Model.FactoryEncoding
import Proofs.ConfigPolicyDecoding

namespace SputnikDAO2

theorem parse_factory_info_encoded (validAccount : String → Bool)
    (info : FactoryInfo) (rest : BountyBytes)
    (hfits : wireStringFits info.factoryId)
    (hvalid : validAccount info.factoryId = true) :
    parseFactoryInfo validAccount (encodeFactoryInfo info ++ rest) =
      some (info, rest) := by
  have hs := parse_wire_string_encoded info.factoryId
    ([if info.autoUpdate then 1 else 0] ++ rest) hfits
  unfold parseFactoryInfo encodeFactoryInfo
  simp only [List.append_assoc]
  rw [hs]
  cases hauto : info.autoUpdate <;>
    simp [hvalid, bountyParseBool]
  all_goals cases info <;> simp_all

theorem parse_factory_info_exact_encoded (validAccount : String → Bool)
    (info : FactoryInfo)
    (hfits : wireStringFits info.factoryId)
    (hvalid : validAccount info.factoryId = true) :
    parseFactoryInfoExact validAccount (encodeFactoryInfo info) =
      some info := by
  have h := parse_factory_info_encoded validAccount info [] hfits hvalid
  simp only [List.append_nil] at h
  simp [parseFactoryInfoExact, h]

theorem parse_factory_info_rejects_trailing_byte
    (validAccount : String → Bool) (info : FactoryInfo) (extra : UInt8)
    (hfits : wireStringFits info.factoryId)
    (hvalid : validAccount info.factoryId = true) :
    parseFactoryInfoExact validAccount
      (encodeFactoryInfo info ++ [extra]) = none := by
  have h := parse_factory_info_encoded validAccount info [extra] hfits hvalid
  simp [parseFactoryInfoExact, h]

theorem parse_factory_info_rejects_invalid_account
    (validAccount : String → Bool) (info : FactoryInfo)
    (hfits : wireStringFits info.factoryId)
    (hinvalid : validAccount info.factoryId = false) :
    parseFactoryInfoExact validAccount (encodeFactoryInfo info) = none := by
  have hs := parse_wire_string_encoded info.factoryId
    [if info.autoUpdate then 1 else 0] hfits
  simp [parseFactoryInfoExact, parseFactoryInfo, encodeFactoryInfo,
    hs, hinvalid]

theorem parse_factory_info_rejects_invalid_bool
    (validAccount : String → Bool) (factoryId : String)
    (hfits : wireStringFits factoryId)
    (hvalid : validAccount factoryId = true) :
    parseFactoryInfoExact validAccount
      (bountyBorshString factoryId ++ [2]) = none := by
  have hs := parse_wire_string_encoded factoryId [2] hfits
  simp [parseFactoryInfoExact, parseFactoryInfo, hs,
    hvalid, bountyParseBool]

theorem parse_factory_info_rejects_missing_bool
    (validAccount : String → Bool) (factoryId : String)
    (hfits : wireStringFits factoryId)
    (hvalid : validAccount factoryId = true) :
    parseFactoryInfoExact validAccount
      (bountyBorshString factoryId) = none := by
  have hs := parse_wire_string_encoded factoryId [] hfits
  simp only [List.append_nil] at hs
  simp [parseFactoryInfoExact, parseFactoryInfo, hs,
    hvalid, bountyParseBool]

end SputnikDAO2
