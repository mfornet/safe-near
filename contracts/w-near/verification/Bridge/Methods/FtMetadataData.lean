import Bridge.Methods.InitialState
import Bridge.Functions.MetadataFields
import Model

/-!
# `ft_metadata` (309): the data it reads and the JSON it returns, against the model

* The data segment holds what the getter (308) and the struct serializer (102) read: the three
  constant strings at 1051277 (`seg_metaStrs`), the keys at 1048761 (`seg_metaKeys`), `null` at
  1048754, the punctuation, `ESCAPE` from `' '` at 1061840 (`seg_escT`) and `DEC_DIGITS_LUT` at
  1049500 (`seg_lut2`, the same table as `FmtDigits.lut`).
* `metaJson_eq`: the bytes the binary's serializer writes (`MetadataFields.metaJson`: the fields in
  declaration order, `None` as `null`, `decimals` as the digits `24`) are the model's
  `(Ret.metadata metadata).json`, byte for byte; no byte of the constant strings needs escaping.
* `returnBytes_ftMetadata`: the model's bound on the returned bytes is their 138.
-/

namespace WNear.Binary.InitialState

open WNear.Binary.MetadataFields WNear.Binary.MetadataGetter

set_option maxRecDepth 100000 in
theorem seg_metaStrs : seg 1051277 40 = metaStrs := by decide
set_option maxRecDepth 100000 in
theorem seg_metaKeys : seg 1048761 49 = metaKeys := by decide
theorem seg_null : seg 1048754 4 = nullStr := by decide
theorem seg_comma2 : seg 1051819 1 = [44] := by decide
set_option maxRecDepth 100000 in
theorem seg_escT : seg 1061840 96 = escT := by decide
set_option maxRecDepth 100000 in
theorem seg_lut2 : seg 1049500 200 = FmtDigits.lut := by decide

end WNear.Binary.InitialState

namespace WNear.Binary.FtMetadataMethod

open WNear.Binary.MetadataFields

/-- The model's JSON, as a literal. -/
def metaLit : String :=
  "{\"spec\":\"ft-1.0.0\",\"name\":\"Wrapped NEAR fungible token\",\"symbol\":\"wNEAR\",\"icon\":null,\"reference\":null,\"reference_hash\":null,\"decimals\":24}"

set_option maxRecDepth 100000 in
theorem json_eq : (WNear.Ret.metadata WNear.metadata).json = metaLit := by
  decide

/-- An ASCII string's bytes. -/
theorem ascii_bytes (s : String) (h : ∀ c ∈ s.toList, c.val ≤ 127) :
    s.toUTF8.toList = s.toList.map (fun c => c.toUInt8) := by
  conv => lhs; rw [← String.ofList_toList (s := s)]
  rw [String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode, ToVec.flat_ascii _ h,
    ToVec.toList_eq]
  simp

set_option maxRecDepth 100000 in
/-- **The binary's JSON is the model's**: `{"spec":"ft-1.0.0","name":"Wrapped NEAR fungible
token","symbol":"wNEAR","icon":null,"reference":null,"reference_hash":null,"decimals":24}`. -/
theorem metaJson_eq : (WNear.Ret.metadata WNear.metadata).json.toUTF8.toList = metaJson := by
  rw [json_eq, ascii_bytes _ (by decide)]
  decide

set_option maxRecDepth 100000 in
theorem returnBytes_ftMetadata : WNear.Call.returnBytes .ftMetadata = 138 := by
  rw [WNear.Call.returnBytes, json_eq]
  decide

end WNear.Binary.FtMetadataMethod
