import Model.Borsh
import Proofs.Namespaces

namespace SputnikFactory

export NearSdk.Borsh (fromLE_leBytes)
export NearSdk.BorshParse (borsh_take_append natural_encode exact_natural_encode bytes_encode)
export NearSdk.Collections (vector_encode set_encode map_encode exact_set_encode exact_map_encode)

theorem string_utf8_roundtrip (value : String) :
    String.fromUTF8? ⟨value.toUTF8.data.toList.toArray⟩ = some value := by
  cases value with
  | ofByteArray bytes valid =>
    simp [String.toUTF8_eq_toByteArray, String.fromUTF8?, String.fromUTF8, valid]

/-- The text proof exposes the UTF-8 inverse required to connect Lean's string
decoder to Borsh's byte representation. No trusted axiom is introduced. -/
theorem text_encode (value : String) (rest : Bytes)
    (hlen : value.toUTF8.data.toList.length < 256 ^ 4)
    (hutf8 : String.fromUTF8? ⟨value.toUTF8.data.toList.toArray⟩ = some value) :
    Borsh.text (borshString value ++ rest) = some (value, rest) := by
  simp only [String.toUTF8_eq_toByteArray] at hlen hutf8
  simp only [Borsh.text, borshString, String.toUTF8_eq_toByteArray]
  rw [bytes_encode value.toByteArray.data.toList rest hlen]
  simp [hutf8]

theorem metadata_encode (value : Metadata) (rest : Bytes)
    (hcommit : value.commit.toUTF8.data.toList.length < 256 ^ 4)
    (hcommitUtf8 : String.fromUTF8?
      ⟨value.commit.toUTF8.data.toList.toArray⟩ = some value.commit)
    (hchange : ∀ text, value.changelog = some text →
      text.toUTF8.data.toList.length < 256 ^ 4 ∧
      String.fromUTF8? ⟨text.toUTF8.data.toList.toArray⟩ = some text) :
    Borsh.metadata (Borsh.encodeMetadata value ++ rest) = some (value, rest) := by
  cases value with
  | mk major minor commit changelog =>
    cases changelog with
    | none =>
      have hc := text_encode commit (0 :: rest) hcommit hcommitUtf8
      simp [Borsh.metadata, Borsh.encodeMetadata, Borsh.optionalText,
        hc, List.append_assoc]
    | some text =>
      have htext := hchange text rfl
      have hc : Borsh.text (borshString commit ++ 1 :: (borshString text ++ rest)) =
          some (commit, 1 :: (borshString text ++ rest)) := by
        simpa using text_encode commit (1 :: (borshString text ++ rest))
          hcommit hcommitUtf8
      have ht := text_encode text rest htext.1 htext.2
      simp [Borsh.metadata, Borsh.encodeMetadata, Borsh.optionalText,
        hc, ht, List.append_assoc]

theorem exact_metadata_encode (value : Metadata)
    (hcommit : value.commit.toUTF8.data.toList.length < 256 ^ 4)
    (hcommitUtf8 : String.fromUTF8?
      ⟨value.commit.toUTF8.data.toList.toArray⟩ = some value.commit)
    (hchange : ∀ text, value.changelog = some text →
      text.toUTF8.data.toList.length < 256 ^ 4 ∧
      String.fromUTF8? ⟨text.toUTF8.data.toList.toArray⟩ = some text) :
    Borsh.exact Borsh.metadata (Borsh.encodeMetadata value) = some value := by
  have h := metadata_encode value [] hcommit hcommitUtf8 hchange
  simp only [List.append_nil] at h
  simp [Borsh.exact, h]

theorem exact_metadata_encode_bounded (value : Metadata)
    (hcommit : value.commit.toUTF8.data.toList.length < 256 ^ 4)
    (hchange : ∀ text, value.changelog = some text →
      text.toUTF8.data.toList.length < 256 ^ 4) :
    Borsh.exact Borsh.metadata (Borsh.encodeMetadata value) = some value := by
  exact exact_metadata_encode value hcommit (string_utf8_roundtrip value.commit)
    (fun text h => ⟨hchange text h, string_utf8_roundtrip text⟩)

end SputnikFactory
