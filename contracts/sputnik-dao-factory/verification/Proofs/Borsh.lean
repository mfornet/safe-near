import Model.Borsh
import Proofs.Namespaces

namespace SputnikFactory

theorem fromLE_leBytes (width n : Nat) (h : n < 256 ^ width) :
    Borsh.fromLE (leBytes width n) = n := by
  induction width generalizing n with
  | zero =>
    have hn : n = 0 := by simpa using h
    simp [hn, Borsh.fromLE, leBytes]
  | succ width ih =>
    have hdiv : n / 256 < 256 ^ width := by
      rw [Nat.pow_succ] at h
      omega
    simp only [leBytes, Borsh.fromLE, UInt8.toNat_ofNat', ih _ hdiv]
    have hm : n % 256 < 256 := Nat.mod_lt _ (by decide)
    change n % 256 % 256 + 256 * (n / 256) = n
    rw [Nat.mod_eq_of_lt hm]
    omega

theorem borsh_take_append (width : Nat) (bytes rest : Bytes)
    (h : bytes.length = width) :
    Borsh.take width (bytes ++ rest) = some (bytes, rest) := by
  simp [Borsh.take, h]

theorem natural_encode (width n : Nat) (rest : Bytes) (h : n < 256 ^ width) :
    Borsh.natural width (leBytes width n ++ rest) = some (n, rest) := by
  simp [Borsh.natural, borsh_take_append, fromLE_leBytes, h]

theorem exact_natural_encode (width n : Nat) (h : n < 256 ^ width) :
    Borsh.exact (Borsh.natural width) (leBytes width n) = some n := by
  have hdecode := natural_encode width n [] h
  simpa [Borsh.exact] using congrArg
    (fun result => result.bind fun parsed =>
      if parsed.2 = [] then some parsed.1 else none) hdecode

theorem bytes_encode (bytes rest : Bytes) (h : bytes.length < 256 ^ 4) :
    Borsh.bytes (borshBytes bytes ++ rest) = some (bytes, rest) := by
  simp [Borsh.bytes, borshBytes, List.append_assoc,
    natural_encode, borsh_take_append, h]

theorem vector_encode (header : VectorHeader) (rest : Bytes)
    (hlen : header.length < 256 ^ 8)
    (hprefix : header.keyPrefix.length < 256 ^ 4) :
    Borsh.vector (Borsh.encodeVector header ++ rest) = some (header, rest) := by
  cases header with
  | mk length keyPrefix =>
    simp [Borsh.vector, Borsh.encodeVector, natural_encode,
      bytes_encode, hlen, hprefix, List.append_assoc]

theorem set_encode (header : SetHeader) (rest : Bytes)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4) :
    Borsh.setHeader (Borsh.encodeSet header ++ rest) = some (header, rest) := by
  cases header with
  | mk indexPrefix elements =>
    simp [Borsh.setHeader, Borsh.encodeSet, List.append_assoc,
      bytes_encode, vector_encode, hindex, hlen, hprefix]

theorem map_encode (header : MapHeader) (rest : Bytes)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hkeys : header.keys.length < 256 ^ 8)
    (hkeyPrefix : header.keys.keyPrefix.length < 256 ^ 4)
    (hvalues : header.values.length < 256 ^ 8)
    (hvaluePrefix : header.values.keyPrefix.length < 256 ^ 4) :
    Borsh.mapHeader (Borsh.encodeMap header ++ rest) = some (header, rest) := by
  cases header with
  | mk indexPrefix keys values =>
    simp [Borsh.mapHeader, Borsh.encodeMap, List.append_assoc,
      bytes_encode, vector_encode, hindex, hkeys, hkeyPrefix, hvalues, hvaluePrefix]

theorem exact_set_encode (header : SetHeader)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hlen : header.elements.length < 256 ^ 8)
    (hprefix : header.elements.keyPrefix.length < 256 ^ 4) :
    Borsh.exact Borsh.setHeader (Borsh.encodeSet header) = some header := by
  have h := set_encode header [] hindex hlen hprefix
  simp only [List.append_nil] at h
  simp [Borsh.exact, h]

theorem exact_map_encode (header : MapHeader)
    (hindex : header.indexPrefix.length < 256 ^ 4)
    (hkeys : header.keys.length < 256 ^ 8)
    (hkeyPrefix : header.keys.keyPrefix.length < 256 ^ 4)
    (hvalues : header.values.length < 256 ^ 8)
    (hvaluePrefix : header.values.keyPrefix.length < 256 ^ 4) :
    Borsh.exact Borsh.mapHeader (Borsh.encodeMap header) = some header := by
  have h := map_encode header [] hindex hkeys hkeyPrefix hvalues hvaluePrefix
  simp only [List.append_nil] at h
  simp [Borsh.exact, h]

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
