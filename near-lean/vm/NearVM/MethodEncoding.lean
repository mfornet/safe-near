import Interpreter.Wasm.ByteEncoding
import Init.Data.List.SplitOn.Lemmas
import Init.Data.String.Lemmas.Intercalate
import Init.Data.ByteArray.Lemmas
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace Wasm.Near

/-- The key ABI's empty CSV means unrestricted methods. Otherwise preserve
all raw comma-separated fields, as nearcore does before external UTF-8 decoding. -/
def methodNameFields (bytes : List UInt8) : List (List UInt8) :=
  if bytes.isEmpty then [] else bytes.splitOn 44

def decodeMethodNames (bytes : List UInt8) : List String :=
  (methodNameFields bytes).map fun field => (String.fromUTF8? ⟨field.toArray⟩).getD ""

/-- Each field has an actual UTF-8 decoding witness; no billing equality is assumed. -/
def methodNameFieldsUtf8 (bytes : List UInt8) : Bool :=
  (methodNameFields bytes).all fun field => (String.fromUTF8? ⟨field.toArray⟩).isSome

private theorem fields_terminated_length (separator : UInt8) (fields : List (List UInt8)) (h : fields ≠ []) :
    (fields.map (fun field => field.length + 1)).sum = ([separator].intercalate fields).length + 1 := by
  induction fields with
  | nil => contradiction
  | cons first rest ih =>
    cases rest with
    | nil => simp
    | cons second tail =>
      have ht := ih (by simp)
      simp only [List.map_cons, List.sum_cons] at ht
      simp only [List.map_cons, List.sum_cons, List.intercalate_cons_cons, List.length_append,
        List.length_cons, List.length_nil]
      omega

/-- Terminator billing replaces every comma with a terminator and adds the last
one. No assumption about UTF-8 or nonempty individual fields is needed. -/
theorem methodNameFields_billed_length (bytes : List UInt8) :
    ((methodNameFields bytes).map (fun field => field.length + 1)).sum =
      if bytes.isEmpty then 0 else bytes.length + 1 := by
  unfold methodNameFields
  split
  · simp
  · rw [fields_terminated_length 44 (bytes.splitOn 44) (List.splitOn_ne_nil 44 bytes)]
    rw [List.intercalate_splitOn]

private theorem decoded_field_bytes (field : List UInt8)
    (h : (String.fromUTF8? ⟨field.toArray⟩).isSome = true) :
    ((String.fromUTF8? ⟨field.toArray⟩).getD "").toUTF8.toList = field := by
  cases he : String.fromUTF8? ⟨field.toArray⟩ with
  | none => simp [he] at h
  | some decoded =>
    have hb := congrArg ByteArray.toList (Wasm.ByteEncoding.string_fromUTF8_some_bytes _ decoded he)
    simpa only [he, Option.getD_some, Wasm.ByteEncoding.byteArray_toList_ofArray] using hb

private theorem decoded_field_length (field : List UInt8)
    (h : (String.fromUTF8? ⟨field.toArray⟩).isSome = true) :
    ((String.fromUTF8? ⟨field.toArray⟩).getD "").utf8ByteSize = field.length := by
  simpa only [Wasm.ByteEncoding.string_utf8_length] using congrArg List.length (decoded_field_bytes field h)

/-- Decoding valid fields preserves exactly the bytes charged for key methods. -/
theorem decodeMethodNames_billed_length (bytes : List UInt8) (h : methodNameFieldsUtf8 bytes = true) :
    ((decodeMethodNames bytes).map (fun method => method.utf8ByteSize + 1)).sum =
      if bytes.isEmpty then 0 else bytes.length + 1 := by
  rw [← methodNameFields_billed_length]
  unfold decodeMethodNames
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro field hfield
  have hv : (String.fromUTF8? ⟨field.toArray⟩).isSome = true := (List.all_eq_true.mp h) field hfield
  exact congrArg (fun n : Nat => n + 1) (decoded_field_length field hv)

/-- Valid field decoding preserves every byte, including multibyte method names. -/
theorem decodeMethodNames_bytes (bytes : List UInt8) (h : methodNameFieldsUtf8 bytes = true) :
    ((decodeMethodNames bytes).map (fun method => method.toUTF8.toList)) = methodNameFields bytes := by
  unfold decodeMethodNames
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (l := methodNameFields bytes)]
  apply List.map_congr_left
  intro field hfield
  exact decoded_field_bytes field ((List.all_eq_true.mp h) field hfield)

private theorem string_utf8_append (left right : String) :
    (left ++ right).toUTF8.toList = left.toUTF8.toList ++ right.toUTF8.toList := by
  simp only [String.toUTF8_eq_toByteArray, String.toByteArray_append,
    Wasm.ByteEncoding.byteArray_toList_eq, ByteArray.toList_data_append]

private theorem intercalate_method_bytes (methods : List String) :
    (",".intercalate methods).toUTF8.toList = [44].intercalate (methods.map fun method => method.toUTF8.toList) := by
  induction methods with
  | nil => simp
  | cons first rest ih =>
    cases rest with
    | nil => simp
    | cons second tail =>
      simp only [String.intercalate_cons_cons, List.map_cons, List.intercalate_cons_cons,
        string_utf8_append]
      rw [ih, show ",".toUTF8.toList = [44] from by rw [Wasm.ByteEncoding.byteArray_toList_eq]; rfl]
      rfl

/-- Per-field UTF-8 validation implies the entire raw CSV has a decoding.
This keeps the previous whole-buffer witness while following native per-field validation. -/
theorem methodNameFieldsUtf8_decodes (bytes : List UInt8) (h : methodNameFieldsUtf8 bytes = true) :
    ∃ decoded, String.fromUTF8? ⟨bytes.toArray⟩ = some decoded := by
  let decoded := ",".intercalate (decodeMethodNames bytes)
  have hb : decoded.toUTF8.toList = bytes := by
    rw [intercalate_method_bytes, decodeMethodNames_bytes bytes h]
    unfold methodNameFields
    split
    · simp_all
    · exact List.intercalate_splitOn 44
  have he : decoded.toUTF8 = ⟨bytes.toArray⟩ :=
    Wasm.ByteEncoding.byteArray_toList_injective (by simpa only [Wasm.ByteEncoding.byteArray_toList_ofArray] using hb)
  exact ⟨decoded, he ▸ Wasm.ByteEncoding.string_fromUTF8_toUTF8 decoded⟩

end Wasm.Near
