import Init.Omega
import Init.Data.Array.Lemmas
import Init.Data.List.TakeDrop
import Init.Data.String.Basic

namespace Wasm.ByteEncoding

private theorem byteArray_loop_length (b : ByteArray) (i : Nat) (acc : List UInt8) :
    (ByteArray.toList.loop b i acc).length = acc.length + (b.size - i) := by
  rw [ByteArray.toList.loop]
  split
  · rw [byteArray_loop_length b (i + 1) (b.get! i :: acc)]
    simp only [List.length_cons]
    omega
  · simp only [List.length_reverse]
    omega
termination_by b.size - i

/-- Byte extraction preserves the measured byte length; no compiler evaluation
or UTF-8 decoding assumption is needed. -/
@[simp] theorem byteArray_toList_length (b : ByteArray) : b.toList.length = b.size := by
  simpa only [ByteArray.toList, List.length_nil, Nat.sub_zero, Nat.zero_add] using
    byteArray_loop_length b 0 []

private theorem byteArray_loop_contents (b : ByteArray) (i : Nat) (acc : List UInt8) :
    ByteArray.toList.loop b i acc = acc.reverse ++ b.data.toList.drop i := by
  rw [ByteArray.toList.loop]
  split
  · rename_i hi
    rw [byteArray_loop_contents b (i + 1) (b.get! i :: acc)]
    have hil : i < b.data.toList.length := hi
    rw [List.drop_eq_getElem_cons hil]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 2
    cases b with
    | mk data =>
      change data[i]! = data[i]
      exact getElem!_pos data i hi
  · rename_i hi
    have hil : b.data.toList.length ≤ i := Nat.le_of_not_gt hi
    simp only [List.drop_eq_nil_of_le hil, List.append_nil]
termination_by b.size - i

/-- The executable byte-array traversal agrees with its underlying array. -/
theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  simpa only [ByteArray.toList, List.reverse_nil, List.nil_append, List.drop_zero] using
    byteArray_loop_contents b 0 []

theorem byteArray_toList_injective {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simpa only [byteArray_toList_eq] using h

@[simp] theorem byteArray_of_toList (bytes : ByteArray) :
    (ByteArray.mk bytes.toList.toArray) = bytes := by
  apply ByteArray.ext
  simp [byteArray_toList_eq]

@[simp] theorem byteArray_toList_ofArray (bytes : List UInt8) :
    (ByteArray.mk bytes.toArray).toList = bytes := by
  simp [byteArray_toList_eq]

@[simp] theorem string_utf8_length (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
  rw [byteArray_toList_length]
  rfl

theorem string_fromUTF8_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  simp only [String.toUTF8_eq_toByteArray, String.fromUTF8?, dite_eq_left s.isValidUTF8]
  rfl

theorem string_fromUTF8_some_bytes (bytes : ByteArray) (s : String)
    (h : String.fromUTF8? bytes = some s) : s.toUTF8 = bytes := by
  unfold String.fromUTF8? at h
  split at h
  · have he := Option.some.inj h
    subst s
    rfl
  · contradiction

end Wasm.ByteEncoding
