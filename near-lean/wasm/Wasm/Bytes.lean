/-!
# Bytes, byte arrays and UTF-8

Small facts about `ByteArray.toList` and `String.fromUTF8?` that the NEAR
runtime's encoding proofs use. In Lean 4.34 a `String` is its UTF-8 byte
array with a validity proof, so the round trips are by construction.
-/

namespace Wasm.ByteEncoding

theorem byteArray_toList_loop (bs : ByteArray) (n : Nat) :
    ∀ (i : Nat) (r : List UInt8), bs.size - i = n →
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction n with
  | zero =>
    intro i r hn
    unfold ByteArray.toList.loop
    have h : ¬ i < bs.size := by omega
    have hle : bs.data.toList.length ≤ i := by
      rw [Array.length_toList]; exact Nat.le_of_not_lt h
    simp only [h, ↓reduceIte]
    rw [List.drop_of_length_le hle, List.append_nil]
  | succ n ih =>
    intro i r hn
    unfold ByteArray.toList.loop
    have h : i < bs.size := by omega
    simp only [h, ↓reduceIte]
    rw [ih (i + 1) _ (by omega)]
    simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
    congr 1
    have hlt : i < bs.data.toList.length := by rw [Array.length_toList]; exact h
    rw [List.drop_eq_getElem_cons hlt]
    congr 1
    have hd : i < bs.data.size := h
    show bs.data[i]! = bs.data[i]
    exact getElem!_pos bs.data i hd

theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  unfold ByteArray.toList
  rw [byteArray_toList_loop b (b.size - 0) 0 [] rfl]
  rfl

theorem byteArray_toList_length (b : ByteArray) : b.toList.length = b.size := by
  rw [byteArray_toList_eq, Array.length_toList]
  rfl

theorem byteArray_toList_ofArray (a : Array UInt8) : (ByteArray.mk a).toList = a.toList :=
  byteArray_toList_eq _

theorem byteArray_of_toList (b : ByteArray) : (⟨b.toList.toArray⟩ : ByteArray) = b := by
  cases b
  simp [byteArray_toList_eq]

theorem byteArray_toList_injective {a b : ByteArray} (h : a.toList = b.toList) : a = b := by
  cases a; cases b
  simp only [byteArray_toList_eq] at h
  congr 1
  exact Array.toList_inj.mp h

theorem string_fromUTF8_toUTF8 (s : String) : String.fromUTF8? s.toUTF8 = some s := by
  cases s with
  | ofByteArray b h => simp [String.fromUTF8?, String.fromUTF8, h]

theorem string_fromUTF8_some_bytes (b : ByteArray) (s : String)
    (h : String.fromUTF8? b = some s) : s.toUTF8 = b := by
  unfold String.fromUTF8? at h
  split at h
  · cases h; rfl
  · cases h

theorem string_utf8_length (s : String) : s.toUTF8.toList.length = s.utf8ByteSize := by
  rw [byteArray_toList_length]
  rfl

end Wasm.ByteEncoding
