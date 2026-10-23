import Wasm.Bytes
import Init.Omega
import Init.Data.Array.Lemmas
import Init.Data.List.TakeDrop

/-!
# Borsh encoding (the fragment used by wNEAR)

Only the encoders needed to describe the on-chain layout of the contract
state: little-endian fixed-width integers and length-prefixed byte strings.

This belongs in a shared `near-lean/sdk` library once that exists; it is kept
here so the contract model is self-contained.
-/

namespace WNear.Borsh

abbrev Bytes := List UInt8

/-- `width` little-endian bytes of `n`. Callers keep `n < 2 ^ (8 * width)`. -/
def leBytes : (width : Nat) → Nat → Bytes
  | 0, _ => []
  | w + 1, n => UInt8.ofNat (n % 256) :: leBytes w (n / 256)

def u32 (n : Nat) : Bytes := leBytes 4 n
def u64 (n : Nat) : Bytes := leBytes 8 n
def u128 (n : Nat) : Bytes := leBytes 16 n

/-- Borsh `Vec<u8>`: `u32` length prefix followed by the bytes. -/
def bytes (b : Bytes) : Bytes := u32 b.length ++ b

/-- Borsh `String`: `u32` byte-length prefix followed by the UTF-8 bytes. -/
def string (s : String) : Bytes := bytes s.toUTF8.toList

@[simp] theorem leBytes_length (w n : Nat) : (leBytes w n).length = w := by
  induction w generalizing n with
  | zero => rfl
  | succ w ih => simp [leBytes, ih]

/-- Interpret fixed-width little-endian bytes as a natural number. -/
def fromLE : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * fromLE bs

/-- Fixed-width encoding loses no information inside its representable range. -/
theorem fromLE_leBytes (width n : Nat) (h : n < 256 ^ width) :
    fromLE (leBytes width n) = n := by
  induction width generalizing n with
  | zero =>
    simp only [Nat.pow_zero] at h
    have hn : n = 0 := by omega
    simp [hn, leBytes, fromLE]
  | succ width ih =>
    have hdiv : n / 256 < 256 ^ width := by
      rw [Nat.pow_succ] at h
      omega
    simp only [leBytes, fromLE, UInt8.toNat_ofNat', ih _ hdiv]
    have hmod : n % 256 < 256 := Nat.mod_lt _ (by decide)
    change n % 256 % 256 + 256 * (n / 256) = n
    rw [Nat.mod_eq_of_lt hmod]
    omega

theorem leBytes_injective_of_lt {width n m : Nat}
    (hn : n < 256 ^ width) (hm : m < 256 ^ width)
    (h : leBytes width n = leBytes width m) : n = m := by
  have e := congrArg fromLE h
  rwa [fromLE_leBytes _ _ hn, fromLE_leBytes _ _ hm] at e

theorem byteArray_toList_length (b : ByteArray) : b.toList.length = b.size :=
  Wasm.ByteEncoding.byteArray_toList_length b

theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList :=
  Wasm.ByteEncoding.byteArray_toList_eq b

theorem byteArray_toList_injective {a b : ByteArray} (h : a.toList = b.toList) : a = b :=
  Wasm.ByteEncoding.byteArray_toList_injective h

theorem bytes_injective {a b : Bytes} (h : bytes a = bytes b) : a = b := by
  have e := congrArg (List.drop 4) h
  have hdrop (n : Nat) : (leBytes 4 n).drop 4 = [] :=
    List.drop_eq_nil_of_le (by simp only [leBytes_length]; exact Nat.le_refl _)
  simpa only [bytes, u32, List.drop_append, leBytes_length, Nat.sub_self,
    List.drop_zero, hdrop, List.nil_append] using e

theorem string_injective {a b : String} (h : string a = string b) : a = b := by
  apply String.toByteArray_inj.mp
  exact byteArray_toList_injective (bytes_injective h)

end WNear.Borsh
