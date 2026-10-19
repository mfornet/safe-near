import Init.Omega

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

end WNear.Borsh
