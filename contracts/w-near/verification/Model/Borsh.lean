import NearSdk
import Wasm.Bytes

/-!
# Borsh encoding (the fragment used by wNEAR)

The encoders that describe the on-chain layout of the contract state come from
the shared `NearSdk` library; the lemmas about `String`'s UTF-8 bytes, which
need the Wasm byte facts, stay here.
-/

namespace WNear.Borsh

export NearSdk.Borsh (Bytes leBytes u32 u64 u128 bytes string leBytes_length fromLE fromLE_leBytes
  leBytes_injective_of_lt bytes_injective)

theorem byteArray_toList_length (b : ByteArray) : b.toList.length = b.size :=
  Wasm.ByteEncoding.byteArray_toList_length b

theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList :=
  Wasm.ByteEncoding.byteArray_toList_eq b

theorem byteArray_toList_injective {a b : ByteArray} (h : a.toList = b.toList) : a = b :=
  Wasm.ByteEncoding.byteArray_toList_injective h

theorem string_injective {a b : String} (h : string a = string b) : a = b := by
  apply String.toByteArray_inj.mp
  exact byteArray_toList_injective (bytes_injective h)

end WNear.Borsh
