import Binary.Bytes

/-!
# The size of `contract.wasm`

The deployed binary is 185625 bytes: the `size` the boundary charges
contract loading for, and the bound the gas proofs assume.
-/

namespace WNear.Binary

theorem wNearBytes_size : wNearBytes.size = 185625 := by
  rw [wNearBytes, Wasm.ByteSource.size_toBytes]
  rfl

end WNear.Binary
