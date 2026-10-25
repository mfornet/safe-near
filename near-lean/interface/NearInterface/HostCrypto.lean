/-!
# Host cryptography

The cryptographic primitives behind the VM's `sha256`, `keccak256`, `keccak512`, `ripemd160`,
`ecrecover`, `ed25519_verify`, `p256_verify`, `alt_bn128_*` and `bls12381_*` host functions.
The VM validates the arguments and charges the gas of those host functions itself; what it asks a
`HostCrypto` for is only the primitive on arguments it has already checked, so the VM and the
contract specifications depend on no implementation of them. The node supplies the implementation
(`NearCrypto`) through `RuntimeConfig.hostCrypto`; without one the host functions are reported as
unsupported rather than answered with a placeholder.

The functions mirror the arguments of `near_vm_runner::logic::{alt_bn128, bls12381}`: an `Except`
is the VM's `InvalidInput` error (its message), and the `bls12381_*` functions take the behaviour
version (`0`, or `1` with `bls12381_not_in_group_fix`, NEP-488).
-/

namespace Wasm.Near

/-- The primitives of the cryptographic host functions. -/
structure HostCrypto where
  sha256 : List UInt8 → List UInt8
  keccak256 : List UInt8 → List UInt8
  keccak512 : List UInt8 → List UInt8
  ripemd160 : List UInt8 → List UInt8
  /-- `ecrecover hash signature v malleabilityFlag` for a 32-byte hash, a 64-byte signature,
  `v < 4`: the 64-byte public key, or `none` when the host function returns `0`. -/
  ecrecover : List UInt8 → List UInt8 → Nat → Bool → Option (List UInt8)
  /-- `ed25519Verify signature message publicKey` for a 64-byte signature and a 32-byte key. -/
  ed25519Verify : List UInt8 → List UInt8 → List UInt8 → Bool
  /-- `p256Verify signature message publicKey` for a 64-byte signature and a 33-byte key. -/
  p256Verify : List UInt8 → List UInt8 → List UInt8 → Bool
  altBn128G1Multiexp : List UInt8 → Except String (List UInt8)
  altBn128G1Sum : List UInt8 → Except String (List UInt8)
  altBn128PairingCheck : List UInt8 → Except String Bool
  /-- The `bls12381_*` functions: `none` is the return value `1`, the bytes are written to the
  register when it is `0`. -/
  bls12381P1Sum : Nat → List UInt8 → Except String (Option (List UInt8))
  bls12381P2Sum : Nat → List UInt8 → Except String (Option (List UInt8))
  bls12381G1Multiexp : Nat → List UInt8 → Except String (Option (List UInt8))
  bls12381G2Multiexp : Nat → List UInt8 → Except String (Option (List UInt8))
  bls12381MapFpToG1 : Nat → List UInt8 → Except String (Option (List UInt8))
  bls12381MapFp2ToG2 : Nat → List UInt8 → Except String (Option (List UInt8))
  bls12381P1Decompress : Nat → List UInt8 → Except String (Option (List UInt8))
  bls12381P2Decompress : Nat → List UInt8 → Except String (Option (List UInt8))
  /-- The value `bls12381_pairing_check` returns: `0`, `1` or `2`. -/
  bls12381PairingCheck : List UInt8 → Except String Nat

end Wasm.Near
