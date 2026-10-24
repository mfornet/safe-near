import NearInterface.HostCrypto
import NearInterface.Config
import NearCrypto.Sha256
import NearCrypto.Keccak
import NearCrypto.Ripemd160
import NearCrypto.Ed25519
import NearCrypto.Secp256k1
import NearCrypto.P256
import NearCrypto.Bn254
import NearCrypto.Bls12381

/-! The cryptography of the VM's host functions (`sha256`, `keccak256`, `keccak512`, `ripemd160`,
`ecrecover`, `ed25519_verify`, `p256_verify`, `alt_bn128_*`, `bls12381_*`), supplied to the VM as
`RuntimeConfig.hostCrypto`. The VM validates arguments, charges gas and raises its errors itself;
these are the `NearCrypto` primitives on arguments it has checked. The fast (`Impl`) versions run.
`bls12381_not_in_group_fix` is protocol configuration: the VM passes the version.
nearcore divergence: the messages of `alt_bn128` errors for an invalid point are those of
`NearCrypto` and omit the offending bytes nearcore prints. -/
namespace ChainReplay.HostCrypto

open Wasm.Near

private def toBytes (bytes : List UInt8) : ByteArray := ⟨bytes.toArray⟩

private def ofBytes (bytes : ByteArray) : List UInt8 := bytes.toList

/-- The host functions' primitives, from `NearCrypto`. -/
def hostCrypto : HostCrypto where
  sha256 m := ofBytes (NearCrypto.sha256 (toBytes m))
  keccak256 m := ofBytes (NearCrypto.keccak256 (toBytes m))
  keccak512 m := ofBytes (NearCrypto.keccak512 (toBytes m))
  ripemd160 m := ofBytes (NearCrypto.ripemd160 (toBytes m))
  ecrecover hash sig v malleability :=
    (NearCrypto.ecrecover (toBytes hash) (toBytes sig) v malleability).map ofBytes
  ed25519Verify sig msg key :=
    NearCrypto.ed25519Verify (toBytes key) (toBytes msg) (toBytes sig)
  p256Verify sig msg key :=
    match NearCrypto.P256.Impl.verify (toBytes sig) (toBytes msg) (toBytes key) with
    | .ok verified => verified
    | .error _ => false
  altBn128G1Multiexp data :=
    (NearCrypto.Bn254.g1Multiexp NearCrypto.Bn254.Impl.ops (toBytes data)).map ofBytes
  altBn128G1Sum data :=
    (NearCrypto.Bn254.g1Sum NearCrypto.Bn254.Impl.ops (toBytes data)).map ofBytes
  altBn128PairingCheck data :=
    NearCrypto.Bn254.pairingCheck NearCrypto.Bn254.Impl.ops (toBytes data)
  bls12381P1Sum version data :=
    (NearCrypto.Bls12381.p1Sum NearCrypto.Bls12381.Impl.ops version (toBytes data)).map (·.map ofBytes)
  bls12381P2Sum version data :=
    (NearCrypto.Bls12381.p2Sum NearCrypto.Bls12381.Impl.ops version (toBytes data)).map (·.map ofBytes)
  bls12381G1Multiexp version data :=
    (NearCrypto.Bls12381.g1Multiexp NearCrypto.Bls12381.Impl.ops version (toBytes data)).map
      (·.map ofBytes)
  bls12381G2Multiexp version data :=
    (NearCrypto.Bls12381.g2Multiexp NearCrypto.Bls12381.Impl.ops version (toBytes data)).map
      (·.map ofBytes)
  bls12381MapFpToG1 _ data :=
    (NearCrypto.Bls12381.mapFpToG1 NearCrypto.Bls12381.Impl.ops (toBytes data)).map (·.map ofBytes)
  bls12381MapFp2ToG2 _ data :=
    (NearCrypto.Bls12381.mapFp2ToG2 NearCrypto.Bls12381.Impl.ops (toBytes data)).map (·.map ofBytes)
  bls12381P1Decompress version data :=
    (NearCrypto.Bls12381.p1Decompress NearCrypto.Bls12381.Impl.ops version (toBytes data)).map
      (·.map ofBytes)
  bls12381P2Decompress version data :=
    (NearCrypto.Bls12381.p2Decompress NearCrypto.Bls12381.Impl.ops version (toBytes data)).map
      (·.map ofBytes)
  bls12381PairingCheck data :=
    NearCrypto.Bls12381.pairingCheck NearCrypto.Bls12381.Impl.ops (toBytes data)

/-- `RuntimeConfig.load` with the host functions' cryptography installed. -/
def loadConfig (directory : System.FilePath) (protocol : Nat) : IO RuntimeConfig := do
  pure { (← RuntimeConfig.load directory protocol) with hostCrypto := some hostCrypto }

end ChainReplay.HostCrypto
