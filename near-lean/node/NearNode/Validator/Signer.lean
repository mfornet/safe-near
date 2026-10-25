import NearNode.Primitives
import NearNode.Network.Keys
import NearCrypto.Vrf

/-!
# The validator signer

`near_primitives::validator_signer::ValidatorSigner` (`InMemoryValidatorSigner`): the account of the
validator and its Ed25519 key, from `validator_key.json` (`account_id`, `public_key`,
`secret_key`). `sign_bytes` signs the bytes given; every signed message of a validator is the
signature over a hash or over the Borsh of an `inner` part.

**Not constant time.** `NearCrypto.Ed25519.Impl.SigningKey.sign` branches on secret data (see the
M2 notes); a node that signs on a hostile network needs a hardened signer.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Network Borsh

structure Signer where
  accountId : AccountId
  key : NodeKey
  /-- The 32-byte seed of the secret key, from which the VRF key derives. -/
  seed : ByteArray
  deriving Inhabited

namespace Signer

def publicKey (s : Signer) : PublicKey :=
  s.key.peerId.key

/-- `ValidatorSigner::sign_bytes`. -/
def sign (s : Signer) (data : ByteArray) : Signature :=
  s.key.sign data

/-- A signer from the secret key text `ed25519:...` of the 64 bytes. -/
def ofSecret? (account : String) (secret : String) : Option Signer := do
  guard (AccountId.isValid account)
  let key ← NodeKey.parse? secret
  let body ← secret.dropPrefix? "ed25519:"
  let pair ← base58Decode? body.toString
  pure ⟨⟨account⟩, key, pair.extract 0 32⟩

/-- `validator_key.json`: `account_id`, `public_key`, `secret_key`. -/
def ofJson? (j : Lean.Json) : Option Signer := do
  let account ← (j.getObjValAs? String "account_id").toOption
  let secret ← (j.getObjValAs? String "secret_key").toOption
  ofSecret? account secret

/-- `compute_vrf_with_proof`'s key: `convert_secret_key` of the seed. -/
def vrfKey (s : Signer) : Option NearCrypto.Vrf.Impl.SecretKey :=
  NearCrypto.Vrf.Impl.SecretKey.ofSeed s.seed

end Signer

end Near.Node.Validator
