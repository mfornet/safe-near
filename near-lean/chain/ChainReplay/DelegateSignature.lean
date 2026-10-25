import NearRuntime.ReceiptEncoding
import NearCrypto.Ed25519
import NearCrypto.Secp256k1

/-! The signature check of a delegate action (`SignedDelegateAction::verify`), supplied to the
runtime as `ApplyState.verifyDelegate`. The runtime hashes nothing itself: the signed message is the
NEP-461 prefix (`2^30 + 366` for `DelegateAction`, `2^30 + 611` for `DelegateActionV2`) followed by
the Borsh of the delegate action, hashed with SHA-256 and verified under the action's own key.
nearcore divergence: only Ed25519 and secp256k1 keys verify; a delegate action under any other key
family (ML-DSA) is reported as having an invalid signature, because `NearCrypto` has no verifier
for it. -/
namespace ChainReplay.DelegateSignature

open Near

private def littleEndian32 (value : Nat) : Bytes :=
  (List.range 4).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

/-- The 32-byte message a delegate action's signature covers. -/
def signedHash (codes : List (String × Bytes)) (action : Action) (v2 : Bool) : Option Bytes :=
  match ReceiptEncoding.delegatePayload codes action with
  | .error _ => none
  | .ok payload =>
    some (Sha256.hash (littleEndian32 (2 ^ 30 + if v2 then 611 else 366) ++ payload))

/-- `near_crypto::Signature::verify` for the key families a signed delegate action can use. -/
def verifyBytes (hash key signature : Bytes) : Bool :=
  match key, signature with
  | 0 :: key, 0 :: signature =>
    NearCrypto.Ed25519.Impl.verify ⟨key.toArray⟩ ⟨hash.toArray⟩ ⟨signature.toArray⟩
  | 1 :: key, 1 :: signature =>
    NearCrypto.Secp256k1.Impl.verify ⟨key.toArray⟩ ⟨hash.toArray⟩ ⟨signature.toArray⟩
  | _, _ => false

/-- `ApplyState.verifyDelegate` for the nodes' catalogue of code. Anything but a delegate action
verifies trivially, since the runtime only asks about delegate actions. -/
def verify (codes : List (String × Bytes)) : Action → Bool
  | action@(.delegate _ _ _ _ _ _ key signature v2) =>
    match signedHash codes action v2 with
    | none => false
    | some hash => verifyBytes hash key signature
  | _ => true

end ChainReplay.DelegateSignature
