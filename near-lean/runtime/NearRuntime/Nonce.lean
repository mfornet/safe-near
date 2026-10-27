import NearRuntime.Types
import NearVM.Config

namespace Near

open Wasm.Near

/-- V0 has no nonce-mode field; V1 ordinary-key transactions use the native
GasKeys envelope gate even when they request monotonic nonces. -/
def Transaction.versionSupported (tx : Transaction) (cfg : RuntimeConfig) : Bool :=
  (tx.version == 0 && tx.nonceMode == .monotonic) ||
    (tx.version == 1 && cfg.v1TransactionsEnabled)

/-- Saturating u64 nonce ceiling from pinned `verifier::verify_nonce`. -/
def nonceUpperBound (height : Nat) : Nat := min (height * 1_000_000) (2 ^ 64 - 1)

/-- The actual nonce predicate, including the reference's error precedence.
`none` is the mempool-style check without a known block height. Apply always
uses `some height`. The wire adapter checks all numeric inputs fit u64. -/
def verifyNonce (nonce current : Nat) (height : Option Nat) (mode : NonceMode) :
    Except RuntimeError Unit := do
  match mode with
  | .monotonic =>
    if nonce ≤ current then throw (.invalidNonce nonce current)
  | .strict =>
    if !(current < 2 ^ 64 - 1 ∧ nonce = current + 1) then throw (.invalidNonce nonce current)
  if let some height := height then
    let upper := nonceUpperBound height
    if nonce ≥ upper then throw (.nonceTooLarge nonce upper)

end Near
