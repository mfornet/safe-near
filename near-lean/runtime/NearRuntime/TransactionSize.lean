import NearRuntime.Fees

namespace Near

/-- Size of the modeled native Borsh action encodings, including enum tags. -/
def Action.borshSize : Action → Nat
  | .createAccount => 1
  | .deployContract code => 1 + 4 + code.size
  | .functionCall method args _ _ => 1 + 4 + method.utf8ByteSize + 4 + args.length + 8 + 16
  | .transfer _ => 1 + 16
  | .stake _ key => 1 + 16 + key.length
  | .addKey key access => 1 + accessKeyStorageBytes key access
  | .deleteKey key => 1 + key.length
  | .deleteAccount beneficiary => 1 + 4 + beneficiary.utf8ByteSize
  | .useGlobalContract (.codeHash _) => 1 + 1 + 32
  | .useGlobalContract (.accountId id) => 1 + 1 + 4 + id.length

/-- V0 has no transaction tag. Ordinary-key V1 adds transaction/nonce tags and nonce mode.
Block hashes have fixed 32-byte encoding and nonce values have fixed 8-byte encoding. -/
def Transaction.bodySize (tx : Transaction) : Nat :=
  4 + tx.signerId.utf8ByteSize + tx.publicKey.length + 8 + 4 + tx.receiverId.utf8ByteSize + 32 + 4 +
    (tx.actions.map Action.borshSize).sum + (if tx.version == 1 then 3 else 0)

/-- Ordinary signature schemes have fixed Borsh widths. Unknown/malformed key
encodings are a model limitation, never silently assigned a signature width. -/
def Transaction.signatureSize? (tx : Transaction) : Option Nat :=
  match tx.publicKey with
  | 0 :: bytes => if bytes.length == 32 then some 65 else none
  | 1 :: bytes => if bytes.length == 64 then some 66 else none
  | _ => none

/-- Source-derived PostQuantumSignatures gate chooses body-only versus full wire size. -/
def Transaction.sizeForLimits? (tx : Transaction) (cfg : Wasm.Near.RuntimeConfig) : Option Nat := do
  let signature ← tx.signatureSize?
  return tx.bodySize + if cfg.transactionSizeIncludesSignature then signature else 0

end Near
