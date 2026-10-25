import NearRuntime.Fees

namespace Near

mutual
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
  | .deployGlobalContract code _ => 1 + 4 + code.size + 1
  | .transferToGasKey key _ | .withdrawFromGasKey key _ => 1 + key.length + 16
  | .delegate sender receiver actions _ nonceIndex _ key signature v2 =>
    -- The delegate action, its public key and signature; V2 adds the payload version and a
    -- tagged nonce.
    (if v2 then 2 else 1) + (4 + sender.utf8ByteSize) + (4 + receiver.utf8ByteSize) + 4
      + Action.borshSizeList actions + (if v2 then 1 + 8 + (if nonceIndex.isSome then 2 else 0) else 8)
      + 8 + key.length + signature.length

def Action.borshSizeList : List Action → Nat
  | [] => 0
  | a :: rest => a.borshSize + Action.borshSizeList rest
end

/-- V0 has no transaction tag. Ordinary-key V1 adds transaction/nonce tags and nonce mode.
Block hashes have fixed 32-byte encoding and nonce values have fixed 8-byte encoding. -/
def Transaction.bodySize (tx : Transaction) : Nat :=
  4 + tx.signerId.utf8ByteSize + tx.publicKey.length + 8 + 4 + tx.receiverId.utf8ByteSize + 32 + 4 +
    Action.borshSizeList tx.actions + (if tx.version == 1 then 3 else 0)

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
