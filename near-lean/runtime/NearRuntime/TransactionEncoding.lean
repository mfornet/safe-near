import NearRuntime.ReceiptEncoding
import NearRuntime.TransactionSize

/-! Native ordinary-key transaction bodies, before signatures. Block hashes
are explicit original inputs: receipt identity cannot be recovered from a model
counter, nonce or execution block height alone. -/
namespace Near.TransactionEncoding

open EncodingPrimitives

private def account (id : AccountId) : Except String Bytes := do
  let bytes := id.toUTF8.toList
  unless Wasm.Near.validAccountIdBytes bytes do throw "invalid transaction account id"
  vector bytes

/-- V0 is untagged. V1 adds the transaction tag, ordinary nonce tag and trailing
nonce mode. Signature bytes are not part of the signed transaction hash. -/
def encode (codes : List (String × Bytes)) (blockHash : NativeIdentity.Hash)
    (tx : Transaction) : Except String Bytes := do
  unless tx.version ≤ 1 do throw "unsupported transaction envelope tag"
  unless tx.version == 1 || tx.nonceMode == .monotonic do throw "V0 transactions have no strict nonce mode"
  let blockHash ← NativeIdentity.checkedHash blockHash
  let key ← StateEncoding.publicKey tx.publicKey
  let nonce ← unsigned 8 tx.nonce
  let actions ← tx.actions.mapM (ReceiptEncoding.action codes)
  let count ← unsigned 4 actions.length
  let nonce := if tx.version == 1 then [0] ++ nonce else nonce
  let body := (if tx.version == 1 then [1] else []) ++ (← account tx.signerId) ++ key ++ nonce ++
    (← account tx.receiverId) ++ blockHash ++ count ++ actions.flatten ++
    (if tx.version == 1 then [if tx.nonceMode == .strict then 1 else 0] else [])
  unless body.length == tx.bodySize do throw "transaction encoding disagrees with modeled body size"
  return body

def hash (codes : List (String × Bytes)) (blockHash : NativeIdentity.Hash) (tx : Transaction) :
    Except String NativeIdentity.Hash := do
  return Sha256.hash (← encode codes blockHash tx)

end Near.TransactionEncoding
