import NearNode.Primitives

/-!
# Fields of a transaction

`Transaction` is a V0 or a V1; these are the fields both have, as `Transaction::signer_id` and the
other accessors of `near-primitives` give them, and the size that counts against the limits of a chunk.
-/

namespace Near.Node

open Near.Node Near.Node.Borsh

namespace Transaction

def signerId : Transaction → AccountId
  | .v0 t => t.signerId
  | .v1 t => t.signerId

def receiverId : Transaction → AccountId
  | .v0 t => t.receiverId
  | .v1 t => t.receiverId

def publicKey : Transaction → PublicKey
  | .v0 t => t.publicKey
  | .v1 t => t.publicKey

def blockHash : Transaction → CryptoHash
  | .v0 t => t.blockHash
  | .v1 t => t.blockHash

def actions : Transaction → Array Action
  | .v0 t => t.actions
  | .v1 t => t.actions

/-- The nonce and, for a gas key, the index of its lane. -/
def nonce : Transaction → TransactionNonce
  | .v0 t => .nonce t.nonce
  | .v1 t => t.nonce

def nonceValue (t : Transaction) : Nonce :=
  match t.nonce with
  | .nonce n | .gasKeyNonce n _ => n

def nonceIndex (t : Transaction) : Option NonceIndex :=
  match t.nonce with
  | .nonce _ => none
  | .gasKeyNonce _ i => some i

def isStrict : Transaction → Bool
  | .v0 _ => false
  | .v1 t => t.nonceMode == .strict

end Transaction

/-- The size that counts against the pool and the chunk limits (`SignedTransaction::wire_size`,
which is `size_for_limits` from the protocol feature `PostQuantumSignatures`, so at protocol 86). -/
def SignedTransaction.wireSize (t : SignedTransaction) : Nat :=
  (Codec.encode t).size

end Near.Node
