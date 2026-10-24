import NearNode.Primitives.Action

/-!
# Transactions

`near-primitives::transaction` at `=0.37.4`: `Transaction` (V0 and V1),
`SignedTransaction` and its hash.
-/

namespace Near.Node

open Borsh

/-- `NonceMode`: how the nonce is checked against the access key nonce. -/
inductive NonceMode where
  | monotonic
  | strict
  deriving BEq, Inhabited

instance : Codec NonceMode :=
  .enum "NonceMode" [.const 0 .monotonic, .const 1 .strict]

/-- `TransactionV0`. -/
structure TransactionV0 where
  signerId : AccountId
  publicKey : PublicKey
  nonce : Nonce
  receiverId : AccountId
  blockHash : CryptoHash
  actions : Array Action
  deriving BEq, Inhabited

instance : Codec TransactionV0 :=
  .iso (AccountId × PublicKey × Nonce × AccountId × CryptoHash × Array Action)
    (fun (s, k, n, r, b, a) => ⟨s, k, n, r, b, a⟩) fun x =>
    (x.signerId, x.publicKey, x.nonce, x.receiverId, x.blockHash, x.actions)

/-- `TransactionV1`: gas key nonces and a nonce mode. -/
structure TransactionV1 where
  signerId : AccountId
  publicKey : PublicKey
  nonce : TransactionNonce
  receiverId : AccountId
  blockHash : CryptoHash
  actions : Array Action
  nonceMode : NonceMode
  deriving BEq, Inhabited

instance : Codec TransactionV1 :=
  .iso
    (AccountId × PublicKey × TransactionNonce × AccountId × CryptoHash × Array Action × NonceMode)
    (fun (s, k, n, r, b, a, m) => ⟨s, k, n, r, b, a, m⟩) fun x =>
    (x.signerId, x.publicKey, x.nonce, x.receiverId, x.blockHash, x.actions, x.nonceMode)

/-- `Transaction`. V0 has no tag. V1 is `1` followed by `TransactionV1`; the decoder tells
them apart by the second byte, which is the high byte of a V0 account id length (always 0). -/
inductive Transaction where
  | v0 (t : TransactionV0)
  | v1 (t : TransactionV1)
  deriving BEq, Inhabited

instance : Codec Transaction :=
  let c0 : Codec TransactionV0 := inferInstance
  let c1 : Codec TransactionV1 := inferInstance
  { spec :=
      { enc := fun
          | .v0 t => c0.spec.enc t
          | .v1 t => 1 :: c1.spec.enc t
        dec := fun l =>
          match l with
          | u1 :: u2 :: _ =>
            if u2 == 0 then do
              let (t, r) ← c0.spec.dec l
              pure (.v0 t, r)
            else
              if u1 == 1 then do
                let (t, r) ← c1.spec.dec (l.drop 1)
                pure (.v1 t, r)
              else throw (.tag "Transaction" u1.toNat)
          | _ => throw .eof }
    impl :=
      { put := fun
          | .v0 t, d => c0.impl.put t d
          | .v1 t, d => c1.impl.put t (d.push 1)
        get := fun d p =>
          if p + 2 ≤ d.size then
            if d[p + 1]! == 0 then (c0.impl.get d p).map .v0
            else
              if d[p]! == 1 then (c1.impl.get d (p + 1)).map .v1
              else .err (.tag "Transaction" d[p]!.toNat)
          else .err .eof } }

namespace Transaction

/-- The signed message: the hash of the Borsh encoding. -/
def hash (t : Transaction) : CryptoHash :=
  CryptoHash.hashBorsh t

end Transaction

/-- `SignedTransaction`. The cached hash and size are not on the wire. -/
structure SignedTransaction where
  transaction : Transaction
  signature : Signature
  deriving BEq, Inhabited

instance : Codec SignedTransaction :=
  .iso (Transaction × Signature) (fun (t, s) => ⟨t, s⟩) fun x => (x.transaction, x.signature)

/-- The transaction hash (`SignedTransaction::get_hash`). -/
def SignedTransaction.hash (t : SignedTransaction) : CryptoHash :=
  t.transaction.hash

end Near.Node
