import NearNode.Network.Types
import NearCrypto.Ed25519
import Lean.Data.Json

/-!
# Node keys

The key a node signs its edges and routed messages with (`node_key.json` of nearcore): an Ed25519
`SecretKey` is written `ed25519:` and the base58 of the 64 bytes seed and public key; a `PublicKey`
likewise with its 32 bytes. This is also the `PeerId` of the node.
-/

namespace Near.Node.Network

open Near.Node

/-- The Bitcoin base58 alphabet. -/
private def alphabet : String :=
  "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

/-- Decodes base58 text; `none` on a character outside the alphabet. -/
def base58Decode? (s : String) : Option ByteArray := do
  let digits := alphabet.toList
  let mut n : Nat := 0
  let mut zeros := 0
  let mut leading := true
  for c in s.toList do
    let i ← digits.findIdx? (· == c)
    if leading && i == 0 then
      zeros := zeros + 1
    else
      leading := false
    n := n * 58 + i
  let mut out : List UInt8 := []
  while n > 0 do
    out := (n % 256).toUInt8 :: out
    n := n / 256
  pure (ByteArray.mk (Array.replicate zeros 0 ++ out.toArray))

/-- Base58 text of bytes. -/
def base58Encode (b : ByteArray) : String :=
  Id.run do
    let digits := alphabet.toList.toArray
    let mut n := b.foldl (fun n x => n * 256 + x.toNat) 0
    let mut out : List Char := []
    while n > 0 do
      out := digits[n % 58]! :: out
      n := n / 58
    let zeros := (b.toList.takeWhile (· == 0)).length
    return String.ofList (List.replicate zeros '1' ++ out)

/-- `ed25519:` and the base58 of the key bytes. -/
def PublicKey.toText : PublicKey → String
  | .ed25519 k => "ed25519:" ++ base58Encode k
  | .secp256k1 k => "secp256k1:" ++ base58Encode k
  | .mldsa65 k => "mldsa65:" ++ base58Encode k

/-- Parses `ed25519:<base58>`; other key types are not node keys. -/
def PublicKey.parse? (s : String) : Option PublicKey := do
  let body ← s.dropPrefix? "ed25519:"
  let k ← base58Decode? body.toString
  if k.size == 32 then
    some (.ed25519 k)
  else
    none

/-- A node's Ed25519 key. -/
structure NodeKey where
  signing : NearCrypto.Ed25519.Impl.SigningKey
  deriving Inhabited

namespace NodeKey

/-- The public key of the node, as a peer id. -/
def peerId (k : NodeKey) : PeerId :=
  ⟨.ed25519 k.signing.publicKey⟩

/-- The 64 bytes `seed ++ public key` text `ed25519:...` of `near_crypto::SecretKey`. -/
def parse? (s : String) : Option NodeKey := do
  let body ← s.dropPrefix? "ed25519:"
  let pair ← base58Decode? body.toString
  let signing ← NearCrypto.Ed25519.Impl.SigningKey.ofKeypair pair
  pure ⟨signing⟩

/-- A key from a 32-byte seed. -/
def ofSeed? (seed : ByteArray) : Option NodeKey :=
  (NearCrypto.Ed25519.Impl.SigningKey.ofSeed seed).map fun s => ⟨s⟩

/-- Signs with the key: `SecretKey::sign`. -/
def sign (k : NodeKey) (data : ByteArray) : Signature :=
  .ed25519 (k.signing.sign data)

/-- `PartialEdgeInfo::new`: the node signs the hash of the edge between itself and `peer`. -/
def partialEdge (k : NodeKey) (peer : PeerId) (nonce : UInt64) : PartialEdgeInfo :=
  ⟨nonce, k.sign (Edge.buildHash k.peerId peer nonce).bytes⟩

/-- A key read from a `node_key.json`: its `secret_key` field. -/
def ofJson? (j : Lean.Json) : Option NodeKey :=
  match j.getObjValAs? String "secret_key" with
  | .ok s => parse? s
  | .error _ => none

end NodeKey

end Near.Node.Network
