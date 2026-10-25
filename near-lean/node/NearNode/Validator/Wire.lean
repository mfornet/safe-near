import NearNode.Network.Message
import NearNode.Network.Keys
import NearNode.Validator.Signer

/-!
# What a validator sends over the wire

* **Account data.** `send_message_to_account` finds the peer of an account in the `AccountData` that
  the validator itself signs and spreads (`SyncAccountsData`): its peer id, its proxies (none: the
  localnet needs no tier 1 connection, a message to an account goes over the connection to the peer)
  and a version. The payload is the protobuf `AccountKeyPayload` of `AccountData`, signed with the
  validator key (`AccountData::sign`).
* **Routed messages.** A message for a validator is a `Routed` message addressed to the peer id of
  the connection, signed with the node key.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Network Near.Node.Borsh

/-- `AccountData::sign`: the validator key signs the serialized payload. -/
def signAccountData (s : Signer) (peer : NodeKey) (version : UInt64) (secs : Int) : SignedAccountData :=
  let data : AccountData :=
    { peerId := peer.peerId, accountKey := s.publicKey, proxies := #[], version,
      timestamp := ⟨secs, 0⟩ }
  let payload := encodeAccountDataPayload data
  ⟨data, ⟨payload, s.sign payload⟩⟩

/-- The `SyncAccountsData` that announces the validator. -/
def announce (s : Signer) (peer : NodeKey) (version : UInt64) (secs : Int) : PeerMessage :=
  .syncAccountsData ⟨#[signAccountData s peer version secs], true, false⟩

/-- A routed message from this node to `target`. -/
def routedTo (key : NodeKey) (target : PeerId) (body : RoutedBody) (now : Nat) : PeerMessage :=
  let t := PeerIdOrHash.peerId target
  let author := key.peerId
  let hash := CryptoHash.hashBorsh (t, author, body)
  .routed
    { target := t, author, ttl := 100, body, signature := some (key.sign hash.bytes),
      createdAt := some now, numHops := 0 }

end Near.Node.Validator
