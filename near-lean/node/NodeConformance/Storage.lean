import NodeConformance.Runner
import NearNode.Primitives

/-!
The M4a part of the registry of `node-conformance-types`: the storage-layer types.
-/

open Near.Node Near.Node.Conformance Near.Node.Borsh

/-- `TrieKey` also parses back from the oracle's `to_vec` bytes. -/
private def checkTrieKey : Check := fun line =>
  (check TrieKey (fun k => [("key", k.toVec)]) line).orElse fun _ =>
    if line.reject then none
    else
      match line.hashes.lookup "key", Codec.decodeAll (α := TrieKey) line.borsh with
      | some (some hex), .ok k =>
        match ofHex hex with
        | some raw =>
          if raw.isEmpty then none
          else if TrieKey.parse? raw == some k then none else some "parse of the key differs"
        | none => some "key is not hex"
      | _, _ => none

private def nodeHashes (n : RawTrieNodeWithSize) : List (String × ByteArray) :=
  [("hash", (CryptoHash.hashBorsh n).bytes)]

/-- Every storage fixture type with its check. -/
def storageRegistry : List (String × Check) :=
  [("TrieKey", checkTrieKey), ("ValueRef", check ValueRef fun v => [("hash", v.hash.bytes)]),
    ("FlatStateValue",
      check FlatStateValue fun v =>
        [("hash", v.toValueRef.hash.bytes), ("length", Codec.encode v.toValueRef.length)]),
    ("StateChangeCause", check StateChangeCause), ("RawStateChange", check RawStateChange),
    ("RawStateChangesWithTrieKey", check RawStateChangesWithTrieKey),
    ("StateChangesForShard", check StateChangesForShard),
    ("StateChangesForBlock", check StateChangesForBlock),
    ("StateChangesForBlockRange", check StateChangesForBlockRange),
    ("RawTrieNodeWithSize", check RawTrieNodeWithSize nodeHashes)]
