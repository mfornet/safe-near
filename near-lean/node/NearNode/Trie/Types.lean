import Std.Data.HashMap
import NearNode.Primitives.TrieNode
import NearNode.Trie.Nibbles

/-!
# Trie vocabulary

Hashes as keys, the source of nodes, the record of reads (`TrieRecorder`) and the refcount
changes of an update (`TrieChanges`, `TrieRefcountAddition`, `TrieRefcountSubtraction`), at
nearcore `44f7ae6` (`core/store/src/trie/mod.rs`).
-/

namespace Near.Node

/-- Hash maps keyed by hash use the first eight bytes, which are uniform. -/
instance : Hashable CryptoHash where
  hash h :=
    (List.range 8).foldl (fun acc i => acc ||| (h.bytes.get! i).toUInt64 <<< (8 * i).toUInt64) 0

end Near.Node

namespace Near.Node.Trie

/-- `Trie::EMPTY_ROOT`. -/
def emptyRoot : CryptoHash :=
  CryptoHash.zero

/-- `TRIE_COSTS`: the memory usage of one node, per byte of encoded key, per byte of value. -/
def nodeCost : UInt64 :=
  50

def byteOfKey : UInt64 :=
  2

def byteOfValue : UInt64 :=
  1

/-- Where nodes and values are read from, by hash. -/
structure NodeSource where
  read : CryptoHash → Option ByteArray

/-- The nodes and values a computation read, by hash (`TrieRecorder`). -/
abbrev Recorder :=
  Std.HashMap CryptoHash ByteArray

namespace Recorder

/-- `PartialStorage`: the recorded values, sorted as bytes. -/
def partialState (r : Recorder) : Array ByteArray :=
  r.fold (fun acc _ v => acc.push v) #[] |>.qsort fun a b => Borsh.compareBytes a b == .lt

end Recorder

/-- `TrieRefcountAddition`: a node or value to store, with the references to add. -/
structure Addition where
  hash : CryptoHash
  data : ByteArray
  rc : UInt32
  deriving BEq, Inhabited

/-- `TrieRefcountSubtraction`. -/
structure Subtraction where
  hash : CryptoHash
  rc : UInt32
  deriving BEq, Inhabited

/-- `TrieChanges`: the new root and the refcount deltas, sorted by hash. -/
structure TrieChanges where
  oldRoot : CryptoHash
  newRoot : CryptoHash
  insertions : Array Addition
  deletions : Array Subtraction
  deriving BEq, Inhabited

/-- The hash as a hex string, for messages. -/
def hashHex (h : CryptoHash) : String :=
  h.bytes.foldl (fun s b => s ++ String.ofList (Nat.toDigits 16 (b.toNat + 256)).tail) ""

end Near.Node.Trie
