import NearRuntime.TrieAccounting
import NearRuntime.Sha256

/-! Canonical raw-trie construction at the pinned near-store boundary. Native
TRIE_COSTS are 50 per node, 2 per encoded key byte and 1 per value byte;
values additionally carry one node cost, including values stored in leaves. -/
namespace Near.TrieConstruction
open TrieAccounting

private def little (count value : Nat) : Bytes :=
  (List.range count).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

private def vector (bytes : Bytes) : Bytes := little 4 bytes.length ++ bytes

private def pack : List Nat → Bytes
  | [] => []
  | [a] => [UInt8.ofNat (16 * a)]
  | a :: b :: rest => UInt8.ofNat (16 * a + b) :: pack rest

def encodePath (leaf : Bool) (path : List Nat) : Bytes :=
  let flag := if leaf then 32 else 0
  if path.length % 2 == 0 then UInt8.ofNat flag :: pack path
  else UInt8.ofNat (flag + 16 + path.head!) :: pack path.tail

private def refBytes (value : Bytes) : Bytes := little 4 value.length ++ Sha256.hash value

structure Built where
  root : Hash
  memoryUsage : Nat
  witness : Witness
  deriving Repr

private def finish (node : Bytes) (usage : Nat) (objects : Witness) : Except String Built := do
  if usage ≥ 2 ^ 64 then throw "trie subtree size exceeds u64"
  let bytes := node ++ little 8 usage
  let root := Sha256.hash bytes
  return { root, memoryUsage := usage, witness := (root, bytes) :: objects }

private def common : List Nat → List Nat → List Nat
  | a :: as, b :: bs => if a == b then a :: common as bs else []
  | _, _ => []

/-- Canonical compressed hexary trie. Fuel bounds depth by the largest nibble
key plus one; it is not an execution approximation or a native node input. -/
private def construct : Nat → List (List Nat × Bytes) → Except String Built
  | 0, _ => .error "trie construction depth exhausted"
  | fuel + 1, entries => do
    match entries with
    | [] => return { root := List.replicate 32 0, memoryUsage := 0, witness := [] }
    | [(path, value)] =>
      let encoded := encodePath true path
      if encoded.length ≥ 2 ^ 32 then throw "trie compact path exceeds u32"
      finish ([0] ++ vector encoded ++ refBytes value) (100 + 2 * encoded.length + value.length)
        [(Sha256.hash value, value)]
    | first :: rest =>
      let shared := rest.foldl (fun path entry => common path entry.1) first.1
      if !shared.isEmpty then
        let child ← construct fuel (entries.map fun (key, value) => (key.drop shared.length, value))
        let encoded := encodePath false shared
        if encoded.length ≥ 2 ^ 32 then throw "trie compact path exceeds u32"
        finish ([3] ++ vector encoded ++ child.root) (50 + 2 * encoded.length + child.memoryUsage) child.witness
      else
        let value := ((entries.find? (·.1.isEmpty)).map (·.2))
        let mut mask := 0
        let mut hashes : Bytes := []
        let mut objects : Witness := []
        let mut usage := 50
        for nibble in [0:16] do
          let group := entries.filter (fun entry => entry.1.head? == some nibble)
          if !group.isEmpty then
            let child ← construct fuel (group.map fun (key, value) => (key.tail, value))
            mask := mask + 2 ^ nibble
            hashes := hashes ++ child.root
            objects := objects ++ child.witness
            usage := usage + child.memoryUsage
        let mut header : Bytes := [1]
        if let some value := value then
          usage := usage + 50 + value.length
          objects := (Sha256.hash value, value) :: objects
          header := [2] ++ refBytes value
        finish (header ++ little 2 mask ++ hashes) usage objects

/-- Construct the canonical root and all objects directly from raw state.
No native root, witness, path or accounting observations enter this function. -/
def build (entries : List (Bytes × Bytes)) : Except String Built := do
  let keys := entries.map Prod.fst
  if keys.eraseDups.length != keys.length then throw "duplicate trie entry"
  if entries.any (fun (key, value) => key.length ≥ 2 ^ 32 || value.length ≥ 2 ^ 32) then
    throw "trie key or value exceeds u32"
  let entries := entries.map fun (key, value) => (nibbles key, value)
  let depth := entries.foldl (fun n entry => max n entry.1.length) 0 + 1
  let built ← construct depth entries
  let mut unique : Witness := []
  for (hash, bytes) in built.witness do
    match unique.find? (·.1 == hash) with
    | none => unique := unique ++ [(hash, bytes)]
    | some (_, previous) =>
      if previous != bytes then throw "trie object hash collision"
  return { built with witness := unique }

end Near.TrieConstruction
