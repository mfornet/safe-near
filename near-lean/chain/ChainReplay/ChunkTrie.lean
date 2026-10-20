import NearRuntime.QueueEncoding
import NearVM.TrieOverlay

/-! Complete synthetic single-shard chunk state. The scheduler transition follows
runtime/runtime/src/bandwidth_scheduler/{mod,scheduler}.rs at the pinned revision.
For protocols 83–86 max_shard_bandwidth = max_allowance = 4,500,000 and
max_base_bandwidth = 100,000 (parameters v74). Empty requests grant only base
bandwidth against allowance; distributing the remainder does not debit it.
No generated native state, access counts or gas enters this construction. -/
namespace ChainReplay.ChunkTrie
open Near

private def little (width value : Nat) : Bytes :=
  (List.range width).map fun i => UInt8.ofNat (value / 2 ^ (8 * i) % 256)

structure Input where
  linkAllowed : Bool := true
  /-- Highest requested total on the single link; base grant if there is none. -/
  requested : Nat := 100000
  deriving Inhabited

private def number (bytes : Bytes) : Nat :=
  bytes.foldr (fun byte rest => byte.toNat + 256 * rest) 0

/-- Decode original external scheduler inputs, never generated scheduler state.
The oracle's epoch provider fixes the layout to shard zero. -/
def input (congestion : List (Nat × Bytes × Nat)) (requests : Bytes) : Except String Input := do
  unless (congestion.map (·.1)).eraseDups.length == congestion.length do
    throw "duplicate congestion shard"
  let mut allowed := false
  for (shard, bytes, missed) in congestion do
    unless shard == 0 do throw "chunk trie supports the reference single-shard layout"
    unless bytes.length == 43 && bytes.head? == some 0 do throw "invalid congestion V1 bytes"
    unless number (bytes.drop 41) == 0 do throw "allowed congestion shard is outside reference layout"
    allowed := missed == 0
  if requests == little 4 0 then return { linkAllowed := allowed }
  unless requests.take 4 == little 4 1 && requests.length ≥ 17 &&
      (requests.drop 4).take 8 == little 8 0 do throw "unsupported bandwidth request map"
  unless requests[12]? == some 0 do throw "unsupported bandwidth request version"
  let count := number ((requests.drop 13).take 4)
  unless requests.length == 17 + count * 7 do throw "invalid bandwidth request bytes"
  let mut requested := 100000
  let mut seen := false
  for i in List.range count do
    let row := (requests.drop (17 + i * 7)).take 7
    if number (row.take 2) == 0 then
      if seen then throw "duplicate single-link bandwidth request"
      seen := true
      let bitmap := number (row.drop 2)
      for bit in List.range 40 do
        if bitmap / 2 ^ bit % 2 == 1 then
          requested := max requested (100000 + (4194304 - 100000) * (bit + 1) / 40)
  return { linkAllowed := allowed, requested }

structure Scheduler where
  sanity : Bytes := List.replicate 32 0
  allowance : Nat := 0
  present : Bool := false

def Scheduler.entries (state : Scheduler) : List (Bytes × Bytes) :=
  if state.present then
    [([15], [0] ++ little 4 1 ++ little 8 0 ++ little 8 0 ++ little 8 state.allowance ++ state.sanity)]
  else []

/-- Single-link scheduling from original external inputs. Remainder grants
do not debit allowance; only the base and requested increments do.
The sanity hash includes the Borsh vector of shard ids, not block height. -/
def Scheduler.advance (state : Scheduler) (input : Input := {}) : Scheduler :=
  { sanity := Sha256.hash (state.sanity ++ Sha256.hash (little 4 1 ++ little 8 0))
    allowance := min 4500000 (state.allowance + 4500000) - (if input.linkAllowed then input.requested else 0)
    present := true }

/-- Every encoded runtime column contributes to canonical trie shape. Rebuild
only at a chunk boundary, which also starts an empty accounting cache. -/
def start (cfg : Wasm.Near.RuntimeConfig) (codes : List (String × Bytes))
    (context : QueueEncoding.Context) (state : ChainState) (scheduler : Scheduler) :
    Except String TrieOverlay.State := do
  TrieOverlay.start ((← QueueEncoding.encode state codes context (some cfg)) ++ scheduler.entries)

end ChainReplay.ChunkTrie
