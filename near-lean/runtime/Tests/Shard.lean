import Batteries.Lean.Except
import NearRuntime.ShardSink
import NearRuntime.ShardLayout
import NearRuntime.ChaCha
import NearRuntime.Congestion
import NearRuntime.Bandwidth
import NearRuntime.ShardSink

/-! Shard machinery against values `rand 0.8.5`, `rand_chacha 0.3.1` and nearcore's own unit tests
produce (`distribute_remaining.rs`, `bandwidth_scheduler.rs`). -/
namespace NearRuntime.Tests.Shard

open Near Near.Sharding Near.ChaCha Near.Congestion Near.Bandwidth Near.ShardSink

private def require (count : IO.Ref Nat) (name : String) (ok : Bool) : IO Unit := do
  unless ok do
    throw (IO.userError s!"FAIL: {name}")
  count.modify (· + 1)
  IO.println s!"ok: {name}"

private def seed : Bytes := (List.range 32).map fun i => UInt8.ofNat ((i * 7 + 3) % 256)

/-- Hex of the shard layout the localnet corpus uses (boundaries test1..test3, ids 3, 1, 0, 2). -/
private def corpusLayout : String :=
  "020300000005000000746573743105000000746573743205000000746573743304000000030000000000000001000000" ++
  "000000000000000000000000020000000000000004000000000000000000000002000000000000000100000000000000" ++
  "010000000000000002000000000000000300000000000000030000000000000000000000000000000400000000000000" ++
  "000000000300000000000000010000000000000001000000000000000200000000000000000000000000000003000000" ++
  "000000000200000000000000000000000000"

private def unhex (text : String) : Bytes :=
  let digits := text.toList.map fun c => if c.isDigit then c.toNat - 48 else c.toNat - 87
  let rec go : List Nat → Bytes
    | a :: b :: rest => UInt8.ofNat (a * 16 + b) :: go rest
    | _ => []
  go digits

private def sizes (n : Nat) : Array Nat := Array.replicate (n * n) 0

/-- `distribute_remaining_bandwidth` as the nearcore tests call it. -/
private def distribute (budgets : List Nat) (allowed : List (Nat × Nat)) : List ((Nat × Nat) × Nat) :=
  let n := budgets.length
  let flags := (Array.range (n * n)).map fun l => allowed.contains (l / n, l % n)
  let grants := distributeRemaining n budgets.toArray budgets.toArray flags
  ((List.range (n * n)).filterMap fun l =>
    if flags[l]! then some ((l / n, l % n), grants[l]!) else none)

def run : IO Nat := do
  let count ← IO.mkRef 0
  -- the layout of the sharded corpus: ids 3, 1, 0, 2 over boundaries test1, test2, test3
  match ShardLayout.ofBorsh (unhex corpusLayout) with
  | .error e => throw (IO.userError s!"layout: {e}")
  | .ok layout =>
    require count "layout parses" (layout.shardIds == [3, 1, 0, 2] && layout.boundaries.length == 3)
    require count "accounts route by boundary"
      (layout.accountShard "a.node0" == 3 && layout.accountShard "test1.node0" == 1 &&
        layout.accountShard "test2.node0" == 0 && layout.accountShard "test3.node0" == 2 &&
        layout.accountShard "test1" == 1 && layout.accountShard "zzz" == 2)
    require count "shard index is the position in the id list"
      (layout.index? 0 == some 2 && layout.index? 3 == some 0 && layout.index? 9 == none)
  require count "single shard layout" (ShardLayout.single.accountShard "anyone" == 0)
  -- ChaCha20 keystream and rand's bounded integers
  let (zero, _) := (List.range 4).foldl (fun (acc, rng) _ =>
    let (v, rng) := rng.nextU32
    (acc ++ [v], rng)) (([] : List Nat), Rng.ofSeed (List.replicate 32 0))
  require count "ChaCha20 zero seed words" (zero == [2917185654, 2419978656, 3848953152, 683509331])
  let (words, _) := (List.range 20).foldl (fun (acc, rng) _ =>
    let (v, rng) := rng.nextU32
    (acc ++ [v], rng)) (([] : List Nat), Rng.ofSeed seed)
  require count "ChaCha20 words across a block boundary"
    (words == [2629850234, 447817501, 132856601, 1539537464, 2046792620, 1161496927, 3332484898,
      735472602, 764129432, 3371905307, 2948077146, 1032965797, 686490056, 3485757872, 3653031167,
      212640606, 1794996188, 7929947, 435728522, 46221356])
  let bounds := [1, 2, 3, 5, 7, 10, 16, 17, 100, 1000, 65537, 3000000000]
  let (below, _) := (List.range 24).foldl (fun (acc, rng) i =>
    let (v, rng) := rng.below (bounds[i % 12]!)
    (acc ++ [v], rng)) (([] : List Nat), Rng.ofSeed seed)
  require count "gen_range(0..n) rejection sampling"
    (below == [0, 0, 1, 2, 5, 2, 0, 0, 58, 554, 12320, 2675927987, 0, 0, 0, 1, 5, 3, 5, 7, 46, 193,
      63016, 434142030])
  let (shuffles, _) := (List.range 13).foldl (fun (acc, rng) n =>
    let (a, rng) := rng.shuffle (Array.range n)
    (acc ++ [a.toList], rng)) (([] : List (List Nat)), Rng.ofSeed seed)
  require count "slice shuffle"
    (shuffles == [[], [0], [0, 1], [1, 2, 0], [2, 0, 3, 1], [1, 0, 2, 4, 3], [5, 1, 3, 4, 0, 2],
      [3, 6, 4, 0, 2, 5, 1], [7, 3, 5, 1, 6, 2, 4, 0], [5, 8, 1, 4, 6, 7, 2, 3, 0],
      [1, 5, 9, 0, 8, 6, 3, 7, 4, 2], [6, 4, 3, 7, 9, 2, 5, 8, 10, 0, 1],
      [11, 9, 0, 5, 2, 8, 7, 1, 3, 10, 4, 6]])
  -- scheduler parameters and request values (`bandwidth_scheduler.rs` tests)
  let params := Params.protocol 6 (4 * 1024 * 1024)
  require count "base bandwidth of six shards" (params.baseBandwidth == 61139)
  require count "request values"
    (requestValues params == [164468, 267797, 371126, 474455, 577784, 681113, 784442, 887772, 991101,
      1094430, 1197759, 1301088, 1404417, 1507746, 1611075, 1714405, 1817734, 1921063, 2024392,
      2127721, 2231050, 2334379, 2437708, 2541038, 2644367, 2747696, 2851025, 2954354, 3057683,
      3161012, 3264341, 3367671, 3471000, 3574329, 3677658, 3780987, 3884316, 3987645, 4090974,
      4194304])
  require count "base bandwidth of one shard" ((Params.protocol 1 (4 * 1024 * 1024)).baseBandwidth == 100000)
  require count "request from receipt sizes"
    (makeRequest 0 [100000, 100000, 50000] (Params.protocol 4 (4 * 1024 * 1024)) ==
      some { toShard := 0, bitmap := 1 + 2 ^ 1 } && makeRequest 0 [100000] (Params.protocol 4 (4 * 1024 * 1024)) == none)
  -- `distribute_remaining.rs` unit tests
  require count "distribute: three shards share equally"
    ((distribute [300, 300, 300] ((List.range 9).map fun l => (l / 3, l % 3))).all (·.2 == 100))
  require count "distribute: two to one"
    (distribute [100, 100, 100] [(1, 0), (1, 2), (0, 1), (2, 1)] ==
      [((0, 1), 50), ((1, 0), 50), ((1, 2), 50), ((2, 1), 50)])
  require count "distribute: two fully congested"
    (distribute [300, 300, 300] [(0, 0), (0, 1), (1, 0), (1, 2), (2, 0)] ==
      [((0, 0), 100), ((0, 1), 200), ((1, 0), 100), ((1, 2), 200), ((2, 0), 100)])
  -- an idle four-shard run grants base bandwidth plus a share of the rest and keeps allowances
  let layout := ShardLayout.mk [] [0, 1, 2, 3]
  let open_ : ShardStatus := { lastChunkMissing := false, allowedSenderIndex := none, isFullyCongested := false }
  let out := schedule layout {} (Params.protocol 4 (4 * 1024 * 1024)) []
    ((List.range 4).map fun s => (s, open_)) (List.replicate 32 0)
  require count "idle scheduler grants every link the same"
    ((List.range 16).all fun l => out.granted[l]! == out.granted[0]!)
  require count "idle scheduler stays inside the shard budget"
    (out.granted[0]! * 4 ≤ 4_500_000 && out.granted[0]! ≥ 100000)
  require count "idle scheduler allowance is fair share minus base"
    (out.state.allowances.all (fun (_, _, a) => a == 4_500_000 / 4 - 100000) && out.state.allowances.length == 16)
  -- congestion math
  require count "mix of equal ends" (mix 7 7 0.3 == 7)
  require count "mix rounds" (mix 50 80 0.33 == 60 && mix 0 1000 0.5 == 500)
  require count "clamped fraction" (clampedFraction 5 10 == 0.5 && clampedFraction 10 10 == 1.0)
  return ← count.get


/-- A Borsh receipt header: predecessor, receiver, id, then the tag byte and `rest`. -/
private def receiptBytes (receiver : String) (tag : UInt8) (rest : Bytes) : Bytes :=
  let text (s : String) := Wire.little 4 s.toUTF8.toList.length ++ s.toUTF8.toList
  text "alice.near" ++ text receiver ++ List.replicate 32 7 ++ [tag] ++ rest

private def filler (n : Nat) : Bytes := List.replicate n 9

private def shardFixture (limits : List (Nat × Limit)) : Sink :=
  let layout := ShardLayout.mk ["m"] [0, 1]
  { config := default, layout, shard := 0, info := {}, limits, buffers := {} }

def runSink : IO Nat := do
  let count ← IO.mkRef 0
  let config : Config := { (default : Config) with maxReceiptSize := 4_194_304 }
  let layout := ShardLayout.mk ["m"] [0, 1]
  let route := Route.ofReceipt (receiptBytes "zed.near" 0 (filler 20))
  require count "a receipt routes by its receiver" ((route.map (·.shard layout)) == .ok 1)
  let dist := Route.ofReceipt (receiptBytes "system" 4 ([1, 0] ++ List.replicate 32 3 ++ Wire.little 8 0 ++ filler 4))
  require count "a distribution routes by its target shard" ((dist.map (·.shard layout)) == .ok 0)
  let sink : Sink := { shardFixture [(1, { gas := 1000, size := 500 }), (0, { gas := gasMax, size := 500 })]
    with config }
  let near := receiptBytes "a.near" 0 (filler 100)
  let far := receiptBytes "zed.near" 0 (filler 100)
  -- the first fits, the second no longer does and is buffered with its metadata
  let r := sink.forwardOrBuffer far 600 >>= fun s => s.forwardOrBuffer far 600
  match r with
  | .error e => throw (IO.userError s!"sink: {e}")
  | .ok s =>
    require count "an unaffordable receipt is buffered, not sent"
      (s.outgoing == [far] && s.buffers.length 1 == 1 && s.info.bufferedGas == 600 &&
        s.info.receiptBytes == far.length)
  match sink.forwardOrBuffer near 5 with
  | .error e => throw (IO.userError s!"sink: {e}")
  | .ok s => require count "an affordable receipt is sent at once" (s.outgoing == [near] && s.buffers.queues.isEmpty)
  -- groups: two receipts of 100 kB share a group only up to the bound
  let small := receiptBytes "zed.near" 0 (filler 50)
  let blocked : Sink := { sink with limits := [(1, { gas := 1000, size := 0 })] }
  let big := blocked.forwardOrBuffer small 0 >>= fun s => s.forwardOrBuffer small 0
  match big with
  | .error e => throw (IO.userError s!"sink: {e}")
  | .ok s =>
    let groups := ((s.buffers.groups.find? (·.1 == 1)).map (·.2)).getD {}
    require count "receipts of one buffer share a group"
      (groups.groups.length == 1 && groups.totalReceipts == 2 && groups.totalSize == 2 * small.length)
    -- the round trip of the raw columns, and the bytes nearcore stores for a 2-receipt group
    match s.buffers.entries with
    | .error e => throw (IO.userError s!"entries: {e}")
    | .ok entries =>
      require count "buffer columns round trip" ((Buffers.ofEntries entries).toOption == some s.buffers)
      require count "group queue data layout"
        (entries.contains ([16] ++ Wire.little 8 1,
          [0] ++ Wire.little 8 0 ++ Wire.little 8 1 ++ Wire.little 8 (2 * small.length) ++ Wire.little 16 0 ++
            Wire.little 8 2))
  -- bandwidth requests ask for the group sizes above the base bandwidth
  let oversize := receiptBytes "zed.near" 0 (filler 150_000)
  match blocked.forwardOrBuffer oversize 0 with
  | .error e => throw (IO.userError s!"sink: {e}")
  | .ok s =>
    require count "a large buffered receipt makes a request"
      ((s.requests (Params.protocol 2 4_194_304)).length == 1)
  -- forwarding from the buffer stops at the first receipt that does not fit
  match (blocked.forwardOrBuffer far 600 >>= fun s => s.forwardOrBuffer far 600) with
  | .error e => throw (IO.userError s!"sink: {e}")
  | .ok s =>
    let again := { s with outgoing := [], limits := [(1, { gas := 700, size := 10_000 })] }
    match again.forwardFromBuffer 1 with
    | .error e => throw (IO.userError s!"forward: {e}")
    | .ok t =>
      require count "buffered receipts are sent once they fit"
        (t.outgoing == [far] && t.buffers.length 1 == 1 && t.info.bufferedGas == 600 &&
          t.info.receiptBytes == far.length && (t.buffers.entries.toOption.map (·.length)) == some 4)
  return ← count.get

end NearRuntime.Tests.Shard
