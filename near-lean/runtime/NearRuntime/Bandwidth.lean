import NearRuntime.ShardLayout
import NearRuntime.ChaCha
import NearRuntime.Sha256

/-! # Bandwidth scheduler

`core/primitives/src/bandwidth_scheduler.rs` (parameters, request values, request bitmaps, the
persistent state) and `runtime/runtime/src/bandwidth_scheduler/{mod,scheduler,distribute_remaining}.rs`
(the algorithm): every shard runs it with the same inputs and gets the same grants of how many bytes
of receipts each shard may send to each other shard at this height.

Stages: give every link its fair allowance, grant base bandwidth, grant requested increases in the
order of decreasing link allowance (ties broken by shuffling with a `ChaCha20Rng` seeded with the
previous block hash), then distribute what remains.

Parameters are those of protocols 74 to 86 (`core/parameters/res/runtime_configs/74.yaml`):
`max_shard_bandwidth = max_allowance = 4_500_000`, `max_single_grant = 4_194_304`,
`max_base_bandwidth = 100_000`; `max_receipt_size` comes from the configuration. -/
namespace Near.Bandwidth

open Near.Sharding

/-! ## Parameters and requests -/

structure Params where
  baseBandwidth : Nat
  maxShardBandwidth : Nat
  maxSingleGrant : Nat
  maxReceiptSize : Nat
  maxAllowance : Nat
  deriving BEq, Repr, Inhabited

/-- `BandwidthSchedulerParams::calculate`. -/
def Params.calculate (maxShardBandwidth maxSingleGrant maxAllowance maxBaseBandwidth maxReceiptSize
    numShards : Nat) : Params :=
  let available := maxShardBandwidth - maxSingleGrant
  { baseBandwidth := min (available / max 1 (numShards - 1)) maxBaseBandwidth
    maxShardBandwidth, maxSingleGrant, maxReceiptSize, maxAllowance }

/-- The parameters of protocols 74 to 86. -/
def Params.protocol (numShards maxReceiptSize : Nat) : Params :=
  Params.calculate 4_500_000 4_194_304 4_500_000 100_000 maxReceiptSize numShards

/-- `BANDWIDTH_REQUEST_VALUES_NUM`. -/
def valuesNum : Nat := 40

/-- `BandwidthRequestValues::new`: `interpolate(base, max_single_grant, i + 1, 40)`. -/
def requestValues (params : Params) : List Nat :=
  (List.range valuesNum).map fun i =>
    params.baseBandwidth + (params.maxSingleGrant - params.baseBandwidth) * (i + 1) / valuesNum

/-- `BandwidthRequest`: the receiver and a 40-bit bitmap of requested values (bit `i`, least
significant first, requests `requestValues[i]`). -/
structure Request where
  toShard : Nat
  bitmap : Nat
  deriving BEq, Repr, Inhabited

def Request.bit (request : Request) (i : Nat) : Bool := request.bitmap / 2 ^ i % 2 == 1

/-- `BandwidthRequest::make_from_receipt_sizes`: for each prefix of the receipt sizes (or receipt
groups) above the base bandwidth, request the smallest value that covers it. -/
def makeRequest (toShard : Nat) (sizes : List Nat) (params : Params) : Option Request := Id.run do
  let values := (requestValues params).toArray
  let mut bitmap := 0
  let mut total := 0
  let mut value := 0
  for size in sizes do
    total := total + size
    if total ≤ params.baseBandwidth then continue
    while value < values.size && values[value]! < total do
      value := value + 1
    if value == values.size then break
    if bitmap / 2 ^ value % 2 == 0 then bitmap := bitmap + 2 ^ value
  if bitmap == 0 then return none
  return some { toShard, bitmap }

/-- Borsh `BandwidthRequests`: variant 0, then the requests. -/
def requestsToBorsh (requests : List Request) : Bytes :=
  [0] ++ Wire.little 4 requests.length ++
    (requests.map fun r => Wire.little 2 r.toShard ++ Wire.little 5 r.bitmap).flatten

private def requestsParser : Wire.Parser (List Request) := do
  unless (← Wire.uint 1) == 0 do throw "unknown bandwidth requests version"
  Wire.repeatN (← Wire.uint 4) do
    let toShard ← Wire.uint 2
    return { toShard, bitmap := ← Wire.uint 5 }

/-- Requests of every shard at the previous height: `BTreeMap<ShardId, BandwidthRequests>`. -/
def blockRequestsOfBorsh : Bytes → Except String (List (Nat × List Request)) := Wire.run do
  let count ← Wire.uint 4
  Wire.repeatN count do
    let shard ← Wire.uint 8
    return (shard, ← requestsParser)

def blockRequestsToBorsh (requests : List (Nat × List Request)) : Bytes :=
  Wire.little 4 requests.length ++
    (requests.map fun (shard, rs) => Wire.little 8 shard ++ requestsToBorsh rs).flatten

/-! ## Persistent state -/

/-- `BandwidthSchedulerStateV1`; `present` tells whether the trie column exists. -/
structure State where
  allowances : List (Nat × Nat × Nat) := []
  sanity : Bytes := List.replicate 32 0
  present : Bool := false
  deriving BEq, Repr, Inhabited

def State.toBorsh (state : State) : Bytes :=
  [0] ++ Wire.little 4 state.allowances.length ++
    (state.allowances.map fun (s, r, a) => Wire.little 8 s ++ Wire.little 8 r ++ Wire.little 8 a).flatten ++
    state.sanity

def State.ofBorsh : Bytes → Except String State := Wire.run do
  unless (← Wire.uint 1) == 0 do throw "unknown scheduler state version"
  let allowances ← Wire.repeatN (← Wire.uint 4) do
    let sender ← Wire.uint 8
    let receiver ← Wire.uint 8
    return (sender, receiver, ← Wire.uint 8)
  return { allowances, sanity := ← Wire.take 32, present := true }

/-- The column `BandwidthSchedulerState` (key 15), when present. -/
def State.entries (state : State) : List (Bytes × Bytes) :=
  if state.present then [([15], state.toBorsh)] else []

/-! ## The algorithm -/

structure ShardStatus where
  lastChunkMissing : Bool
  allowedSenderIndex : Option Nat
  isFullyCongested : Bool
  deriving Repr

structure Output where
  /-- Bytes `sender` may send to `receiver`, by shard index (`n * sender + receiver`). -/
  granted : Array Nat
  numShards : Nat
  state : State

/-- `GrantedBandwidth::get_granted_bandwidth`, by shard indices. -/
def Output.grant (out : Output) (sender receiver : Nat) : Nat :=
  if sender < out.numShards && receiver < out.numShards then
    out.granted[sender * out.numShards + receiver]!
  else 0

/-- `calculate_is_link_allowed`. -/
def linkAllowed (status : Array (Option ShardStatus)) (sender receiver : Nat) : Bool :=
  match status[receiver]! with
  | none => false
  | some receiverStatus =>
    if receiverStatus.lastChunkMissing then false
    else if (status[sender]!).any (·.lastChunkMissing) then false
    else if receiverStatus.isFullyCongested then receiverStatus.allowedSenderIndex == some sender
    else true

/-- A request in the scheduler's form: the link and the consecutive increases it asks for. -/
structure SchedulerRequest where
  sender : Nat
  receiver : Nat
  increases : List Nat
  deriving Inhabited

/-- `SchedulerBandwidthRequest::new`. -/
def schedulerRequest (layout : ShardLayout) (params : Params) (sender : Nat) (request : Request) :
    Option SchedulerRequest := do
  let senderIndex ← layout.index? sender
  let receiverIndex ← layout.index? request.toShard
  let mut increases := []
  let mut total := params.baseBandwidth
  for (value, i) in (requestValues params).zipIdx do
    if !request.bit i then continue
    if value ≤ total then continue
    increases := increases ++ [value - total]
    total := value
  if increases.isEmpty then none
  else some { sender := senderIndex, receiver := receiverIndex, increases }

/-- Mutable scheduler state of one run (`BandwidthScheduler`). -/
structure Run where
  n : Nat
  params : Params
  allowed : Array Bool
  senderBudget : Array Nat
  receiverBudget : Array Nat
  allowance : Array (Option Nat)
  granted : Array (Option Nat)
  rng : ChaCha.Rng

namespace Run

def link (r : Run) (sender receiver : Nat) : Nat := sender * r.n + receiver

def getAllowance (r : Run) (l : Nat) : Nat := (r.allowance[l]!).getD 0

def increaseAllowance (r : Run) (l increase : Nat) : Run :=
  { r with allowance := r.allowance.set! l (some (min (r.getAllowance l + increase) r.params.maxAllowance)) }

def decreaseAllowance (r : Run) (l decrease : Nat) : Run :=
  { r with allowance := r.allowance.set! l (some (r.getAllowance l - decrease)) }

def grantMore (r : Run) (l bandwidth : Nat) : Run :=
  { r with granted := r.granted.set! l (some ((r.granted[l]!).getD 0 + bandwidth)) }

/-- `try_grant_bandwidth`: `none` when the link is closed or a budget is too small. -/
def tryGrant (r : Run) (sender receiver bandwidth : Nat) : Option Run :=
  let l := r.link sender receiver
  if !r.allowed[l]! then none
  else if r.senderBudget[sender]! < bandwidth || r.receiverBudget[receiver]! < bandwidth then none
  else
    let r := { r with senderBudget := r.senderBudget.set! sender (r.senderBudget[sender]! - bandwidth)
                      receiverBudget := r.receiverBudget.set! receiver (r.receiverBudget[receiver]! - bandwidth) }
    some ((r.decreaseAllowance l bandwidth).grantMore l bandwidth)

end Run

/-- One endpoint of `distribute_remaining_bandwidth`. -/
structure Endpoint where
  linksNum : Nat
  bandwidthLeft : Nat
  deriving Inhabited

private def Endpoint.average (e : Endpoint) : Nat :=
  if e.linksNum == 0 then 0 else e.bandwidthLeft / e.linksNum

/-- `distribute_remaining_bandwidth`: grants per link (`n * sender + receiver`) that use up what
the budgets still allow, processing senders and receivers by increasing average link bandwidth. -/
def distributeRemaining (n : Nat) (senderBudget receiverBudget : Array Nat) (allowed : Array Bool) :
    Array Nat := Id.run do
  let mut senders : Array Endpoint := (List.range n).toArray.map fun i =>
    { linksNum := 0, bandwidthLeft := senderBudget[i]! }
  let mut receivers : Array Endpoint := (List.range n).toArray.map fun i =>
    { linksNum := 0, bandwidthLeft := receiverBudget[i]! }
  for s in List.range n do
    for r in List.range n do
      if allowed[s * n + r]! then
        senders := senders.modify s fun e => { e with linksNum := e.linksNum + 1 }
        receivers := receivers.modify r fun e => { e with linksNum := e.linksNum + 1 }
  -- stable sorts, as `sort_by_key`
  let sendersByAverage := (List.range n).mergeSort fun a b => senders[a]!.average ≤ senders[b]!.average
  let receiversByAverage := (List.range n).mergeSort fun a b => receivers[a]!.average ≤ receivers[b]!.average
  let mut grants := Array.replicate (n * n) 0
  for s in sendersByAverage do
    for r in receiversByAverage do
      if !allowed[s * n + r]! then continue
      let sender := senders[s]!
      let receiver := receivers[r]!
      if sender.linksNum == 0 || receiver.linksNum == 0 then break
      let granted := min (sender.bandwidthLeft / sender.linksNum) (receiver.bandwidthLeft / receiver.linksNum)
      grants := grants.set! (s * n + r) granted
      senders := senders.set! s { linksNum := sender.linksNum - 1, bandwidthLeft := sender.bandwidthLeft - granted }
      receivers := receivers.set! r { linksNum := receiver.linksNum - 1, bandwidthLeft := receiver.bandwidthLeft - granted }
  return grants

/-- Requests by allowance, ascending, as the `BTreeMap<Bandwidth, Vec<_>>` of `process_bandwidth_requests`. -/
private def insertByAllowance (key : Nat) (request : SchedulerRequest) :
    List (Nat × List SchedulerRequest) → List (Nat × List SchedulerRequest)
  | [] => [(key, [request])]
  | (k, rs) :: rest =>
    if k == key then (k, rs ++ [request]) :: rest
    else if key < k then (key, [request]) :: (k, rs) :: rest
    else (k, rs) :: insertByAllowance key request rest

/-- `process_bandwidth_requests`; `fuel` bounds the number of groups, which each retire an increase. -/
private def processRequests (fuel : Nat) (r : Run) (queue : List (Nat × List SchedulerRequest)) : Run :=
  match fuel, queue.getLast? with
  | 0, _ | _, none => r
  | fuel + 1, some (_, group) =>
    let queue := queue.dropLast
    let (shuffled, rng) := r.rng.shuffle group.toArray
    let r := { r with rng }
    let (r, queue) := shuffled.toList.foldl (fun (r, queue) request =>
      match request.increases with
      | [] => (r, queue)
      | first :: rest =>
        match r.tryGrant request.sender request.receiver first with
        | none => (r, queue)
        | some r =>
          if rest.isEmpty then (r, queue)
          else (r, insertByAllowance (r.getAllowance (r.link request.sender request.receiver))
            { request with increases := rest } queue)) (r, queue)
    processRequests fuel r queue

/-- `BandwidthScheduler::run`. `requests` lists every shard's requests of the previous height in
shard id order, `status` the shards' congestion status by shard id, `seed` the previous block hash. -/
def schedule (layout : ShardLayout) (state : State) (params : Params)
    (requests : List (Nat × List Request)) (status : List (Nat × ShardStatus)) (seed : Bytes) : Output :=
  let n := layout.numShards
  let blank : Run :=
    { n, params, allowed := Array.replicate (n * n) false, senderBudget := Array.replicate n 0
      receiverBudget := Array.replicate n 0, allowance := Array.replicate (n * n) none
      granted := Array.replicate (n * n) none, rng := ChaCha.Rng.ofSeed seed }
  -- link allowances of the previous state; entries of shards outside the layout are dropped
  let r := state.allowances.foldl (fun (r : Run) (s, rc, a) =>
    match layout.index? s, layout.index? rc with
    | some si, some ri => { r with allowance := r.allowance.set! (r.link si ri) (some a) }
    | _, _ => r) blank
  let byIndex : Array (Option ShardStatus) := status.foldl (fun acc (shard, st) =>
    match layout.index? shard with
    | some i => acc.set! i (some st)
    | none => acc) (Array.replicate n none)
  let r := { r with allowed := (Array.range (n * n)).map fun l => linkAllowed byIndex (l / n) (l % n) }
  let schedulerRequests := (requests.flatMap fun (sender, rs) =>
    rs.filterMap (schedulerRequest layout params sender))
  let r := { r with senderBudget := Array.replicate n params.maxShardBandwidth
                    receiverBudget := Array.replicate n params.maxShardBandwidth }
  -- increase_allowances
  let fair := params.maxShardBandwidth / n
  let r := (List.range (n * n)).foldl (fun r l => r.increaseAllowance l fair) r
  -- grant_base_bandwidth
  let r := (List.range n).foldl (fun r s => (List.range n).foldl (fun r rc =>
    (r.tryGrant s rc params.baseBandwidth).getD r) r) r
  -- process_bandwidth_requests
  let queue := schedulerRequests.foldl (fun queue request =>
    insertByAllowance (r.getAllowance (r.link request.sender request.receiver)) request queue) []
  let fuel := schedulerRequests.foldl (fun total request => total + request.increases.length + 1) 1
  let r := processRequests fuel r queue
  -- distribute_remaining_bandwidth
  let remaining := distributeRemaining n r.senderBudget r.receiverBudget r.allowed
  let r := (List.range (n * n)).foldl (fun r l => r.grantMore l remaining[l]!) r
  let allShards := layout.shardIds
  let allowances := (List.range (n * n)).filterMap fun l =>
    (r.allowance[l]!).map fun a =>
      ((layout.id? (l / n)).getD 0, (layout.id? (l % n)).getD 0, a)
  let sanity := Sha256.hash (state.sanity ++ Sha256.hash
    (Wire.little 4 allShards.length ++ (allShards.map (Wire.little 8)).flatten))
  { granted := (r.granted.map fun g => g.getD 0), numShards := n
    state := { allowances, sanity, present := true } }

end Near.Bandwidth
