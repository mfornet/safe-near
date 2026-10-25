import Lean.Data.Json
import NearNode.Network.Driver
import NearNode.Chain.Apply
import NearNode.Chain.Persist

/-!
# Applying the blocks the driver hands over

The worker takes validated blocks with their chunk bodies one at a time, applies the chunks
(`Apply.applyBlock`, M5b), commits the block with its trie nodes and chunk extras to the store, and
compares what it computed with what the peer reported:

* the `ChunkExtra` of a chunk against the header of the shard's next new chunk, which carries the
  previous chunk's state root, outcome root, gas used, balance burnt, validator proposals, congestion
  info and bandwidth requests (`ShardChunkHeaderInner::prev_*`); the state root is also checked by the
  application of that next block;
* the receipts the chunk sent against the `prev_outgoing_receipts` in the body of the next new chunk
  of the shard.

It runs on its own thread: applying a chunk takes the time the Lean interpreter needs for its
contracts, minutes for a block of heavy calls.
-/

namespace Near.Node.Network

open Near.Node Near.Node.Borsh Near.Node.Chain Near.Node.Apply

/-- Counters of the worker. -/
structure ApplyStats where
  blocks : Nat := 0
  chunks : Nat := 0
  extrasChecked : Nat := 0
  extrasAgree : Nat := 0
  receiptsChecked : Nat := 0
  receiptsAgree : Nat := 0
  /-- Time spent applying, in milliseconds. -/
  millis : Nat := 0
  /-- What differed, the first few. -/
  mismatches : Array String := #[]
  deriving Inhabited

/-- The fields of a chunk header that report the previous chunk's results. -/
private def previousResults (h : ShardChunkHeader) :
    Option
      (CryptoHash ×
        CryptoHash × Gas × Balance × Array ValidatorStake × CongestionInfo × BandwidthRequests) :=
  match h with
  | .v3 ⟨.v4 i, _, _⟩ =>
    some
      (i.prevStateRoot, i.prevOutcomeRoot, i.prevGasUsed, i.prevBalanceBurnt,
        i.prevValidatorProposals, i.congestionInfo, i.bandwidthRequests)
  | .v3 ⟨.v5 i, _, _⟩ =>
    some
      (i.prevStateRoot, i.prevOutcomeRoot, i.prevGasUsed, i.prevBalanceBurnt,
        i.prevValidatorProposals, i.congestionInfo, i.bandwidthRequests)
  | _ => none

/-- What of a `ChunkExtra` differs from the header of the next chunk. -/
def extraDifferences (extra : ChunkExtra) (next : ShardChunkHeader) : List String :=
  match extra, previousResults next with
  | .v5 e, some (root, outcome, gas, burnt, proposals, congestion, requests) =>
    ([("stateRoot", e.stateRoot == root), ("outcomeRoot", e.outcomeRoot == outcome),
              ("gasUsed", e.gasUsed == gas), ("balanceBurnt", e.balanceBurnt == burnt),
              ("validatorProposals", e.validatorProposals == proposals),
              ("congestionInfo", e.congestionInfo == congestion),
              ("bandwidthRequests", e.bandwidthRequests == requests)].filter
          (!·.2)).map
      (·.1)
  | _, _ => ["unsupported header version"]

private def hex (b : ByteArray) : String :=
  b.foldl (fun s x => s ++ String.ofList (Nat.toDigits 16 (x.toNat + 256)).tail) ""

/-- One line of the log of applied blocks. -/
private def appliedLine (work : Work) (reports : Array ShardReport) : String :=
  let h := work.block.header.view?.get!.height
  let shards :=
    reports.toList.map fun r =>
      match r.extra with
      | .v5 e =>
        s!"\{\"shard\":{r.shard},\"stateRoot\":\"{hex e.stateRoot.bytes}\",\"outcomeRoot\":\"{hex e.outcomeRoot.bytes}\",\"gasUsed\":{e.gasUsed}}"
      | _ => s!"\{\"shard\":{r.shard}}"
  s!"\{\"height\":{h},\"hash\":\"{hex work.block.header.hash.bytes}\",\"chunks\":[{",".intercalate shards}]}"

/-- Where the worker keeps what it commits and reports. -/
structure WorkerEnv where
  params : Params
  shared : Shared
  store : Option Store.Store
  progress : IO.Ref Progress
  stats : IO.Ref ApplyStats
  /-- The log of applied blocks. -/
  appliedLog : Option IO.FS.Handle
  log : String → IO Unit

/-- Applies one block. -/
def applyWork (env : WorkerEnv) (work : Work) : IO Unit := do
  let started ← IO.monoMsNow
  let height := work.block.header.view?.get!.height
  let empty : Body := { transactions := #[], claimedOutgoing := #[], claimedIncoming := #[] }
  let pr ← env.progress.get
  match applyBlock env.params work.st work.block (fun s => (work.bodies[s]?).getD empty) pr with
  | .error m =>
    env.shared.fail s!"block {height}: applying the chunks failed: {m}"
  | .ok (pr, reports, chunkOps) =>
    env.progress.set pr
    let mut st ← env.stats.get
    for rep in reports do
      st := { st with chunks := st.chunks + 1 }
      -- the next new chunk of the shard is in the child block
      let next? :=
        work.childChunks.find? fun c => c.shardId == rep.shard && c.isNewChunk work.childHeight
      if let some next := next? then
        st := { st with extrasChecked := st.extrasChecked + 1 }
        match extraDifferences rep.extra next with
        | [] =>
          st := { st with extrasAgree := st.extrasAgree + 1 }
        | diff =>
          st :=
            { st with
              mismatches :=
                st.mismatches.push
                  s!"block {height} shard {rep.shard}: ChunkExtra differs in {", ".intercalate diff}" }
        if let some body := work.bodies[rep.shard]? then
          st := { st with receiptsChecked := st.receiptsChecked + 1 }
          if body.claimedOutgoing == rep.outgoing then
            st := { st with receiptsAgree := st.receiptsAgree + 1 }
          else
            st :=
              { st with
                mismatches :=
                  st.mismatches.push
                    s!"block {height} shard {rep.shard}: outgoing receipts differ from the next chunk's" }
    if let some s := env.store then
      match commitOps work.st work.block work.fin chunkOps with
      | .ok ops =>
        discard <| s.commit ops
      | .error e =>
        env.shared.fail s!"block {height}: {e}"
    st :=
      { st with
        blocks := st.blocks + 1, millis := st.millis + ((← IO.monoMsNow) - started) }
    env.stats.set st
    env.shared.applied.set height
    if let some h := env.appliedLog then
      h.putStrLn (appliedLine work reports)
      h.flush

/-- The worker loop: applies what the driver queues until asked to stop or something fails. -/
partial def applyLoop (env : WorkerEnv) : IO Unit := do
  if (← env.shared.failure.get).isSome then
    return
  let q ← env.shared.queue.modifyGet fun q => (q[0]?, q.extract 1 q.size)
  match q with
  | some work =>
    applyWork env work
    applyLoop env
  | none =>
    if ← env.shared.stop.get then
      return
    IO.sleep 5
    applyLoop env

end Near.Node.Network
