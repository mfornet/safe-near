import NearNode.Chain.State
import NearNode.Validator.Messages

/-!
# Doomslug

`chain/chain/src/doomslug.rs` at the pin: what a block producer does with approvals and what every
validator does to send them. Time is a number of milliseconds on a monotonic clock that the caller
reads; every function that depends on it takes it.

* **Sending.** `setTip` restarts the timer when the head changes and marks an endorsement pending.
  `processTimer` (every `doomslug_step_period`) sends an `Endorsement(tip)` for `tip + 1` once
  `endorsement_delay` has passed since the last one, and a `Skip(tip)` for each further height whose
  wait `T(h - last_final_height)` has passed. The largest target height only grows: the node never
  approves two blocks at one height.
* **Receiving.** `onApprovalMessage` keeps one approval per account (a newer one withdraws the older
  from its tracker) in a tracker per `(target height, ApprovalInner)` with the stake it carries in this
  epoch and the next; a block can be produced once both exceed two thirds (or the next is zero) and,
  in `readyToProduceBlock`, either all chunks are in or a third of `T` has passed since then.
-/

namespace Near.Node.Validator

open Near.Node Near.Node.Chain

def maxTimerIters : Nat :=
  20

def maxHeightsAheadToStoreApprovals : Nat :=
  10000

def maxHeightsBeforeToStoreApprovals : Nat :=
  20

/-- `DoomslugBlockProductionReadiness`. -/
inductive Readiness where
  | notReady
  | readySince (t : Nat)
  deriving BEq, Inhabited, Repr

/-- `ChunksReadiness`. -/
inductive ChunksReadiness where
  | notReady
  | ready (t : Nat)
  deriving BEq, Inhabited, Repr

/-- `DoomslugApprovalsTracker`. -/
structure Tracker where
  /-- The approvals seen, by account, with the time they arrived. -/
  witness : Std.HashMap String (Approval × Nat) := {}
  stakes : Std.HashMap String (Nat × Nat) := {}
  totalThis : Nat := 0
  totalNext : Nat := 0
  approvedThis : Nat := 0
  approvedNext : Nat := 0
  timePassedThreshold : Option Nat := none
  deriving Inhabited

def Tracker.new (stakes : Array ApprovalStake) : Tracker :=
  let map :=
    stakes.foldl (fun m s => m.insert s.accountId.val (s.stakeThisEpoch.val, s.stakeNextEpoch.val))
      {}
  { stakes := map, totalThis := stakes.foldl (· + ·.stakeThisEpoch.val) 0,
    totalNext := stakes.foldl (· + ·.stakeNextEpoch.val) 0 }

/-- `get_block_production_readiness`: sets the time the threshold was passed the first time. -/
def Tracker.readiness (t : Tracker) (now : Nat) : Tracker × Readiness :=
  let minThis := t.totalThis * 2 / 3
  let minNext := t.totalNext * 2 / 3
  if t.approvedThis > minThis && (t.approvedNext > minNext || t.totalNext == 0) then
    let since := t.timePassedThreshold.getD now
    ({ t with timePassedThreshold := some since }, .readySince since)
  else (t, .notReady)

/-- `DoomslugApprovalsTracker::process_approval`. -/
def Tracker.process (t : Tracker) (a : Approval) (now : Nat) : Tracker × Readiness :=
  let t :=
    if t.witness.contains a.accountId.val then t
    else
      let (s, n) := t.stakes.getD a.accountId.val (0, 0)
      { t with
        witness := t.witness.insert a.accountId.val (a, now), approvedThis := t.approvedThis + s,
        approvedNext := t.approvedNext + n }
  t.readiness now

/-- `withdraw_approval`. -/
def Tracker.withdraw (t : Tracker) (account : AccountId) : Tracker :=
  match t.witness[account.val]? with
  | none => t
  | some _ =>
    let (s, n) := t.stakes.getD account.val (0, 0)
    { t with
      witness := t.witness.erase account.val, approvedThis := t.approvedThis - s,
      approvedNext := t.approvedNext - n }

/-- `DoomslugApprovalsTrackersAtHeight`: the trackers of one target height by what they approve. -/
structure AtHeight where
  trackers : Array (ApprovalInner × Tracker) := #[]
  lastApprovalPerAccount : Std.HashMap String ApprovalInner := {}
  deriving Inhabited

def AtHeight.tracker? (h : AtHeight) (inner : ApprovalInner) : Option Tracker :=
  (h.trackers.find? (·.1 == inner)).map (·.2)

private def AtHeight.setTracker (h : AtHeight) (inner : ApprovalInner) (t : Tracker) : AtHeight :=
  match h.trackers.findIdx? (·.1 == inner) with
  | some i => { h with trackers := h.trackers.set! i (inner, t) }
  | none => { h with trackers := h.trackers.push (inner, t) }

/-- `DoomslugApprovalsTrackersAtHeight::process_approval`. -/
def AtHeight.process (h : AtHeight) (a : Approval) (stakes : Array ApprovalStake) (now : Nat) :
    AtHeight × Readiness :=
  Id.run do
    let mut h := h
    if let some last := h.lastApprovalPerAccount[a.accountId.val]? then
      if let some t := h.tracker? last then
        let t := t.withdraw a.accountId
        if t.witness.isEmpty then
          h := { h with trackers := h.trackers.filter (·.1 != last) }
        else
          h := h.setTracker last t
    if !stakes.any (·.accountId == a.accountId) then
      return (h, .notReady)
    h :=
      { h with lastApprovalPerAccount := h.lastApprovalPerAccount.insert a.accountId.val a.inner }
    let t := (h.tracker? a.inner).getD (Tracker.new stakes)
    let (t, r) := t.process a now
    return (h.setTracker a.inner t, r)

/-- `DoomslugTimer`. -/
structure Timer where
  started : Nat
  lastEndorsementSent : Nat
  height : BlockHeight := 0
  deriving Inhabited

/-- The delays, in milliseconds: the endorsement delay, the base and the cap of `T`, and
`chunk_wait_mult` as `numer / denom`. -/
structure Delays where
  endorsement : Nat
  base : Nat
  cap : Nat
  chunkWaitNumer : Nat := 1
  chunkWaitDenom : Nat := 3
  deriving Inhabited

/-- `DoomslugTimer::get_delay`: `min(cap, base + base / 10 * max(n - 2, 0))`. -/
def Delays.delay (d : Delays) (n : Nat) : Nat :=
  min d.cap (d.base + d.base / 10 * (n - 2))

structure Tip where
  hash : CryptoHash
  height : BlockHeight

structure Doomslug where
  delays : Delays
  /-- `DoomslugThresholdMode::TwoThirds` when true; `NoApprovals` otherwise. -/
  twoThirds : Bool := true
  trackers : Std.HashMap UInt64 AtHeight := {}
  largestTargetHeight : BlockHeight
  largestFinalHeight : BlockHeight := 0
  largestThresholdHeight : BlockHeight := 0
  largestApprovalHeight : BlockHeight := 0
  tip : Tip := ⟨CryptoHash.zero, 0⟩
  endorsementPending : Bool := false
  timer : Timer

def Doomslug.new (now : Nat) (largestTargetHeight : BlockHeight) (delays : Delays) : Doomslug :=
  { delays, largestTargetHeight, timer := ⟨now, now, 0⟩ }

/-- `set_tip`: the new head restarts the timer and makes an endorsement pending. -/
def Doomslug.setTip (ds : Doomslug) (hash : CryptoHash) (height lastFinalHeight : BlockHeight)
    (now : Nat) : Doomslug :=
  -- `should_retain_height`
  let keep (h : UInt64) : Bool :=
    h > (if height ≥ 20 then height - 20 else 0) &&
      h ≤ height + maxHeightsAheadToStoreApprovals.toUInt64
  { ds with
    tip := ⟨hash, height⟩, largestFinalHeight := lastFinalHeight,
    timer :=
      { ds.timer with
        height := height + 1, started := now },
    trackers := ds.trackers.filter fun h _ => keep h, endorsementPending := true }

/-- `Approval::new` from the tip for a target height. -/
private def Doomslug.approval (ds : Doomslug) (s : Signer) (target : BlockHeight) : Approval :=
  newApproval s ds.tip.hash ds.tip.height target

/-- `process_timer`: the approvals to send now. -/
def Doomslug.processTimer (ds : Doomslug) (now : Nat) (signer : Option Signer) :
    Doomslug × Array Approval :=
  Id.run do
    let mut ds := ds
    let mut out : Array Approval := #[]
    for _ in [0:maxTimerIters] do
      let skipDelay := ds.delays.delay (ds.timer.height - ds.largestFinalHeight).toNat
      if ds.endorsementPending && now ≥ ds.timer.lastEndorsementSent + ds.delays.endorsement then
        if ds.tip.height ≥ ds.largestTargetHeight then
          ds := { ds with largestTargetHeight := ds.tip.height + 1 }
          if let some s := signer then
            out := out.push (ds.approval s (ds.tip.height + 1))
        ds :=
          { ds with
            timer := { ds.timer with lastEndorsementSent := now }, endorsementPending := false }
      if now ≥ ds.timer.started + skipDelay then
        ds := { ds with largestTargetHeight := max (ds.timer.height + 1) ds.largestTargetHeight }
        if let some s := signer then
          out := out.push (ds.approval s (ds.timer.height + 1))
        ds :=
          { ds with
            timer :=
              { ds.timer with
                started := ds.timer.started + skipDelay, height := ds.timer.height + 1 } }
      else
        break
    return (ds, out)

/-- `on_approval_message_internal`. -/
def Doomslug.onApprovalInternal (ds : Doomslug) (a : Approval) (stakes : Array ApprovalStake)
    (now : Nat) : Doomslug × Readiness :=
  let h := (ds.trackers[a.targetHeight]?).getD {}
  let (h, r) := h.process a stakes now
  let r := if ds.twoThirds then r else .readySince now
  let ds := { ds with trackers := ds.trackers.insert a.targetHeight h }
  let ds :=
    if a.targetHeight > ds.largestApprovalHeight then
      { ds with largestApprovalHeight := a.targetHeight }
    else ds
  let ds :=
    if r != .notReady && a.targetHeight > ds.largestThresholdHeight then
      { ds with largestThresholdHeight := a.targetHeight }
    else ds
  (ds, r)

/-- `on_approval_message`: an approval for a height the node can still use. -/
def Doomslug.onApproval (ds : Doomslug) (a : Approval) (stakes : Array ApprovalStake) (now : Nat) :
    Doomslug :=
  if
      a.targetHeight < ds.tip.height ||
        a.targetHeight > ds.tip.height + maxHeightsAheadToStoreApprovals.toUInt64 then
    ds
  else (ds.onApprovalInternal a stakes now).1

/-- `get_witness`: the approvals of `(prev_hash, parent_height)` for `target_height`. -/
def Doomslug.witness (ds : Doomslug) (prevHash : CryptoHash)
    (parentHeight targetHeight : BlockHeight) : Array (AccountId × Approval × Nat) :=
  let inner := approvalInner prevHash parentHeight targetHeight
  match ds.trackers[targetHeight]? >>= (·.tracker? inner) with
  | none => #[]
  | some t => t.witness.toArray.map fun (_, (a, at_)) => (a.accountId, a, at_)

/-- `ready_to_produce_block`: whether a block for `target_height` on the tip can be produced now. -/
def Doomslug.readyToProduce (ds : Doomslug) (targetHeight : BlockHeight) (chunks : ChunksReadiness)
    (now : Nat) : Doomslug × Bool :=
  let inner := approvalInner ds.tip.hash ds.tip.height targetHeight
  match ds.trackers[targetHeight]? with
  | none => (ds, false)
  | some h =>
    match h.tracker? inner with
    | none => (ds, false)
    | some t =>
      let (t, r) := t.readiness now
      let r := if ds.twoThirds then r else .readySince now
      let ds := { ds with trackers := ds.trackers.insert targetHeight (h.setTracker inner t) }
      match r with
      | .notReady => (ds, false)
      | .readySince since =>
        match chunks with
        | .ready _ => (ds, true)
        | .notReady =>
          let wait :=
            ds.delays.delay (ds.timer.height - ds.largestFinalHeight).toNat *
                ds.delays.chunkWaitNumer /
              ds.delays.chunkWaitDenom
          (ds, now > since + wait)

end Near.Node.Validator
