import NearRuntime
import NearChain.Schedule

/-!
# Chain steps

A `Snapshot` is a chain state together with the receipts in flight. One
`step` applies a block (transactions and selected pending receipts) and yields
the next snapshot. `Reachable` closes `step` under any sequence of blocks.
Everything is defined from `Near.apply`; nothing is axiomatised.
-/

namespace Near

open Wasm.Near

/-- The decoder for contract code deployed by contracts. Binary decoding is
not available in Lean yet, so a chain is run with a table of known code. -/
abbrev CodeTable :=
  Bytes → ContractCode

structure Snapshot where
  state : ChainState
  /-- Receipts available for delivery, including work deferred by earlier blocks. -/
  pending : List Receipt := []
  deriving Inhabited

/-- One block: its context, transactions and ordered incoming delivery.
The default delivers every pending receipt, preserving the original behavior. -/
structure Block where
  ap : ApplyState
  txs : List Transaction
  receipts : ReceiptSchedule := .all
  deriving Inhabited

-- nearcore divergence: block context is arbitrary input (no height/gas-price evolution, epochs
-- or rewards) and delivery is any schedule, a superset of nearcore's per-shard receipt order.
/-- Invalid delivery schedules are rejected before applying transactions.
Supported blocks retain deferred receipts before their newly outgoing work.
Runtime-delayed and postponed queues remain governed by `Near.apply`. -/
def step (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot) (b : Block) :
    Except ScheduleError (Snapshot × ApplyResult) :=
  match b.receipts.resolve s.pending with
  | .error error => .error error
  | .ok (incoming, deferred) =>
    let r := apply cfg b.ap codeOf s.state b.txs incoming
    if r.issue.isSome then .ok (s, r)
    else .ok ({ state := r.state, pending := deferred ++ r.outgoing }, r)

/-- A successful schedule exposes the exact result of applying its selected receipts. -/
theorem step_applyResult (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot) (b : Block)
    (incoming deferred : List Receipt) (next : Snapshot) (result : ApplyResult)
    (hs : b.receipts.resolve s.pending = .ok (incoming, deferred))
    (hr : step cfg codeOf s b = .ok (next, result)) :
    result = apply cfg b.ap codeOf s.state b.txs incoming := by
  simp only [step, hs] at hr
  split at hr <;> cases hr <;> rfl

theorem step_issue_unchanged (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot) (b : Block)
    (next : Snapshot) (result : ApplyResult) (h : step cfg codeOf s b = .ok (next, result))
    (hi : result.issue.isSome = true) : next = s := by
  cases hs : b.receipts.resolve s.pending with
  | error error => simp [step, hs] at h
  | ok pair =>
    rcases pair with ⟨incoming, deferred⟩
    simp only [step, hs] at h
    split at h
    · cases h
      rfl
    · cases h
      simp_all

theorem step_supported (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot) (b : Block)
    (incoming deferred : List Receipt)
    (hs : b.receipts.resolve s.pending = .ok (incoming, deferred))
    (hi : (apply cfg b.ap codeOf s.state b.txs incoming).issue = none) :
    step cfg codeOf s b =
      .ok
        ({ state := (apply cfg b.ap codeOf s.state b.txs incoming).state,
           pending := deferred ++ (apply cfg b.ap codeOf s.state b.txs incoming).outgoing },
          apply cfg b.ap codeOf s.state b.txs incoming) := by
  simp [step, hs, hi]

/-- States reachable from `genesis` by applying blocks. -/
inductive Reachable (cfg : RuntimeConfig) (codeOf : CodeTable) (genesis : Snapshot) :
    Snapshot → Prop
  | refl : Reachable cfg codeOf genesis genesis
  |
  step {s next : Snapshot} (b : Block) (result : ApplyResult) :
    step cfg codeOf s b = .ok (next, result) →
      result.issue = none → Reachable cfg codeOf genesis s → Reachable cfg codeOf genesis next

/-- First-step reachability from the public step result. Keeping this transport
abstract prevents proof inference from evaluating a concrete transaction batch. -/
theorem Reachable.firstStep (cfg : RuntimeConfig) (codeOf : CodeTable) (genesis : Snapshot)
    (b : Block) (next : Snapshot) (result : ApplyResult)
    (hs : Near.step cfg codeOf genesis b = .ok (next, result)) (hi : result.issue = none) :
    Reachable cfg codeOf genesis next := by
  exact Reachable.step b result hs hi Reachable.refl

/-- No receipt in flight, delayed, or waiting for data. -/
def Snapshot.quiescent (s : Snapshot) : Bool :=
  s.pending.isEmpty && s.state.delayed.isEmpty && s.state.postponed.isEmpty

inductive RunStop
  | quiescent
  | fuelExhausted
  | invalidSchedule (error : ScheduleError)
  | executionIssue (receiptId : ReceiptId) (issue : ExecutionIssue)
  deriving Repr, BEq, Inhabited

/-- A bounded run explicitly reports whether it finished, exhausted its block
budget, or encountered semantics the model cannot execute. -/
structure RunResult where
  snapshot : Snapshot
  applies : List ApplyResult
  stop : RunStop

def RunResult.finish (s : Snapshot) (rs : List ApplyResult) : RunResult :=
  { snapshot := s, applies := rs, stop := if s.quiescent then .quiescent else .fuelExhausted }

theorem RunResult.finish_quiescent_iff (s : Snapshot) (rs : List ApplyResult) :
    (RunResult.finish s rs).stop = .quiescent ↔ s.quiescent = true := by
  simp only [RunResult.finish]
  split <;> simp_all

-- nearcore divergence: every settling block reuses one `ApplyState` (height, seed, gas price).
/-- Apply empty blocks until quiescent (at most `fuel` of them). A pending
callback without its data is incomplete even if no receipt can run now. -/
def settle (cfg : RuntimeConfig) (codeOf : CodeTable) (ap : ApplyState) (s : Snapshot)
    (fuel : Nat := 64) : RunResult :=
  match fuel with
  | 0 => .finish s []
  | n + 1 =>
    if s.quiescent then .finish s []
    else
      match step cfg codeOf s { ap, txs := [] } with
      | .error error => { snapshot := s, applies := [], stop := .invalidSchedule error }
      | .ok (s', r) =>
        match r.issue with
        | some (rid, issue) => { snapshot := s', applies := [r], stop := .executionIssue rid issue }
        | none =>
            let rest := settle cfg codeOf ap s' n
            { rest with applies := r :: rest.applies }

/-- Reported completion means no pending, delayed, or postponed receipt remains,
even when the last available block consumes the entire settlement budget. -/
theorem settle_completed_quiescent (cfg : RuntimeConfig) (codeOf : CodeTable) (ap : ApplyState)
    (s : Snapshot) (fuel : Nat) (h : (settle cfg codeOf ap s fuel).stop = .quiescent) :
    (settle cfg codeOf ap s fuel).snapshot.quiescent = true := by
  induction fuel generalizing s with
  | zero => exact (RunResult.finish_quiescent_iff s []).mp h
  | succ fuel ih =>
    by_cases hs : s.quiescent = true
    · simp [settle, hs, RunResult.finish]
    · cases hr : step cfg codeOf s { ap, txs := [] } with
      | error error => simp [settle, hs, hr] at h
      | ok pair =>
        rcases pair with ⟨next, result⟩
        cases hi : result.issue with
        | none =>
          have complete : (settle cfg codeOf ap next fuel).stop = .quiescent := by
            simpa [settle, hs, hr, hi] using h
          simpa [settle, hs, hr, hi] using ih next complete
        | some issue => simp [settle, hs, hr, hi] at h

/-- Run `txs` and everything they cause, with nothing else interleaved. -/
def runIsolated (cfg : RuntimeConfig) (codeOf : CodeTable) (ap : ApplyState) (s : Snapshot)
    (txs : List Transaction) (fuel : Nat := 64) : RunResult :=
  match step cfg codeOf s { ap, txs } with
  | .error error => { snapshot := s, applies := [], stop := .invalidSchedule error }
  | .ok (s1, r1) =>
    match r1.issue with
    | some (rid, issue) => { snapshot := s1, applies := [r1], stop := .executionIssue rid issue }
    | none =>
      let settled := settle cfg codeOf ap s1 fuel
      { settled with applies := r1 :: settled.applies }

theorem runIsolated_completed_quiescent (cfg : RuntimeConfig) (codeOf : CodeTable) (ap : ApplyState)
    (s : Snapshot) (txs : List Transaction) (fuel : Nat)
    (h : (runIsolated cfg codeOf ap s txs fuel).stop = .quiescent) :
    (runIsolated cfg codeOf ap s txs fuel).snapshot.quiescent = true := by
  cases hr : step cfg codeOf s { ap, txs } with
  | error error => simp [runIsolated, hr] at h
  | ok pair =>
    rcases pair with ⟨next, result⟩
    cases hi : result.issue with
    | none =>
      have complete : (settle cfg codeOf ap next fuel).stop = .quiescent := by
        simpa [runIsolated, hr, hi] using h
      simpa [runIsolated, hr, hi] using settle_completed_quiescent cfg codeOf ap next fuel complete
    | some issue => simp [runIsolated, hr, hi] at h

/-- Execute exactly the supplied blocks. An empty list reports quiescence or
an exhausted block budget; it never silently drains deferred receipts.
Invalid schedules and model issues stop before later blocks are attempted. -/
def runBlocks (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot) : List Block → RunResult
  | [] => .finish s []
  | b :: blocks =>
    match step cfg codeOf s b with
    | .error error => { snapshot := s, applies := [], stop := .invalidSchedule error }
    | .ok (next, result) =>
      match result.issue with
      | some (rid, issue) =>
        { snapshot := next, applies := [result], stop := .executionIssue rid issue }
      | none =>
        let rest := runBlocks cfg codeOf next blocks
        { rest with applies := result :: rest.applies }

theorem runBlocks_completed_quiescent (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot)
    (blocks : List Block) (h : (runBlocks cfg codeOf s blocks).stop = .quiescent) :
    (runBlocks cfg codeOf s blocks).snapshot.quiescent = true := by
  induction blocks generalizing s with
  | nil => exact (RunResult.finish_quiescent_iff s []).mp h
  | cons b blocks ih =>
    cases hr : step cfg codeOf s b with
    | error error => simp [runBlocks, hr] at h
    | ok pair =>
      rcases pair with ⟨next, result⟩
      cases hi : result.issue with
      | none =>
        have complete : (runBlocks cfg codeOf next blocks).stop = .quiescent := by
          simpa [runBlocks, hr, hi] using h
        simpa [runBlocks, hr, hi] using ih next complete
      | some issue => simp [runBlocks, hr, hi] at h

/-- Every scripted result is reachable. Rejected schedules and unsupported
execution attempts leave the last reachable snapshot unchanged. -/
theorem runBlocks_reachable (cfg : RuntimeConfig) (codeOf : CodeTable) (genesis s : Snapshot)
    (blocks : List Block) (hs : Reachable cfg codeOf genesis s) :
    Reachable cfg codeOf genesis (runBlocks cfg codeOf s blocks).snapshot := by
  induction blocks generalizing s with
  | nil => exact hs
  | cons b blocks ih =>
    cases hr : step cfg codeOf s b with
    | error error => simpa [runBlocks, hr] using hs
    | ok pair =>
      rcases pair with ⟨next, result⟩
      cases hi : result.issue with
      | none =>
        have hn := Reachable.step b result hr hi hs
        simpa [runBlocks, hr, hi] using ih next hn
      | some
        issue =>
        have hn : next = s := step_issue_unchanged cfg codeOf s b next result hr (by simp [hi])
        simpa [runBlocks, hr, hi, hn] using hs

/-! ## Predicates on transitions -/

def Action.upgrades : Action → Bool
  | .deployContract _ | .deleteAccount _ | .useGlobalContract _ => true
  | _ => false

/-- The receipt deploys code to, or deletes, `c`. -/
def Receipt.upgrades (c : AccountId) (r : Receipt) : Bool :=
  r.receiverId == c && r.actions.any Action.upgrades

def Transaction.upgrades (c : AccountId) (tx : Transaction) : Bool :=
  tx.receiverId == c && tx.actions.any Action.upgrades

/-- `u` signs, sends or receives the receipt. -/
def Receipt.touches (u : AccountId) (r : Receipt) : Bool :=
  r.predecessorId == u || r.receiverId == u ||
    (match r.receipt with
    | .action a => a.signerId == u
    | .data _ | .globalDistribution _ => false)

def Transaction.touches (u : AccountId) (tx : Transaction) : Bool :=
  tx.signerId == u || tx.receiverId == u

/-- Every receipt already in flight, including delayed and postponed work. -/
def Snapshot.inFlight (s : Snapshot) : List Receipt :=
  s.pending ++ s.state.delayed ++ s.state.postponed.map (·.2) ++ s.state.yieldReceipts.map (·.2)

/-- Account and in-flight funds, including purchased gas in every receipt queue.
Minted subsidy and burnt tokens are separate transition observations. -/
def Snapshot.totalFunds (cfg : RuntimeConfig) (s : Snapshot) : Nat :=
  s.state.totalBalance + (s.inFlight.map (Fees.receiptFunds cfg)).sum

/-- A direct-interaction filter, not a noninterference theorem. It accounts
for all existing receipt queues; contract calls can still emit new actions
affecting other accounts, so indirect effects need a semantic premise. -/
def Block.independentOf (b : Block) (s : Snapshot) (c u : AccountId) : Bool :=
  b.txs.all (fun tx => !tx.upgrades c && !tx.touches u) &&
    s.inFlight.all (fun r => !r.upgrades c && !r.touches u)

/-- Gas burnt by the recorded outcomes. This excludes reserved promise gas
and is not a sufficient prepaid-gas bound. -/
def gasBurnt (rs : List ApplyResult) : Nat :=
  (rs.map fun r => (r.outcomes.map fun (_, o) => o.gasBurnt).sum).sum

/-- Measure one isolated run with maximum attached gas. `none` means the run
did not settle or some transaction/receipt failed. Even `some n` measures
burnt gas only; it does not establish a sufficient or minimal gas budget. -/
def measureCallGasBurnt (cfg : RuntimeConfig) (codeOf : CodeTable) (ap : ApplyState) (s : Snapshot)
    (signer receiver : AccountId) (pk : PublicKey) (nonce : Nat) (method : String) (args : Bytes)
    (deposit : Nat) (fuel : Nat := 64) : Option Nat :=
  let tx : Transaction :=
    { signerId := signer, publicKey := pk, nonce, receiverId := receiver
      actions := [.functionCall method args cfg.wasm.limits.maxTotalPrepaidGas deposit] }
  let result := runIsolated cfg codeOf ap s [tx] fuel
  if
      result.stop == .quiescent &&
        result.applies.all
          (fun r => r.issue.isNone && r.outcomes.all (fun (_, o) => o.status.isSuccess)) then
    some (gasBurnt result.applies)
  else none

end Near
