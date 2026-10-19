import NearRuntime

/-!
# Chain steps

A `Snapshot` is a chain state together with the receipts in flight. One
`step` applies a block (transactions and the pending receipts) and yields
the next snapshot. `Reachable` closes `step` under any sequence of blocks.
Everything is defined from `Near.apply`; nothing is axiomatised.
-/

namespace Near

open Wasm.Near

/-- The decoder for contract code deployed by contracts. Binary decoding is
not available in Lean yet, so a chain is run with a table of known code. -/
abbrev CodeTable := Bytes → ContractCode

structure Snapshot where
  state : ChainState
  /-- Outgoing receipts of the previous block, incoming for the next. -/
  pending : List Receipt := []
  deriving Inhabited

/-- One block: its context and transactions. -/
structure Block where
  ap : ApplyState
  txs : List Transaction
  deriving Inhabited

def step (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot) (b : Block) : Snapshot × ApplyResult :=
  let r := apply cfg b.ap codeOf s.state b.txs s.pending
  if r.issue.isSome then (s, r)
  else ({ state := r.state, pending := r.outgoing }, r)

/-- Every chain step exposes the exact apply result, including rejected attempts. -/
theorem step_applyResult (cfg : RuntimeConfig) (codeOf : CodeTable) (s : Snapshot) (b : Block) :
    (step cfg codeOf s b).2 = apply cfg b.ap codeOf s.state b.txs s.pending := by
  unfold step
  dsimp only
  split <;> rfl

theorem step_issue_unchanged (cfg : RuntimeConfig) (codeOf : CodeTable)
    (s : Snapshot) (b : Block)
    (h : (apply cfg b.ap codeOf s.state b.txs s.pending).issue.isSome = true) :
    (step cfg codeOf s b).1 = s := by
  simp [step, h]

/-- States reachable from `genesis` by applying blocks. -/
inductive Reachable (cfg : RuntimeConfig) (codeOf : CodeTable) (genesis : Snapshot) : Snapshot → Prop
  | refl : Reachable cfg codeOf genesis genesis
  | step {s : Snapshot} (b : Block) : (step cfg codeOf s b).2.issue = none →
      Reachable cfg codeOf genesis s →
      Reachable cfg codeOf genesis (step cfg codeOf s b).1

/-- First-step reachability from the public step result. Keeping this transport
abstract prevents proof inference from evaluating a concrete transaction batch. -/
theorem Reachable.firstStep (cfg : RuntimeConfig) (codeOf : CodeTable) (genesis : Snapshot) (b : Block)
    (h : (Near.step cfg codeOf genesis b).2.issue = none) :
    Reachable cfg codeOf genesis (Near.step cfg codeOf genesis b).1 := by
  exact Reachable.step (cfg := cfg) (codeOf := codeOf) (genesis := genesis)
    (s := genesis) b h Reachable.refl

/-- No receipt in flight, delayed, or waiting for data. -/
def Snapshot.quiescent (s : Snapshot) : Bool :=
  s.pending.isEmpty && s.state.delayed.isEmpty && s.state.postponed.isEmpty

inductive RunStop
  | quiescent
  | fuelExhausted
  | executionIssue (receiptId : ReceiptId) (issue : ExecutionIssue)
  deriving Repr, BEq, Inhabited

/-- A bounded run explicitly reports whether it finished, exhausted its block
budget, or encountered semantics the model cannot execute. -/
structure RunResult where
  snapshot : Snapshot
  applies : List ApplyResult
  stop : RunStop

def RunResult.finish (s : Snapshot) (rs : List ApplyResult) : RunResult :=
  { snapshot := s, applies := rs,
    stop := if s.quiescent then .quiescent else .fuelExhausted }

theorem RunResult.finish_quiescent_iff (s : Snapshot) (rs : List ApplyResult) :
    (RunResult.finish s rs).stop = .quiescent ↔ s.quiescent = true := by
  simp only [RunResult.finish]
  split <;> simp_all

/-- Apply empty blocks until quiescent (at most `fuel` of them). A pending
callback without its data is incomplete even if no receipt can run now. -/
def settle (cfg : RuntimeConfig) (codeOf : CodeTable) (ap : ApplyState) (s : Snapshot) (fuel : Nat := 64) :
    RunResult :=
  match fuel with
    | 0 => .finish s []
    | n + 1 =>
      if s.quiescent then .finish s []
      else
        let (s', r) := step cfg codeOf s { ap, txs := [] }
        match r.issue with
        | some (rid, issue) => { snapshot := s', applies := [r], stop := .executionIssue rid issue }
        | none =>
          let rest := settle cfg codeOf ap s' n
          { rest with applies := r :: rest.applies }

/-- Reported completion means no pending, delayed, or postponed receipt remains,
even when the last available block consumes the entire settlement budget. -/
theorem settle_completed_quiescent (cfg : RuntimeConfig) (codeOf : CodeTable)
    (ap : ApplyState) (s : Snapshot) (fuel : Nat)
    (h : (settle cfg codeOf ap s fuel).stop = .quiescent) :
    (settle cfg codeOf ap s fuel).snapshot.quiescent = true := by
  induction fuel generalizing s with
  | zero => exact (RunResult.finish_quiescent_iff s []).mp h
  | succ fuel ih =>
    by_cases hs : s.quiescent = true
    · simp [settle, hs, RunResult.finish]
    · cases hr : step cfg codeOf s { ap, txs := [] } with
      | mk next result =>
        cases hi : result.issue with
        | none =>
          have complete : (settle cfg codeOf ap next fuel).stop = .quiescent := by
            simpa [settle, hs, hr, hi] using h
          simpa [settle, hs, hr, hi] using ih next complete
        | some issue => simp [settle, hs, hr, hi] at h

/-- Run `txs` and everything they cause, with nothing else interleaved. -/
def runIsolated (cfg : RuntimeConfig) (codeOf : CodeTable) (ap : ApplyState) (s : Snapshot)
    (txs : List Transaction) (fuel : Nat := 64) : RunResult :=
  let (s1, r1) := step cfg codeOf s { ap, txs }
  match r1.issue with
  | some (rid, issue) => { snapshot := s1, applies := [r1], stop := .executionIssue rid issue }
  | none =>
    let settled := settle cfg codeOf ap s1 fuel
    { settled with applies := r1 :: settled.applies }

theorem runIsolated_completed_quiescent (cfg : RuntimeConfig) (codeOf : CodeTable)
    (ap : ApplyState) (s : Snapshot) (txs : List Transaction) (fuel : Nat)
    (h : (runIsolated cfg codeOf ap s txs fuel).stop = .quiescent) :
    (runIsolated cfg codeOf ap s txs fuel).snapshot.quiescent = true := by
  cases hr : step cfg codeOf s { ap, txs } with
  | mk next result =>
    cases hi : result.issue with
    | none =>
      have complete : (settle cfg codeOf ap next fuel).stop = .quiescent := by
        simpa [runIsolated, hr, hi] using h
      simpa [runIsolated, hr, hi] using settle_completed_quiescent cfg codeOf ap next fuel complete
    | some issue => simp [runIsolated, hr, hi] at h

/-! ## Predicates on transitions -/

def Action.upgrades : Action → Bool
  | .deployContract _ | .deleteAccount _ => true
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
      | .data _ => false)

def Transaction.touches (u : AccountId) (tx : Transaction) : Bool :=
  tx.signerId == u || tx.receiverId == u

/-- Every receipt already in flight, including delayed and postponed work. -/
def Snapshot.inFlight (s : Snapshot) : List Receipt :=
  s.pending ++ s.state.delayed ++ s.state.postponed.map (·.2)

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
  if result.stop == .quiescent &&
      result.applies.all (fun r => r.issue.isNone && r.outcomes.all (fun (_, o) => o.status.isSuccess)) then
    some (gasBurnt result.applies)
  else none

end Near
