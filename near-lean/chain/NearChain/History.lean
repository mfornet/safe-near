import NearChain.Step

/-! Explicit scheduling and progress assumptions. These predicates do not
assert that an arbitrary delivery selector is a valid native shard schedule. -/
namespace Near
open Wasm.Near

/-- A supplied sequence of block contexts, transactions and delivery choices. -/
abbrev Schedule := Nat → Block

/-- State before block n; each transition uses the public step, retaining the
old snapshot when that attempt reports a modeling issue. -/
def snapshotAt (cfg : RuntimeConfig) (decoder : CodeTable) (genesis : Snapshot)
    (schedule : Schedule) : Nat → Snapshot
  | 0 => genesis
  | n + 1 => match step cfg decoder (snapshotAt cfg decoder genesis schedule n) (schedule n) with
    | .ok (next, _) => next
    | .error _ => snapshotAt cfg decoder genesis schedule n

/-- Every attempted transition is within executable model coverage. This does
not validate signatures, consensus, shard routing or native block contexts. -/
def ScheduleSupported (cfg : RuntimeConfig) (decoder : CodeTable) (genesis : Snapshot)
    (schedule : Schedule) : Prop :=
  ∀ n, ∃ next result,
    step cfg decoder (snapshotAt cfg decoder genesis schedule n) (schedule n) = .ok (next, result) ∧
    result.issue = none

/-- Every in-transit envelope is eventually selected in an accepted apply.
The witness has no uniform block bound. This is an explicit premise on an
infinite history, not an axiom or a consequence of step. It guarantees arrival
only: gas-delayed processing and resolution of dependencies require progress
of the runtime and of the producing receipts too. In particular an indefinitely
delegating contract need not ever supply a final result despite fair delivery. -/
def DeliveryFair (cfg : RuntimeConfig) (decoder : CodeTable) (genesis : Snapshot)
    (schedule : Schedule) : Prop :=
  ∀ n receipt, receipt ∈ (snapshotAt cfg decoder genesis schedule n).pending →
    ∃ later incoming deferred next result, n ≤ later ∧
      receipt ∈ (snapshotAt cfg decoder genesis schedule later).pending ∧
      (schedule later).receipts.resolve (snapshotAt cfg decoder genesis schedule later).pending =
        .ok (incoming, deferred) ∧
      receipt ∈ incoming ∧
      step cfg decoder (snapshotAt cfg decoder genesis schedule later) (schedule later) = .ok (next, result) ∧
      result.issue = none

end Near
