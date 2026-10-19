# Scripted chain execution

`NearChain` orchestrates the trusted `Near.apply` runtime. A `Snapshot` contains
account state and pending receipts. A `Block` supplies trusted block context,
transactions, and an incoming receipt schedule.

## Receipt delivery

`Block.receipts` defaults to `.all`, which delivers the pending queue in order.
Use `.indices [2, 0]` to deliver the original third receipt before the original
first receipt. Positions refer to the queue at the start of that block, and are
recomputed from the new queue for the next block. Unselected receipts retain
their relative order and precede the block's newly outgoing receipts.

```lean
let block : Near.Block :=
  { ap := { blockHeight := 100 }, txs := [], receipts := .indices [2, 0] }
-- Requires at least three pending receipts.
match Near.step cfg codeOf snapshot block with
| .error (.unavailableIndex position) =>
  s!"Missing or repeated pending receipt position: {position}"
| .ok (next, result) =>
  s!"Pending receipts: {next.pending.length}; execution issue: {repr result.issue}"
```

An invalid position or repeated selection rejects the entire schedule before
transactions run. The input snapshot remains available to the caller. Valid
selection never fabricates a receipt or uses a receipt id to identify a queue
entry; even snapshots with repeated ids select by position.

`.indices []` defers every pending incoming receipt. Transactions and the
runtime's delayed queue still execute, and data arrivals can resume postponed
callbacks. The schedule does not bypass the runtime's gas limits or manipulate
its internal delayed/postponed queues.

`step` now returns `Except ScheduleError (Snapshot × ApplyResult)`. A model
execution limitation remains inside `ApplyResult.issue` and rolls back the
entire block, retaining both selected and deferred incoming receipts. A
schedule error is an orchestration error, not a NEAR protocol outcome.

## Block sequences and reachability

`runBlocks cfg codeOf snapshot blocks` executes exactly the supplied sequence.
It records each attempted apply, stops on a schedule error or execution issue,
and never implicitly drains the queues after the last block. `RunStop`
distinguishes quiescence, exhausted block budget, invalid schedule and execution
issue. Callers supply each block's height, timestamp and other context; the
runner does not invent later block context.

`settle` retains the automatic all-receipt delivery policy, and `runIsolated`
uses it to finish an isolated transaction sequence. `Reachable.step` covers
custom schedules through the same `step` function, requiring a valid schedule
and no model execution issue.

Kernel-checked theorems establish:

- Successful selection partitions the original receipt multiset
  (`ReceiptSchedule.resolve_perm`).
- Deferral preserves the relative order of unselected receipts
  (`ReceiptSchedule.resolve_deferred_sublist`).
- An execution issue leaves the complete input snapshot unchanged
  (`step_issue_unchanged`).
- Every scripted final snapshot is reachable, including the last committed
  snapshot retained after an invalid schedule (`runBlocks_reachable`).
- Reported completion implies no pending, delayed or postponed work remains
  (`runBlocks_completed_quiescent`, with analogous automatic-run theorems).

## Verification

Run `just near-test` from the repository root, or `lake exe chain-tests` here.
Tests cover exhaustive small schedules, reordered and deferred transfers,
atomic rejection, runtime gas delays, callbacks arriving before their data,
and real wNEAR withdrawals delivered one receipt at a time with idle blocks.

These tests exercise the Lean scheduler. They do not establish equivalence to
nearcore's full transaction/receipt runtime. The independent `Runtime::apply`
oracle and per-block differential harness remain open; the existing
`just near-conformance` compares VM calls only.
