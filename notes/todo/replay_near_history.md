We have much of the differential-testing infrastructure, but **exact historical replay is not implemented yet**.

I saved a detailed [design and gap analysis](/Users/marcelo/.codex/worktrees/8766/safe-near/notes/design/HISTORICAL_RUNTIME_REPLAY.md) and linked it from the project notes/TODO.

What already exists:

- Block-pinned downloads of account state, keys, storage and contract code.
- A pinned nearcore `Runtime::apply` oracle and a Lean replay runner.
- Comparisons covering execution, receipt bytes, state bytes, identities, randomness and synthetic trie accounting.
- Tests requiring storage writes, removals and rollback to match.

The important constraint: **a few account snapshots plus filtered transactions generally cannot reproduce historical outputs exactly.** Receipts may originate before the snapshot, callbacks cross account boundaries, and original trie shape plus earlier chunk activity can affect gas, refunds and balances.

The proposed approach is:

1. Select interesting contracts, then capture the **complete shard chunks** containing their execution.
2. Export original transactions, ordered incoming receipts, queues, execution context and an original-trie witness.
3. Verify that pinned nearcore reproduces the archived result.
4. Run Lean against the same immutable bundle, comparing canonical output bytes and post-state roots.
5. Expand from one chunk to consecutive chunks and several contracts.

Nearcore already has a useful extraction seam in its [historical apply-range and recorded-storage implementation](https://github.com/near/nearcore/blob/44f7ae6cd7ef08bab604e20a473bf77e35d4c993/tools/state-viewer/src/apply_chain_range.rs).

The main missing pieces are the historical exporter, faithful epoch/shard context, external receipt ingestion, witness-backed Lean storage, and complete outcome/metadata serialization comparison.

**Recommended first milestone:** one downloadable, offline historical chunk fixture, independently checked against the archive. Establish that before building a large corpus.

Validation: 30 offline chain-tooling tests passed; execution comparisons were not rerun because the binaries are not built in this worktree.
