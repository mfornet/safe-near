# wNEAR refinement: misstatement log

Every wrong statement caught during the refinement campaign
([wnear_refinement_proof.md](wnear_refinement_proof.md), section 6). A
statement caught here before its proof was finished is a detour that did not
happen: that is the point of the log.

Before writing a new contract, skim the root causes below: the same mistake
tends to come back in another place.

## Entry format

```
### <n>. <short title>

- **Statement:** the declaration and what it claimed.
- **Truth:** what actually holds.
- **Caught by:** harness / call site / failed proof / review / scenario.
- **Root cause:** the wrong assumption about the code, the runtime or the model.
- **Sweep:** where else the same mistake was looked for, and what was fixed.
- **Test added:** the harness test or scenario that would have caught it.
```

## Entries

### 1. `__multi3`'s cost: activation miscounted

- **Statement:** `Harness.multi3.cost`: 72 `regular_op_cost`.
- **Truth:** 80: the activation is 20 (64 bytes, 36 of parameters, 56 of
  seven `i64` locals, in 8-byte units), not 12; the 60 instructions were right.
- **Caught by:** harness (every input burnt 80).
- **Root cause:** the activation was estimated from the parameters only;
  `activationGas` counts the declared locals too.
- **Sweep:** `memcpy`, `memset`, `bcmp` recounted with locals: right.
- **Test added:** the cost check of `wnear-harness` on every input.

### 2. `bcmp`'s cost: loop body miscounted

- **Statement:** `Harness.bcmp.cost`: `30 + 18k` for the `k` pairs compared.
- **Truth:** 24 per equal pair (23 instructions and the back-edge charge of
  `br 0`), and two shapes: `16 + 24n` when all `n` pairs agree, `30 + 24k`
  when pair `k` differs.
- **Caught by:** harness (stated below the burnt gas on 117 of 120 inputs).
- **Root cause:** the loop body was counted from `memcpy`'s, which it does
  not share: `bcmp` loads two bytes, compares, and exits through two
  different branches.
- **Sweep:** every cost in `Harness/Builtins.lean` is now written with its
  count in a comment, and the harness reports how many inputs it matches
  exactly.
- **Test added:** the bcmp inputs with equal ranges and with differences at
  the first and last pair.

### 3. A credit cannot mean only burnt gas

- **Statement:** the first M2 draft conserved burnt gas plus residual credits exactly.
- **Truth:** promise prepayment consumes prepaid capacity without burning gas.
  `Pays` must bound both burnt and used increases, and require the residual
  credits to fit both final limits.
- **Caught by:** design review before callers used the draft.
- **Root cause:** treating all gas consumption as instruction burn.
- **Sweep:** `GasCredits.prepay_credits`, `Pays.trans` and `WP.result` now
  include promise reservations. Boundary adequacy distinguishes committed
  `usedGas - distributedGas` from failed execution's burnt gas.
- **Regression evidence:** kernel-checked `prepay_credits` covers arbitrary
  initial promise reservations and residual credit frames.

### 4. Zero balance does not always force a storage-stake failure

- **Statement:** the initial M2 skeleton test expected zero balance to force
  a late storage-stake failure after writing a short value.
- **Truth:** `stakeDeficit` exempts accounts using at most 770 bytes
  (NEP-448). The test must include account/code storage overhead to exercise
  the intended failing branch.
- **Caught by:** the effectful skeleton's runtime validation.
- **Root cause:** counting contract records but forgetting the storage-stake
  exemption and total account storage usage.
- **Sweep:** the shared `stakeDeficit` and wNEAR model already include the
  exemption; no model or runtime correction is needed.
- **Test added:** skeleton contexts include 1000 bytes of existing account
  storage, and check that a late failure restores storage, balance, usage
  and receipts while retaining the emitted log.

### 5. Canonical trie data alone does not make overlays well formed

- **Statement:** `Context.WF` guaranteed that trie reference lookup agreed
  with the raw contract storage used by the model.
- **Truth:** the old predicate allowed duplicate keys within either overlay.
  `State.view` folds updates left to right (last duplicate wins), whereas
  reference lookup searches from the front (first duplicate wins). A canonical
  base and agreement between the view and raw storage did not exclude this.
- **Caught by:** a kernel-backed counterexample in `Skeleton/OverlayProbe.lean`
  (commit `a65583a` proves every old `Context.WF` clause uniformly, with only
  numeric bounds checked for protocol 86). Actual execution of both skeleton
  `save` and the deployed wNEAR `new` reports `executionIssue` from the storage
  accounting mismatch. The wNEAR example has empty raw storage, so it also
  represents the model's uninitialized state.
- **Root cause:** list representations of update maps lacked their uniqueness
  invariant at the refinement boundary. Base-trie canonicity says nothing
  about prospective or committed overlays.
- **Sweep:** inspected every overlay mutation in interface, VM and runtime.
  `start` creates empty maps; set/remove filter the old key before prepending;
  commit uses the same operation; rollback, reads, cache changes and checkpoint
  preserve uniqueness. Cross-overlay disjointness is deliberately not required:
  a prospective write may override a committed write.
- **Correction:** add `trie_changes_unique` to `Context.WF`, backed by
  `NearInterface/TrieOverlayInvariant.lean` preservation proofs for actual
  constructors and operations. The differential hypothesis checker rejects
  duplicate overlays too. Runtime lookup and view semantics are unchanged.
- **Regression evidence:** retain the executable mismatches outside the corrected
  premise, prove the duplicate contexts fail corrected `Context.WF`, and run
  the existing scenario and skeleton suites. This repairs the intended scope
  of runtime-constructible contexts; it is a substantive premise correction,
  not a proof of the old, false statement.

## Agent results

Success and failure per task type and model (section 11.2 of the plan), used
to move task types to a cheaper or stronger model.

| Task type | Model | Succeeded | Failed | Notes |
|---|---|---|---|---|
| Harness design and first checkers (M1) | Opus | 1 | 0 | Two cost miscounts, caught by the harness itself |
| Initial metered contracts (M2) | Codex, inherited model | 1 | 0 | Closed WP/charging proofs; full instruction and host logic remains open |
| Boundary adequacy (M2) | Codex, inherited model | 1 | 0 | Closed observation and assembly rules; low-budget premise remains open |
| Effectful skeleton validation/model (M2) | Codex, inherited model | 1 | 0 | Exact failures, two budget directions, closed checker equivalence; universal refinement open |
| Host contracts and direct-call composition (M2) | Codex, inherited model | 2 | 0 | Metered input/output, exact gas and residual frames; storage trie phase open |
| Skeleton linking/instantiation (M2) | Codex, inherited model | 1 | 0 | Original module closed; runtime-prepared memory remains open |
