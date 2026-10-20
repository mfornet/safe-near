# Receipt-result conformance against pinned native NEAR

This harness executes real wNEAR and a small caller/callback contract through
nearcore's `Runtime::apply`, Wasmtime, and a real trie, then replays the same
receipt deliveries through Lean's public `Near.step` / `Near.apply` / `NearVM.run`.
The native source is pinned to `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, protocol
86. `build.py` requires a clean checkout, overlays only a visibility module and
binary declaration, serializes overlays with the other native adapters, and
restores the checkout in `finally`. Build hashes and compiler metadata are saved
in `audit/receipt-reference-build.json`.

From the repository root:

```sh
just near-receipt-conformance /path/to/clean/pinned/nearcore
```

The recipe builds the Lean replay and native adapter and explicitly selects
`--scope receipt-results`. Ten scenarios cover:

- wNEAR withdrawal returning the transfer receipt, forwarding its listeners,
  postponing the callback, retaining receipts across multiple empty blocks,
  and resuming the callback in the apply that receives its final input;
- failed payout after account deletion: failed data reaches the callback and
  the committed token burn remains;
- callback out of gas: result delivery still completes but callback writes roll
  back; waiting does not replenish its prepaid gas;
- unrelated receipt execution during withdrawal delay;
- direct value return and guest panic;
- a successful VM invocation followed by failed storage staking: storage rolls
  back and only failed result data is sent;
- data arriving before its callback;
- a final non-call action clearing an earlier function-call promise return;
- chunk gas limits retaining receipts in the runtime's delayed queue.

Each backend must satisfy independent causal assertions, then their receipt-result
observations must match. Only opaque receipt/data names are renamed. Account
existence and storage usage, all inspected contract bytes, ordinary deposits,
prepaid child/callback gas, result targets, dependencies, data payloads, action
ordering, logs, statuses and queue lengths remain exact. Unknown failures or
unsupported output actions are errors. Failure encodings are compared by an
explicit recognized error category; raw backend diagnostics remain in the report.

## Full financial comparisons are separate and currently fail

The receipt-result observation explicitly excludes account balances, outcome
`gasBurnt`/`tokensBurnt`, and system refund transfer amounts. Both complete raw
traces and every full-trace difference are retained in
`audit/receipt-conformance.json`; they are not an allowlist or a claim of full
runtime equivalence. To require complete agreement:

```sh
python3 tools/runtime-receipt-reference/compare.py \
  /path/to/nearcore/target/debug/safe-near-receipt-reference --scope full
```

That command currently exits nonzero. Real-trie storage accesses charge costs
absent from Lean's map storage model. Native initialization also charges
`storage_remove_ret_value_byte`, currently absent from Lean's postcharge. Native
system refund transfers report execution gas (223182562500 gas in these fixtures)
even though their monetary gas burn is zero; Lean currently skips that execution
gas. These differences propagate into receiver rewards, account balances and
refund amounts. Fixing receipt-result routing does not establish general gas or
trie-cost fidelity.

## Exact seam and remaining trust boundaries

The test injects already-funded action receipts. It does not admit signed
transactions, verify signatures, derive a genesis state from the blockchain, run
consensus, or simulate cross-shard routing. Delivery selection is a shared test
input, preserving selected order and retaining the rest, rather than a native
network oracle. It deliberately explores callback/data ordering and arbitrary
finite delays. Per-shard routing, FIFO constraints, congestion/bandwidth scheduling,
and eventual network/runtime progress require separate modeling and review.
There is no fixed block bound, and eventual processing does not imply success.
`NearChain.History` defines histories, supported execution and `DeliveryFair`
explicitly. Fair delivery guarantees arrival only; progress through gas-delayed
work and dependency resolution needs separate premises. An indefinitely
delegating contract can keep a logical result pending even under fair delivery.

Production protocol-86 configuration is used; native VM kind is overridden to
Wasmtime for portability. Genesis accounts, code storage usage, gas prices and
injected receipt IDs are constructed by the adapters. Keys are empty Ed25519
keys. No execution results, generated receipts or refund logic are mocked.

Native executes the pinned Wasm bytes; Lean executes the associated WAT through
its supplied code table. The fixture manifest hashes wNEAR, the caller Wasm and
caller WAT. Caller compilation used the recorded `wasm-tools` version:

```sh
wasm-tools parse tools/runtime-receipt-reference/fixtures/caller.wat \
  -o tools/runtime-receipt-reference/fixtures/caller.wasm
wasm-tools validate tools/runtime-receipt-reference/fixtures/caller.wasm
```

A checked binary decoder and a universal refinement from actual nearcore remain
outside this finite differential test. The report records tested schedules, not
a proof of fairness or exhaustive interleaving coverage.
