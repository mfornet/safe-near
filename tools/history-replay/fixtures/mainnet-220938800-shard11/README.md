# Mainnet block 220938800, shard 11

This is a real, complete shard runtime application at protocol 86, captured with
nearcore 2.13.4 (`44f7ae6cd7ef08bab604e20a473bf77e35d4c993`). Native execution
matches the retained chain's outcome bytes, outgoing receipt bytes, gas, burned
balance and post-state root, plus the successor chunk's commitments. Offline
replay matches all deterministic captured observations. Lean execution is not
yet established.

| Property | Value |
| --- | --- |
| Block hash | `FpX49fvNFJArdkZNDKrg9yqDrXyHf9wUwBsxQFo8mSv9` |
| Shard | `11` (`s11.v3`) |
| Newly included signed transactions | 0 |
| Incoming receipts | 1, an `ActionV2` receipt with `refund_to=None` |
| Call | `v2.ref-finance.near` → `aggregate-oracle.near.list_prices_no_older_than` |
| Original signer | `watcher03.ref-watchdog.near` |
| Call input | Nine price IDs, maximum age 60 seconds, 15 Tgas, zero attached deposit |
| Execution outcomes | 1 |
| Outgoing receipts | 2: oracle data to `v2.ref-finance.near`, gas refund to the signer |
| Gas burned | `12253937078387` |
| Post-state root | `DhS9rXHxW7arA5WHCYFxDwAsF5kbVv6MpN59sCEUR9ix` |
| Outcome root | `7WuhvNL3ZXsTDkBbU5WB2j7kdAnRSnUC9iS5g5fMfSxQ` |
| Witness | 979,322 bytes, 262 original content-addressed objects |
| Contract code | One 949,959-byte Wasm module, included in the witness |
| Bundle assets | About 2 MB, including hex-encoded Borsh and code |

The original receipt bytes, ordering, pre-state root, queues, configuration and
block/epoch/shard context are retained. No account genesis or synthetic
transaction was substituted. This case exercises contract execution, original
trie reads and asynchronous data/refund generation. It does not exercise newly
included transaction signature/expiry handling or claim coverage of every action.

`manifest.json` hashes the three assets and records source/build provenance and
the exact comparison scope. The one excluded diagnostic is measured scheduler
wall-clock duration: `stats.bandwidth_scheduler.time_to_run_ms`. Its original
unmodified stats encoding and measured value are preserved in `captureTelemetry`;
all remaining stats bytes are compared. In this capture the duration was 2 ms.

## Run

From the repository root:

```sh
just history-build
just history-fixture-test
```

The fixture test relocates these assets and runs native replay and archive
verification without the capture database. It rejects eight deliberate
corruptions and checks that changing only wall-clock telemetry preserves the
result. This fixture passed the same test with OS networking denied. A fresh
verification took about 0.8 seconds and 385 MiB peak resident memory on the
capture host; these are measurements, not test thresholds.

For an explicit executable or another bundle:

```sh
just history-fixture-test --replay /path/to/safe-near-history-replay \
  --bundle tools/history-replay/fixtures/mainnet-220938800-shard11
```

## Acquisition and trust

Captured on 2026-10-21 from a non-validator mainnet node tracking the shard of
`a.near`. Public peers supplied state at sync anchor
`ATBg3cFuWhNv9oLn7DtGb7vrjerfNRoLEbypbfXhw9hV` (height 220938737), then the node
processed subsequent real blocks past the selected transition. The state
snapshot advertisement hash was `55kr4WAumzgi5Y8q3xtfjuRunihRiFiFEiRMwoWFQCUg`.
The retained selected and successor block hashes also matched separately fetched
public RPC headers. The node stopped before capture; state-viewer opened its
store read-only. Acquisition used roughly 43 GiB on disk, while this fixture
needs only the exported witness.

The build's optional outbound state-sync transport overlay changed transport
selection, leaving upstream state validation intact. Its hash is recorded in
`capture-build.json`. The retained store and capture build are trusted sources;
the offline verifier does not reverify consensus signatures or establish a
light-client chain of trust. See the [tool guide](../../README.md) for the
capture mechanism, comparison surface and remaining Lean boundary.
