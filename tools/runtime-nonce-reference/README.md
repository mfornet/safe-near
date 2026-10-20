# Nonce admission conformance

```sh
just near-nonce-conformance /absolute/path/to/pinned/nearcore
```

The checkout must be revision `44f7ae6cd7ef08bab604e20a473bf77e35d4c993`, with
no tracked changes. Its Rust 1.93.0 toolchain and nearcore native dependencies
are required. The builder appends an adapter child module to `verifier.rs`,
reexports its entry point from `lib.rs`, adds a binary declaration, then restores
all three files in `finally`. No original implementation is rewritten. This
adapter calls the actual private `verify_nonce`; the version gate queries the
pinned `StrictNonce` feature table, matching `ValidatedTransaction::new`.
The financial and nonce builders hold a shared checkout lock for their overlays.
Build metadata records revision, restored source cleanliness, binary, adapter,
driver and lock hashes, toolchain and features in `audit/nonce-reference-build.json`.

The 126 comparisons cover v84/85/86, monotonic and strict modes, optional/zero
block height, stale/equal/jumping nonces, ceiling equality, saturated height
multiplication, checked increment overflow and overlapping-error precedence.
All wire numbers must fit u64. The ceiling is `min(height * 1_000_000, u64::MAX)`;
nonces equal to it are rejected. Apply always supplies a known height; the
optional-height cases test the reference's standalone admission routine.

This compares the nonce component and feature gate, not signature verification,
pending mempool nonce overlays, gas-key nonce slots, full transaction validation
or receipt execution. The Lean transaction record models strict regular-key
semantics; it does not by itself decode native v1 transaction bytes.

CI runs these comparisons in the queued `Runtime reference components` workflow,
so a cold build can finish and save its cache despite newer pushes. Lean scenario
and axiom checks remain in the separate `wasm` workflow.
