# Runtime financial conformance

Build the adapter against a clean checkout of nearcore revision
`44f7ae6cd7ef08bab604e20a473bf77e35d4c993` (Rust 1.93.0):

```sh
just near-finance-conformance /absolute/path/to/nearcore
```

The builder temporarily appends a child module and binary declaration to the
pinned checkout, compiles them, and restores both original files in `finally`.
It refuses tracked changes or another revision. No original runtime function is
rewritten: the child module calls `calculate_tx_cost` and the actual private
`refund_unspent_gas_and_deposits` method. Build metadata records source revision,
cleanliness after restoration, toolchain, adapter/driver/binary and lock hashes.
Reports are saved in `audit/finance-reference-build.json` and `audit/finance.json`.
The first build requires nearcore's native dependencies and can take substantial
time; subsequent builds reuse its Cargo target directory.

The Lean executable compares exact transaction burnt/remaining gas, purchased
receipt price, total debit, burn price, refund, price deficit/surplus, refund
penalty and account-creation charge. Seventy-two cases cover v84/85/86, prices
below/at/above the minimum, increasing/decreasing prices and account creation.
The supplied used/burnt gas aggregates satisfy a valid financial budget. These
are financial routine comparisons, not evidence that an action sequence can
produce each supplied aggregate. They do not execute contracts, validate
transactions, process receipt dependencies, or establish chain-level equivalence.

The pinned production refund penalty is zero; the generic Lean implementation
also models bounded relative/minimum penalties and proves the v85+ partition
identity for them. Complete receipt execution still needs its own reference seam.
