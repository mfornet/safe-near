# Partial NEAR snapshots

`near_snapshot.py` downloads selected accounts into one JSON fixture using
only Python's standard library and public, read-only RPC calls.

```sh
python3 tools/near_snapshot.py /tmp/near-fixture.json account.near other.near
python3 tools/near_snapshot.py /tmp/historical.json account.near --block 123456789
python3 tools/near_snapshot.py /tmp/testnet.json account.testnet --rpc https://archival-rpc.testnet.near.org
```

The downloader first resolves a finalized block (or the supplied height/hash),
then requests everything at that hash. Each account, code, access-key, and
storage response must report that same block. Downloaded code must hash to
both the code response's hash and the account's code hash. The output includes
the full block response and protocol configuration requested at that block.
Account balances, nonces, permissions, and raw binary storage are preserved;
JSON amounts remain decimal strings and storage stays base64-encoded.
For gas keys, the separately queried parallel nonce lanes are preserved in
`gas_key_nonces` at the same pinned block; ordinary accounts have an empty list.

The file is published atomically after all reads and checks succeed. Existing
files are never overwritten. To repeat a capture, select the saved block hash
and a new output filename. An archival RPC is normally needed for old blocks.

## Storage scope

By default, each selected account's **entire** storage is requested. The RPC
may reject large contracts. It never becomes a silently truncated snapshot.
To deliberately capture a subset, pass one or more base64 prefixes:

```sh
# STATE is U1RBVEU= in base64.
python3 tools/near_snapshot.py /tmp/state-only.json account.near --prefix-base64 U1RBVEU=
```

Every account's `storage` records `complete`, `prefixes_base64`, and the
captured `values`. Overlapping prefixes are deduplicated. Missing keys outside
the captured prefixes mean **unknown**, not absent. A runtime importer must
reject reads outside that scope or require a complete account snapshot.

Some providers enforce the state-size limit on the whole account even with a
prefix. A live capture of `wrap.near` on the default archival endpoint returned
`TOO_LARGE_CONTRACT_STATE` even for the `STATE` prefix. Such accounts require
an RPC node configured with a higher state-view limit; prefixes cannot be
relied on to bypass that limit. The downloader fails without publishing a file.

## Fixture boundary

The format is `safe-near-snapshot-v1`. `accounts` is sorted by account ID;
storage is sorted by decoded key and access keys by public key. The snapshot
is trusted RPC input: it does not verify state proofs, signatures, or consensus.
It contains selected accounts, not the whole chain, and does not include
in-flight/delayed receipts or epoch/validator state. Global contract code
references are explicitly rejected pending support for their resolution.

This is an input fixture for a future runtime importer and differential
harness. It is not sufficient to replay an arbitrary historical block.
Keep the fixture's block context and protocol configuration together; selecting
an older configuration table alone does not implement older execution semantics.

RPC field definitions: [NEAR accounts and contracts](https://docs.near.org/api/rpc/contracts),
[blocks](https://docs.near.org/api/rpc/block-chunk), and
[protocol configuration](https://docs.near.org/api/rpc/protocol).

Offline regression tests:

```sh
python3 -m unittest discover -s tools/tests -v
```
