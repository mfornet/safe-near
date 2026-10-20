# Safe NEAR

Formally verify NEAR smart contracts.

Check the [human written notes](notes/README.md).

## Notes

`notes/` holds the human-written notes: the design of each component, the
plan for what is being worked on, and the TODO list. Start at
[notes/README.md](notes/README.md). The folder is written by humans only; see
[notes/AGENTS.md](notes/AGENTS.md).

## Checks

Pushes and pull requests run one Python-only job: Lean pin consistency and offline
tooling regressions, with a five-minute limit. Run the same checks with `just ci-check`.
This fast gate does not certify Lean proofs or native equivalence.

Run the expensive validation locally during the weekly periodic review:

```sh
just periodic-check-plan
just periodic-check /path/to/clean/pinned/nearcore
```

The checkout must be at `44f7ae6cd7ef08bab604e20a473bf77e35d4c993` for the
finance/nonce adapters. Install the pinned Lean/Rust toolchains and
`wasm-tools 1.251.0`, initialize the Wasm testsuite submodule, and allow time and
disk space for cold nearcore builds. The full-chain oracle uses its own clean
source cache. The runner builds packages sequentially, checks the Wasm report and
program reproducibility, runs all scenarios and native suites, and audits every
core/wNEAR declaration. It stops on the first failure and saves commands, source
revision, working-tree status, logs, and timings under `audit/periodic/`.

The existing large GitHub workflows remain available through **Run workflow**
when explicitly needed; they do not run on pushes, pull requests, or a schedule.
The local command covers their executable checks. The broader
[periodic review](notes/design/PERIODIC_CHECK.md) also includes architecture,
documentation, blueprint and contract-reproduction review. Human-only notes are
maintained separately.

## Contracts dataset

`contracts/` holds one folder per on-chain binary: the binary, its NEAR code
hash, a reproducible `build.sh`, and the upstream source pinned as a git
submodule. See [contracts/README.md](contracts/README.md) for the format and
[contracts/CATALOG.md](contracts/CATALOG.md) for the list of contracts.

```
git submodule update --init contracts/<name>/source   # fetch the pinned source
tools/verify_build.sh contracts/<name>              # rebuild and compare hashes
```
