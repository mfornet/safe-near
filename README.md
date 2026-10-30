# Safe NEAR

Formalizing NEAR smart contracts at the binary level using Lean.

## How it works

We verify the Wasm binary that is actually deployed on chain, not the Rust
source. To do that, everything the binary runs on is implemented in Lean:

- **Wasm** (`near-lean/wasm`): a Wasm runtime written from the specification,
  whose single executable step function is also what proofs reason about.
- **NEAR runtime** (`near-lean/vm`, `near-lean/runtime`, `near-lean/chain`):
  host functions, gas, transactions, receipts and block execution on top of the
  runtime.

Per contract, we write a high-level model of its state and methods, state the
properties we care about (for example "balances always sum to the total
supply"), prove them in Lean, and connect the model to the binary running on
the Lean runtime. The Lean implementation is tested against the official Wasm
testsuite and against nearcore.

See [notes/](notes/README.md) for the design and open work.

## Usage

```sh
just                      # list all recipes
just list                 # contracts, and which have a verification project
just build w-near         # build a contract's model, specs and proofs
just blueprint w-near     # render the blueprint linking statements to proofs
just wnear-audit          # check proofs have no sorry or extra axioms, and the pinned statements
just wnear-pin-statements # accept a change to a pinned statement (STATEMENTS.md)
just near-build           # build the Wasm interpreter and NEAR runtime
just near-test            # run the runtime test suites
just ci-check             # the fast checks CI runs on every push
```

Heavy validation (conformance against a pinned nearcore checkout, full builds)
runs locally with `just periodic-check <nearcore-checkout>`; see
[periodic checks](notes/design/PERIODIC_CHECK.md).
Three Lean workflows run automatically, each only when its packages change: the
`near-lean` workflow builds the chain package and everything below it, so a
change that breaks the build is caught on its pull request; the `wNEAR`
workflow builds the wNEAR proofs and audits their axioms and pinned statements
([proving](notes/design/PROVING.md)); the `wasm-logic`
workflow builds and checks the separation logic over the Wasm runtime
(`near-lean/wasm-logic`), which takes a few minutes with iris-lean cached.

Every Lake package enables Lake's artifact cache, so a module built once (in
any worktree, by any branch) is reused from
`~/.elan/toolchains/<toolchain>/lake/cache` instead of rebuilt. The cache is
safe to delete; it only grows, so clear it now and then.

## Contracts dataset

`contracts/` has one folder per on-chain binary: the binary, its code hash, the
upstream source pinned as a git submodule, and a script that rebuilds the binary
byte-for-byte. A proof is only meaningful for a binary we can trace back to its
source. [CATALOG.md](contracts/CATALOG.md) lists the contracts, and
[contracts/README.md](contracts/README.md) describes the format.

```sh
git submodule update --init contracts/<name>/source   # fetch the pinned source
just reproduce <name>                                 # rebuild and compare hashes
```

Verification projects exist for `w-near` (model proofs complete, deployed
refinement open), `sputnik-dao-factory` and `sputnikdao2-v3.2` (both in
progress). The sequential expansion is tracked in
[contracts/VERIFICATION.md](contracts/VERIFICATION.md); `linkdrop` is queued
again. Its binary is omitted pending redistribution permission; the runtime
supports its imports for local testing.

## License

Apache License 2.0, see [LICENSE](LICENSE). Contract binaries and other
third-party material keep their own licences; see
[THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).
