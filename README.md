# Safe NEAR

Formalizing NEAR smart contracts at the binary level using Lean.

## How it works

We verify the Wasm binary that is actually deployed on chain, not the Rust
source. To do that, everything the binary runs on is implemented in Lean:

- **Wasm** (`near-lean/wasm`, `near-lean/iris-wasm`): a Wasm interpreter and
  proof machinery for reasoning about Wasm code.
- **NEAR runtime** (`near-lean/vm`, `near-lean/runtime`, `near-lean/chain`):
  host functions, gas, transactions, receipts and block execution on top of the
  interpreter.

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
just wnear-audit          # check proofs have no sorry or extra axioms
just near-build           # build the Wasm interpreter and NEAR runtime
just near-test            # run the runtime test suites
just ci-check             # the fast checks CI runs on every push
```

Heavy validation (conformance against a pinned nearcore checkout, full builds)
runs locally with `just periodic-check <nearcore-checkout>`; see
[periodic checks](notes/design/PERIODIC_CHECK.md).

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

`w-near` is the first contract with a verification project.
