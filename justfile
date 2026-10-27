# Safe NEAR. Run `just` to list recipes; `just <recipe> <contract>` takes a name from contracts/.
set shell := ["bash", "-euo", "pipefail", "-c"]

import 'tools/justfile'

[private]
default:
    @just --list --unsorted

# List the contracts in the dataset and whether they have a verification project.
list:
    @for d in contracts/*/; do \
        n=$(basename "$d"); \
        if [ -f "$d/verification/lakefile.toml" ]; then echo "$n  (verification)"; else echo "$n"; fi; \
    done

# Build the Lean verification project of one contract (Model, Spec, Proofs). Open `sorry`s are warnings.
build contract: (_check contract)
    cd contracts/{{ contract }}/verification && lake build

# Build the verification projects of every contract that has one.
build-all:
    @for d in contracts/*/verification; do \
        [ -f "$d/lakefile.toml" ] || continue; \
        echo "== $d"; (cd "$d" && lake build); \
    done

# Audit transitive sorry dependencies, preserving build and audit failures.
sorries contract: (_check contract)
    python3 tools/axiom-audit.py contracts/{{ contract }}/verification --allow-sorry --report audit/{{ contract }}-sorries.json

# Build the web blueprint of one contract (contracts/<name>/verification/blueprint/web/).
blueprint contract: (_check contract)
    @test -d contracts/{{ contract }}/verification/blueprint/src || \
        { echo "contracts/{{ contract }} has no leanblueprint (see its blueprint/README.md)"; exit 1; }
    cd contracts/{{ contract }}/verification && just blueprint-web

# (Served by the launchd agent com.safe-near.blueprint from ~/Library/Application Support/safe-near/blueprint.)
# Build one contract's web blueprint and publish it at https://obiteum-mac-studio.tail9c65ff.ts.net:8444/<contract>/.
publish-blueprint contract: (blueprint contract)
    rsync -a --delete contracts/{{ contract }}/verification/blueprint/web/ \
        "$HOME/Library/Application Support/safe-near/blueprint/{{ contract }}/"
    @echo "https://obiteum-mac-studio.tail9c65ff.ts.net:8444/{{ contract }}/"

# Build near-lean: the Wasm interpreter, the boundary interface, the VM, the runtime, the chain layer, the crypto package and the node.
near-build:
    @for d in near-lean/wasm near-lean/interface near-lean/vm near-lean/runtime near-lean/chain near-lean/crypto near-lean/fastvm near-lean/node; do \
        echo "== $d"; (cd "$d" && lake build); \
    done

# Run the near-lean test suites (VM, runtime and chain scenarios on the real wNEAR binary).
near-test:
    cd near-lean/vm && lake build vm-tests && ./.lake/build/bin/vm-tests
    cd near-lean/runtime && lake build runtime-tests finance-replay nonce-replay allowance-replay && ./.lake/build/bin/runtime-tests
    cd near-lean/chain && lake build chain-tests && ./.lake/build/bin/chain-tests

# Test the wNEAR argument encoding and checked receipt-graph observations.
runtime-adapter-test:
    cd contracts/w-near/verification && lake build runtime-adapter-tests && ./.lake/build/bin/runtime-adapter-tests

# Run the wNEAR differential scenarios: timelines of receipts on the binary and on the model, checked against `Refines`.
wnear-scenarios *args:
    cd contracts/w-near/verification && lake build wnear-scenarios && ./.lake/build/bin/wnear-scenarios {{ args }}

# Stress the wNEAR function contracts: run single functions of the binary and check each contract.
wnear-harness *args:
    cd contracts/w-near/verification && lake build wnear-harness && ./.lake/build/bin/wnear-harness {{ args }}

# Validate the M2 walking skeleton, budget edges and malformed-overlay regression.
wnear-skeleton:
    cd contracts/w-near/verification && lake build wnear-skeleton && ./.lake/build/bin/wnear-skeleton
    cd contracts/w-near/verification && lake env lean --run Skeleton/OverlayProbe.lean

# Audit every wNEAR model/spec/proof declaration, including transitive axioms.
wnear-audit:
    python3 tools/axiom-audit.py contracts/w-near/verification --allow-sorry-module Proofs.Refinement --report audit/wnear.json

# Compare every normalized VM observation, including gas, against pinned nearcore.
near-conformance:
    python3 tools/runtime-conformance/compare.py

# Regenerate near-lean/vm/configs from nearcore's parameter tables (needs cargo).
near-configs:
    cd tools/dump-runtime-config && cargo run --locked --release -- ../../near-lean/vm/configs

# Rebuild one contract's wasm from its pinned source and compare with the on-chain hash.
reproduce contract:
    tools/verify_build.sh contracts/{{ contract }}

[private]
_check contract:
    @test -f contracts/{{ contract }}/verification/lakefile.toml || \
        { echo "contracts/{{ contract }}/verification has no lakefile.toml (see \`just list\`)"; exit 1; }

# Compare transaction gas purchase and refunds to the pinned nearcore runtime.
near-finance-conformance checkout:
    cd near-lean/runtime && lake build finance-replay --wfail
    python3 tools/runtime-finance-reference/build.py {{ checkout }}
    python3 tools/runtime-finance-reference/compare.py {{ checkout }}/target/debug/safe-near-finance-reference

# Compare nonce admission to the pinned nearcore private validator.
near-nonce-conformance checkout:
    cd near-lean/runtime && lake build nonce-replay --wfail
    python3 tools/runtime-nonce-reference/build.py {{ checkout }}
    python3 tools/runtime-nonce-reference/compare.py {{ checkout }}/target/debug/safe-near-nonce-reference

# Compare best-effort key refunds and constructor metadata to native nearcore.
near-allowance-conformance checkout:
    cd near-lean/runtime && lake build allowance-replay --wfail
    python3 tools/runtime-finance-reference/build.py {{checkout}}
    python3 tools/runtime-finance-reference/compare_allowance.py {{checkout}}/target/debug/safe-near-finance-reference

# Compare delayed receipt-result delivery through native and Lean full runtimes.
# Full gas/balance/refund differences remain explicit in the generated report.
near-receipt-conformance checkout:
    cd near-lean/chain && lake build receipt-replay --wfail
    python3 tools/runtime-receipt-reference/build.py {{checkout}}
    python3 tools/runtime-receipt-reference/compare.py {{checkout}}/target/debug/safe-near-receipt-reference --scope receipt-results
