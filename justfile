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
    cd contracts/{{contract}}/verification && lake build

# Build the verification projects of every contract that has one.
build-all:
    @for d in contracts/*/verification; do \
        [ -f "$d/lakefile.toml" ] || continue; \
        echo "== $d"; (cd "$d" && lake build); \
    done

# List the specs of one contract that are still proved by `sorry`.
sorries contract: (_check contract)
    cd contracts/{{contract}}/verification && (lake build 2>&1 | grep "declaration uses \`sorry\`" || echo "no sorry")

# Build the web blueprint of one contract (contracts/<name>/verification/blueprint/web/).
blueprint contract: (_check contract)
    cd contracts/{{contract}}/verification && just blueprint-web

# (Served by the launchd agent com.safe-near.blueprint from ~/Library/Application Support/safe-near/blueprint.)
# Build one contract's web blueprint and publish it at https://obiteum-mac-studio.tail9c65ff.ts.net:8444/<contract>/.
publish-blueprint contract: (blueprint contract)
    rsync -a --delete contracts/{{contract}}/verification/blueprint/web/ \
        "$HOME/Library/Application Support/safe-near/blueprint/{{contract}}/"
    @echo "https://obiteum-mac-studio.tail9c65ff.ts.net:8444/{{contract}}/"

# Build near-lean: the Wasm interpreter, the VM, the runtime and the chain layer.
near-build:
    @for d in near-lean/wasm near-lean/vm near-lean/runtime near-lean/chain; do \
        echo "== $d"; (cd "$d" && lake build); \
    done

# Run the near-lean test suites (VM, runtime and chain scenarios on the real wNEAR binary).
near-test:
    cd near-lean/vm && lake build vm-tests && ./.lake/build/bin/vm-tests
    cd near-lean/runtime && lake build runtime-tests && ./.lake/build/bin/runtime-tests
    cd near-lean/chain && lake build chain-tests && ./.lake/build/bin/chain-tests

# Test the wNEAR argument encoding and checked receipt-graph observations.
runtime-adapter-test:
    cd contracts/w-near/verification && lake build runtime-adapter-tests && ./.lake/build/bin/runtime-adapter-tests

# Audit every wNEAR model/spec/proof declaration, including transitive axioms.
wnear-audit:
    cd contracts/w-near/verification && lake build Model Spec Proofs runtime-adapter-tests
    python3 tools/axiom-audit.py contracts/w-near/verification --no-build --report audit/wnear.json

# Compare every normalized VM observation, including gas, against pinned nearcore.
near-conformance:
    python3 tools/runtime-conformance/compare.py

# Regenerate near-lean/vm/configs from nearcore's parameter tables (needs cargo).
near-configs:
    cd tools/dump-runtime-config && cargo run --release -- ../../near-lean/vm/configs

# Rebuild one contract's wasm from its pinned source and compare with the on-chain hash.
reproduce contract:
    tools/verify_build.sh contracts/{{contract}}

[private]
_check contract:
    @test -f contracts/{{contract}}/verification/lakefile.toml || \
        { echo "contracts/{{contract}}/verification has no lakefile.toml (see \`just list\`)"; exit 1; }
