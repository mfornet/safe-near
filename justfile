# Safe NEAR. Run `just` to list recipes; `just <recipe> <contract>` takes a name from contracts/.
set shell := ["bash", "-euo", "pipefail", "-c"]

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

# Rebuild one contract's wasm from its pinned source and compare with the on-chain hash.
reproduce contract:
    tools/verify_build.sh contracts/{{contract}}

[private]
_check contract:
    @test -f contracts/{{contract}}/verification/lakefile.toml || \
        { echo "contracts/{{contract}}/verification has no lakefile.toml (see \`just list\`)"; exit 1; }
