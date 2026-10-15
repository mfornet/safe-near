#!/usr/bin/env bash
# NEAR Intents verifier (defuse)
# Rebuilds contract.wasm from source/ (pinned at 16d04f6ec4401263f8914638710260da50bb46b0) into build/contract.wasm.
# Method: cargo-near-reproducible. Requirements: docker, cargo-near (https://github.com/near/cargo-near).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=16d04f6ec4401263f8914638710260da50bb46b0
UPSTREAM=https://github.com/near/intents
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/intents-defuse/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-intents-defuse.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
export PATH="$HOME/.cargo/bin:$PATH"
# cargo-near runs the build inside the docker image pinned in Cargo.toml
# ([package.metadata.near.reproducible_build]: sourcescan/cargo-near:0.22.0-rust-1.97.1@sha256:7467038bdddc86484b73b416eeadce926ff59013e128e53dec5a19e1cb4b2234).
# Run from inside the clone: cargo-near discovers the git repository from the working directory.
(cd "$REPO/contracts/defuse" && cargo near build reproducible-wasm)
cp "$REPO/target/near/defuse/defuse.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
