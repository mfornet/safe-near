#!/usr/bin/env bash
# Omni Bridge (NEAR side)
# Rebuilds contract.wasm from source/ (pinned at 3124f85f7b02c45ad4517b059525963d53a7aab9) into build/contract.wasm.
# Method: cargo-near-reproducible. Requirements: docker, cargo-near (https://github.com/near/cargo-near).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=3124f85f7b02c45ad4517b059525963d53a7aab9
UPSTREAM=https://github.com/Near-One/omni-bridge
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/omni-bridge/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-omni-bridge.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
export PATH="$HOME/.cargo/bin:$PATH"
# cargo-near runs the build inside the docker image pinned in Cargo.toml
# ([package.metadata.near.reproducible_build]: sourcescan/cargo-near:0.21.1-rust-1.96.0@sha256:ccb22bb4e677ed022d8b9d1aa1b32f0af52dd0471ef1c32e48dedbf68ee6ee17).
# Run from inside the clone: cargo-near discovers the git repository from the working directory.
(cd "$REPO/near/omni-bridge" && cargo near build reproducible-wasm)
cp "$REPO/near/target/near/omni_bridge/omni_bridge.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
