#!/usr/bin/env bash
# Top-level account contract (linkdrop) on `near`
# Rebuilds contract.wasm from source/ (pinned at 9a6bb316f6b7c83b504ce9c94a80c37178097655) into build/contract.wasm.
# Method: cargo-near-reproducible. Requirements: docker, cargo-near (https://github.com/near/cargo-near).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=9a6bb316f6b7c83b504ce9c94a80c37178097655
UPSTREAM=https://github.com/near/near-linkdrop
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/linkdrop/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-linkdrop.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
export PATH="$HOME/.cargo/bin:$PATH"
# cargo-near runs the build inside the docker image pinned in Cargo.toml
# ([package.metadata.near.reproducible_build]: sourcescan/cargo-near:0.16.0-rust-1.86.0@sha256:3220302ebb7036c1942e772810f21edd9381edf9a339983da43487c77fbad488).
# Run from inside the clone: cargo-near discovers the git repository from the working directory.
(cd "$REPO/." && cargo near build reproducible-wasm)
cp "$REPO/target/near/linkdrop.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
