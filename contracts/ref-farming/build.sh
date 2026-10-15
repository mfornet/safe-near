#!/usr/bin/env bash
# Ref Finance farming v1.1.0
# Rebuilds contract.wasm from source/ (pinned at fc34dd82bcfbc216d1461145679b28a05e1dc56a) into build/contract.wasm.
# Method: docker-script. Requirements: docker.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=fc34dd82bcfbc216d1461145679b28a05e1dc56a
UPSTREAM=https://github.com/DevOfCredit/ref-contracts
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/ref-farming/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-ref-farming.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
# SAFE_NEAR_IMAGE / SAFE_NEAR_TOOLCHAIN can override the pinned image and rustup toolchain for experiments.
IMAGE="${SAFE_NEAR_IMAGE:-rust:1.56.1}"
TOOLCHAIN="${SAFE_NEAR_TOOLCHAIN-}"
SETUP="rustup target add wasm32-unknown-unknown"
if [ -n "$TOOLCHAIN" ]; then SETUP="rustup toolchain install $TOOLCHAIN && rustup default $TOOLCHAIN && $SETUP"; fi
# CARGO_NET_GIT_FETCH_WITH_CLI: libgit2 in old images can no longer fetch the crates.io index from GitHub.
docker run --rm --platform "${SAFE_NEAR_PLATFORM:-linux/amd64}" \
  -v "$REPO:/host" -w /host/. \
  -e RUSTFLAGS='-C link-arg=-s' \
  -e CARGO_NET_GIT_FETCH_WITH_CLI=true \
  "$IMAGE" bash -c "$SETUP && cargo build -p ref_farming --target wasm32-unknown-unknown --release"
cp "$REPO/target/wasm32-unknown-unknown/release/ref_farming.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
