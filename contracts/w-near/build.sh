#!/usr/bin/env bash
# Wrapped NEAR (wNEAR)
# Rebuilds contract.wasm from source/ (pinned at 54f8267436058567b66efdaba3e790394f7f1529) into build/contract.wasm.
# Method: docker-script. Requirements: docker.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=54f8267436058567b66efdaba3e790394f7f1529
UPSTREAM=https://github.com/near/core-contracts
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/w-near/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-w-near.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
# SAFE_NEAR_IMAGE / SAFE_NEAR_TOOLCHAIN can override the pinned image and rustup toolchain for experiments;
# SAFE_NEAR_RUSTFLAGS the flags (unset `-s` to keep the name section, as tools/wasm_names.py needs).
IMAGE="${SAFE_NEAR_IMAGE:-rust:1.51.0}"
TOOLCHAIN="${SAFE_NEAR_TOOLCHAIN-}"
SETUP="rustup target add wasm32-unknown-unknown"
RUSTFLAGS_VALUE="${SAFE_NEAR_RUSTFLAGS--C link-arg=-s}"
if [ -n "$TOOLCHAIN" ]; then SETUP="rustup toolchain install $TOOLCHAIN && rustup default $TOOLCHAIN && $SETUP"; fi
# CARGO_NET_GIT_FETCH_WITH_CLI: libgit2 in old images can no longer fetch the crates.io index from GitHub.
docker run --rm --platform "${SAFE_NEAR_PLATFORM:-linux/amd64}" \
  -v "$REPO:/host" -w /host/w-near \
  -e RUSTFLAGS="$RUSTFLAGS_VALUE" \
  -e CARGO_NET_GIT_FETCH_WITH_CLI=true \
  "$IMAGE" bash -c "$SETUP && cargo build --target wasm32-unknown-unknown --release"
cp "$REPO/w-near/target/wasm32-unknown-unknown/release/w_near.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
