#!/usr/bin/env bash
# Aurora Engine (EVM on NEAR)
# Rebuilds contract.wasm from source/ (pinned at f296f06ab618468dff58cbef81732b1d0ee1782e) into build/contract.wasm.
# Method: docker-script. Requirements: docker.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
COMMIT=f296f06ab618468dff58cbef81732b1d0ee1782e
UPSTREAM=https://github.com/aurora-is-near/aurora-engine
BUILD="$HERE/build"
rm -rf "$BUILD"; mkdir -p "$BUILD"
if [ ! -e "$HERE/source/.git" ]; then git -C "$HERE/../.." submodule update --init "contracts/aurora-engine/source"; fi
# Clean checkout of the pinned commit, independent of any local edits in source/.
# It lives outside this repository's working tree: cargo-near walks up to the
# top-level git repo it finds, which would otherwise be safe-near itself.
WORK="$(mktemp -d "${TMPDIR:-/tmp}/safe-near-build-aurora-engine.XXXXXX")"
REPO="$WORK/repo"
echo "work dir: $WORK"
git clone -q "$HERE/source" "$REPO"
git -C "$REPO" checkout -q "$COMMIT"
git -C "$REPO" remote set-url origin "$UPSTREAM"
IMAGE=nearprotocol/contract-builder:master-13430592a7be246dd5a29439791f4081e0107ff3-amd64
# Mirrors `cargo make build-docker` (Makefile.toml at tag 3.11.1) without needing cargo-make on the host.
docker run --rm --platform linux/amd64 \
  -v "$REPO:/host" -w /host -i \
  -e CARGO_MAKE_VERSION=0.37.24 \
  "$IMAGE" ./scripts/docker-entrypoint.sh
cp "$REPO/bin/aurora-engine.wasm" "$BUILD/contract.wasm"
echo "built $BUILD/contract.wasm sha256(base58)=$(python3 "$HERE/../../tools/near_rpc.py" hash "$BUILD/contract.wasm")"
