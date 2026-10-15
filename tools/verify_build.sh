#!/usr/bin/env bash
# usage: tools/verify_build.sh contracts/<name>
# Runs the entry's build.sh and compares the produced binary with hash.txt.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
DIR="$(cd "$1" && pwd)"
EXPECTED="$(tr -d '[:space:]' < "$DIR/hash.txt")"
if [ ! -e "$DIR/source/.git" ] && [ -z "$(ls -A "$DIR/source" 2>/dev/null)" ]; then
  git -C "$ROOT" submodule update --init "${DIR#$ROOT/}/source"
fi
record() {  # record <status> <hash-or-empty>
  python3 - "$ROOT/tools" "$DIR/contract.toml" "$1" "$2" <<'PY'
import sys, datetime
sys.path.insert(0, sys.argv[1]); import contract_toml
p, status, got = sys.argv[2], sys.argv[3], sys.argv[4]
m = contract_toml.load(p)
m["build"]["reproduced"] = status
m["build"]["reproduced_hash"] = got or None
m["build"]["reproduced_at"] = datetime.date.today().isoformat()
contract_toml.dump(m, p)
PY
}
if ! "$DIR/build.sh"; then
  echo "FAIL $DIR: build.sh exited with an error"
  record failed ""
  exit 1
fi
GOT="$(python3 "$ROOT/tools/near_rpc.py" hash "$DIR/build/contract.wasm")"
if [ "$GOT" = "$EXPECTED" ]; then
  echo "OK   $DIR: rebuilt binary matches $EXPECTED"
  record exact "$GOT"
else
  echo "FAIL $DIR: rebuilt $GOT != expected $EXPECTED"
  record mismatch "$GOT"
  exit 1
fi
