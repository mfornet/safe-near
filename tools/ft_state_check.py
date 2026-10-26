#!/usr/bin/env python3
"""Check a fungible token's invariant on a real storage (SAF-40).

Extracts one account's contract storage and runs `ft-state-check` (near-lean/sdk), which
decodes it as a near-contract-standards `FungibleToken` and decides the invariant wNEAR's
`Inv` states: balances and supply fit a u128, storage usage fits a u64, the balances sum to
the total supply.

    ft_state_check.py chunk <corpus-chunk-dir> <account>      # pre-state of a corpus chunk
    ft_state_check.py snapshot <near_snapshot.json> <account>  # a near_snapshot.py capture

A snapshot must hold the account's complete storage. Mainnet wrap.near cannot be captured
over public RPC today (TOO_LARGE_CONTRACT_STATE, see tools/SNAPSHOTS.md); any capture from a
node with a higher state-view limit can be checked as is.
"""

import argparse
import base64
import gzip
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
BINARY = ROOT / "near-lean/sdk/.lake/build/bin/ft-state-check"
CONTRACT_DATA = 9  # TrieKey::ContractData column


def chunk_storage(chunk: Path, account: str) -> list[list[str]]:
    """The account's ContractData records in a corpus chunk's pre-state."""
    entries = json.loads(gzip.decompress((chunk / "pre_state.json.gz").read_bytes()))["entries"]
    head = bytes([CONTRACT_DATA]) + account.encode() + b","
    return [[bytes.fromhex(key)[len(head):].hex(), value]
            for key, value in entries if bytes.fromhex(key).startswith(head)]


def snapshot_storage(path: Path, account: str) -> list[list[str]]:
    snapshot = json.loads(path.read_text())
    for entry in snapshot["accounts"]:
        if entry["account_id"] == account:
            storage = entry["storage"]
            if not storage["complete"]:
                raise ValueError(f"{account}: the snapshot holds only part of the storage")
            return [[base64.b64decode(v["key"]).hex(), base64.b64decode(v["value"]).hex()]
                    for v in storage["values"]]
    raise ValueError(f"{account} is not in the snapshot")


def check(storage: list[list[str]], binary: Path = BINARY) -> subprocess.CompletedProcess:
    with tempfile.NamedTemporaryFile("w", suffix=".json") as handle:
        json.dump(storage, handle)
        handle.flush()
        return subprocess.run([str(binary), handle.name], capture_output=True, text=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("source", choices=["chunk", "snapshot"])
    parser.add_argument("path", type=Path)
    parser.add_argument("account")
    args = parser.parse_args()
    if not BINARY.exists():
        print(f"build it first: cd near-lean/sdk && lake build ft-state-check", file=sys.stderr)
        return 2
    storage = (chunk_storage if args.source == "chunk" else snapshot_storage)(args.path, args.account)
    result = check(storage)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    return result.returncode


if __name__ == "__main__":
    sys.exit(main())
