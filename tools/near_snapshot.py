#!/usr/bin/env python3
"""Download selected NEAR accounts at one block into a reproducible JSON fixture.

Only reads public RPC data. No signing keys or transactions are needed.
See tools/SNAPSHOTS.md for the fixture boundary and examples.
"""

import argparse
import base64
import json
import os
from pathlib import Path
import re
import sys
import tempfile

from near_rpc import ARCHIVAL_RPC, code_hash, rpc


EMPTY_CODE_HASH = "1" * 32


def decode(value: str) -> bytes:
    return base64.b64decode(value, validate=True)


def capture(accounts: list[str], *, url: str = ARCHIVAL_RPC,
            block=None, prefixes: list[bytes] | None = None, request=rpc) -> dict:
    """Capture all reads at the resolved hash; fail rather than mix block states."""
    if not accounts or len(set(accounts)) != len(accounts):
        raise ValueError("provide a nonempty list of distinct account IDs")
    for account in accounts:
        if not re.fullmatch(r"[a-z0-9]+(?:[._-][a-z0-9]+)*", account) or not 2 <= len(account) <= 64:
            raise ValueError(f"invalid account ID: {account!r}")
    prefixes = sorted(set(prefixes if prefixes is not None else [b""]))
    if not prefixes:
        raise ValueError("provide at least one storage prefix")
    # A full-state request subsumes any narrower prefixes.
    if b"" in prefixes:
        prefixes = [b""]
    reference = {"block_id": block} if block is not None else {"finality": "final"}
    block_data = request("block", reference, url=url)
    header = block_data["header"]
    height, block_hash = header["height"], header["hash"]

    def query(kind, account, **params):
        result = request("query", {"request_type": kind, "account_id": account,
                                   "block_id": block_hash, **params}, url=url)
        if result.get("block_hash") != block_hash or result.get("block_height") != height:
            raise ValueError(f"{account}/{kind}: RPC returned a different block")
        return {k: v for k, v in result.items() if k not in {"block_hash", "block_height"}}

    protocol = request("EXPERIMENTAL_protocol_config", {"block_id": block_hash}, url=url)
    snapshots = []
    for account_id in sorted(accounts):
        account = query("view_account", account_id)
        # Global code resolution needs separate handling; never substitute empty code.
        if account.get("global_contract_hash") or account.get("global_contract_account_id"):
            raise ValueError(f"{account_id}: global contract references are not supported yet")
        code = None
        if account["code_hash"] != EMPTY_CODE_HASH:
            code = query("view_code", account_id)
            actual = code_hash(decode(code["code_base64"]))
            if actual != code["hash"] or actual != account["code_hash"]:
                raise ValueError(f"{account_id}: downloaded code hash does not match account")
        keys = query("view_access_key_list", account_id)["keys"]
        if len({k["public_key"] for k in keys}) != len(keys):
            raise ValueError(f"{account_id}: duplicate access key in RPC response")
        values = {}
        for prefix in prefixes:
            state = query("view_state", account_id,
                          prefix_base64=base64.b64encode(prefix).decode(), include_proof=False)
            for item in state["values"]:
                key, value = decode(item["key"]), decode(item["value"])
                if not key.startswith(prefix):
                    raise ValueError(f"{account_id}: storage key outside requested prefix")
                if key in values and values[key] != value:
                    raise ValueError(f"{account_id}: inconsistent overlapping storage values")
                values[key] = value
        snapshots.append({
            "account_id": account_id, "account": account, "code": code,
            "access_keys": sorted(keys, key=lambda k: k["public_key"]),
            "storage": {
                "complete": prefixes == [b""],
                "prefixes_base64": [base64.b64encode(p).decode() for p in prefixes],
                "values": [{"key": base64.b64encode(k).decode(),
                            "value": base64.b64encode(v).decode()}
                           for k, v in sorted(values.items())],
            },
        })
    return {
        "format": "safe-near-snapshot-v1", "rpc_url": url,
        "block": block_data, "protocol_config": protocol, "accounts": snapshots,
        "scope": {"all_accounts": False, "receipt_queues": False,
                  "state_proofs_verified": False},
    }


def write_snapshot(path: Path, snapshot: dict) -> None:
    """Publish only a complete JSON file and never overwrite an existing fixture."""
    path.parent.mkdir(parents=True, exist_ok=True)
    filename = None
    try:
        with tempfile.NamedTemporaryFile(mode="w", encoding="utf-8", dir=path.parent,
                                         prefix=f".{path.name}.", delete=False) as output:
            filename = output.name
            json.dump(snapshot, output, indent=2, sort_keys=True)
            output.write("\n")
            output.flush()
            os.fsync(output.fileno())
        # Hard-link publication is atomic and fails if the destination exists.
        os.link(filename, path)
    finally:
        if filename is not None:
            os.unlink(filename)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    parser.add_argument("accounts", nargs="+")
    parser.add_argument("--rpc", default=ARCHIVAL_RPC)
    parser.add_argument("--block", help="block height or hash (default: finalized head)")
    parser.add_argument("--prefix-base64", action="append",
                        help="storage prefix; repeat for multiple prefixes (default: all storage)")
    args = parser.parse_args()
    block = int(args.block) if args.block and args.block.isdecimal() else args.block
    try:
        if args.output.exists():
            raise FileExistsError(f"refusing to overwrite {args.output}")
        prefixes = [decode(p) for p in args.prefix_base64] if args.prefix_base64 else None
        snapshot = capture(args.accounts, url=args.rpc, block=block, prefixes=prefixes)
        write_snapshot(args.output, snapshot)
    except (ValueError, OSError, RuntimeError, LookupError) as error:
        print(f"snapshot failed: {error}", file=sys.stderr)
        return 1
    print(f"Saved {len(snapshot['accounts'])} accounts at block "
          f"{snapshot['block']['header']['hash']} to {args.output}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
