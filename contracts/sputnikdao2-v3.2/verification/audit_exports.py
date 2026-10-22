#!/usr/bin/env python3
"""Check the exact exported surface of the factory-stored Sputnik DAO Wasm."""

from __future__ import annotations

import hashlib
from pathlib import Path
import re


WASM = Path(__file__).resolve().parent.parent / "contract.wasm"
LEAN_INVENTORY = Path(__file__).resolve().parent / "Model" / "ExportWrapper.lean"
LEAN_VIEWS = Path(__file__).resolve().parent / "Model" / "ViewExport.lean"
SHA256 = "bf6f951ee5e45968e3367fa857bebf8bc80badec183998c2239c487237e0d7f6"

METHODS = {
    "new", "migrate", "remove_blob", "get_factory_info", "store_blob", "update",
    "add_proposal", "act_proposal", "on_proposal_callback",
    "bounty_claim", "bounty_done", "bounty_giveup",
    "register_delegation", "delegate", "undelegate",
    "version", "get_config", "get_policy", "get_staking_contract", "has_blob",
    "get_locked_storage_amount", "get_available_amount",
    "delegation_total_supply", "delegation_balance_of", "delegation_balance_ratio",
    "get_last_proposal_id", "get_proposals", "get_proposal", "get_bounty",
    "get_last_bounty_id", "get_bounties", "get_bounty_claims",
    "get_bounty_number_of_claims", "get_actions_log",
}
GENERATED_FUNCTIONS = {"__contract_abi", "contract_source_metadata"}
EXPECTED = {
    **{name: 0 for name in METHODS | GENERATED_FUNCTIONS},
    "memory": 2,
    "__data_end": 3,
    "__heap_base": 3,
}


def u32(data: bytes, offset: int) -> tuple[int, int]:
    value = 0
    for shift in range(0, 35, 7):
        if offset >= len(data):
            raise ValueError("truncated unsigned LEB128")
        byte = data[offset]
        offset += 1
        value |= (byte & 0x7f) << shift
        if byte < 0x80:
            if value >= 2**32:
                raise ValueError("unsigned LEB128 exceeds u32")
            return value, offset
    raise ValueError("unsigned LEB128 is too long")


def exports(data: bytes) -> dict[str, int]:
    if data[:8] != b"\0asm\x01\0\0\0":
        raise ValueError("not a WebAssembly v1 module")
    offset = 8
    found: dict[str, int] | None = None
    while offset < len(data):
        section_id = data[offset]
        offset += 1
        size, offset = u32(data, offset)
        end = offset + size
        if end > len(data):
            raise ValueError("section extends beyond the module")
        if section_id == 7:
            if found is not None:
                raise ValueError("multiple export sections")
            count, cursor = u32(data, offset)
            found = {}
            for _ in range(count):
                length, cursor = u32(data, cursor)
                name_end = cursor + length
                if name_end > end:
                    raise ValueError("truncated export name")
                name = data[cursor:name_end].decode("utf-8")
                cursor = name_end
                if cursor >= end:
                    raise ValueError("truncated export descriptor")
                kind = data[cursor]
                cursor += 1
                _, cursor = u32(data, cursor)
                if name in found:
                    raise ValueError(f"duplicate export: {name}")
                found[name] = kind
            if cursor != end:
                raise ValueError("trailing bytes in export section")
        offset = end
    if found is None:
        raise ValueError("missing export section")
    return found


def main() -> None:
    inventory = LEAN_INVENTORY.read_text()
    lean_names = re.findall(r'^\s*entry "([^"]+)"', inventory, flags=re.MULTILINE)
    if len(lean_names) != len(METHODS) or set(lean_names) != METHODS:
        raise SystemExit(
            "Lean export inventory mismatch: "
            f"missing={sorted(METHODS - set(lean_names))}, "
            f"extra={sorted(set(lean_names) - METHODS)}, "
            f"duplicates={len(lean_names) - len(set(lean_names))}"
        )
    view_names = re.findall(r'^\s*entry "([^"]+)" \.view', inventory, flags=re.MULTILINE)
    compositions = re.findall(
        r'runGeneratedViewWrapper\s+raw\s+"([^"]+)"', LEAN_VIEWS.read_text()
    )
    if len(compositions) != len(view_names) or set(compositions) != set(view_names):
        raise SystemExit(
            "Lean view composition mismatch: "
            f"missing={sorted(set(view_names) - set(compositions))}, "
            f"extra={sorted(set(compositions) - set(view_names))}, "
            f"duplicates={len(compositions) - len(set(compositions))}"
        )
    data = WASM.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    if digest != SHA256:
        raise SystemExit(f"unexpected canonical Wasm SHA-256: {digest}")
    actual = exports(data)
    if actual != EXPECTED:
        missing = EXPECTED.keys() - actual.keys()
        extra = actual.keys() - EXPECTED.keys()
        wrong_kind = {
            name: (EXPECTED[name], actual[name])
            for name in EXPECTED.keys() & actual.keys()
            if EXPECTED[name] != actual[name]
        }
        raise SystemExit(
            f"export mismatch: missing={sorted(missing)}, extra={sorted(extra)}, "
            f"wrong_kind={wrong_kind}"
        )
    print(f"{WASM}: {len(METHODS)} contract methods, "
          f"{len(GENERATED_FUNCTIONS)} generated functions, {len(actual)} total exports")
    print(f"{LEAN_VIEWS}: {len(view_names)} named view compositions")


if __name__ == "__main__":
    main()
