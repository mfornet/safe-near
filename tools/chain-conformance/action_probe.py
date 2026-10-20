#!/usr/bin/env python3
"""Compare administrative actions and failed multi-action receipt rollback."""
from __future__ import annotations

import argparse
import copy
import json
from pathlib import Path
import tempfile

from compare_fixture import compare
from contract_probe import snapshot, block
import import_snapshot as importer
from prepare import HERE, ROOT, atomic_write

CALLER = "fixture-caller.near"
ZERO_KEY = "ed25519:" + "1" * 32
ADD_KEY = {"AddKey": {"public_key": ZERO_KEY, "access_key": {"nonce": 0, "permission": "FullAccess"}}}
DELETE_KEY = {"DeleteKey": {"public_key": ZERO_KEY}}
CREATE = {"CreateAccount": {}}
TRANSFER = {"Transfer": {"deposit": "1"}}
def call(method):
    return {"FunctionCall": {"method_name": method, "args": "", "gas": 50 * 10**12, "deposit": "0"}}

CASES = {
    "reserved-system": ("system", [CREATE], 0),
    "reserved-system-registrar": ("system", [CREATE, TRANSFER, ADD_KEY], 0),
    "system-lookalike-registrar": ("systemx", [CREATE, {"Transfer": {"deposit": str(10**24)}}, ADD_KEY], "success"),
    "reserved-system-authority": ("system", [CREATE, TRANSFER, ADD_KEY], 0),
    "system-subaccount": ("system." + CALLER, [CREATE, {"Transfer": {"deposit": str(10**24)}}, ADD_KEY], "success"),
    "existing-create": ("captured.near", [CREATE], 0),
    "missing-transfer": ("missing.near", [TRANSFER], 0),
    "foreign-key": ("captured.near", [DELETE_KEY], 0),
    "transfer-before-foreign-key": ("captured.near", [TRANSFER, DELETE_KEY], 1),
    "transfer-before-existing-create": ("captured.near", [TRANSFER, CREATE], 1),
    "wrong-parent": ("new.captured.near", [CREATE], 0),
    "registrar-required": ("xy", [CREATE], 0),
    "self-missing-key": (CALLER, [DELETE_KEY], 0),
    "duplicate-new-key": ("new." + CALLER, [CREATE, ADD_KEY, ADD_KEY], 2),
    "late-missing-key": ("new." + CALLER, [CREATE, TRANSFER, DELETE_KEY], 2),
    "missing-method": ("captured.near", [call("no_such_method")], 0),
    "missing-code": (CALLER, [call("ping")], 0),
    "final-storage-deficit": ("underfunded.near", [TRANSFER], None),
    "add-key": (CALLER, [ADD_KEY], "success"),
    "add-key-late": ("new." + CALLER, [CREATE, {"Transfer": {"deposit": str(10**24)}},
        {"AddKey": {"public_key": ZERO_KEY, "access_key": {"nonce": 987, "permission": "FullAccess"}}}], "success"),
    "add-delete-key": (CALLER, [ADD_KEY, DELETE_KEY], "success"),
}


def prepare_case(version, name):
    capture = snapshot(version)
    receiver, actions, expected_index = CASES[name]
    if name == "final-storage-deficit":
        account = copy.deepcopy(capture["accounts"][0])
        account.update(account_id=receiver, code=None, access_keys=[])
        account["account"].update(amount="0", locked="0", code_hash=importer.EMPTY_CODE_HASH, storage_usage=10**9)
        account["storage"]["values"] = []
        capture["accounts"].append(account)
    transaction = dict(receiverId=receiver, nonce=1, actions=copy.deepcopy(actions))
    scenario = dict(caller=dict(accountId=CALLER, seed="safe-near-action-corpus", amount=str(100 * 10**24)),
        blocks=[block(101, [transaction])] + [block(i) for i in range(102, 106)])
    if name in {"reserved-system-registrar", "system-lookalike-registrar"}:
        scenario["caller"]["accountId"] = "registrar"
    if name == "add-key-late":
        scenario["blocks"] = [block(101, [transaction]), block(110), block(111), block(112)]
    return capture, scenario, expected_index


def run_case(version, name, target, reference, model, registered_model=None):
    capture, scenario, _ = prepare_case(version, name)
    importer.prepare(capture, target, reference=reference, model=model, registered_model=registered_model, scenario=scenario)
    return compare(target, reference, model, registered_model=registered_model)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--protocol", type=int, action="append", choices=[83, 84, 85, 86])
    parser.add_argument("--case", action="append", choices=list(CASES))
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/action-chain-comparison.json")
    args = parser.parse_args()
    cases = []
    with tempfile.TemporaryDirectory(prefix="safe-near-actions-") as temporary:
        for version in args.protocol or [83, 84, 85, 86]:
            for name in args.case or CASES:
                report = run_case(version, name, Path(temporary) / str(len(cases)), args.reference.resolve(), args.model.resolve())
                cases.append(dict(protocolVersion=version, scenario=name, comparison=report))
                print(f"v{version} {name}: {len(report['differences'])} differences; projection={report['projectionError']}", flush=True)
    failed = sum(bool(case["comparison"]["differences"]) for case in cases)
    atomic_write(args.report.resolve(), (json.dumps(dict(cases=cases, differingCases=failed), indent=2) + "\n").encode())
    print(f"{len(cases)} action cases, {failed} differed; evidence: {args.report.resolve()}")
    raise SystemExit(bool(failed))


if __name__ == "__main__":
    main()
