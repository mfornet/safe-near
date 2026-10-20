#!/usr/bin/env python3
"""Independent native Borsh widths, protocol size gates and atomic rejection."""
import base64
import hashlib
import json
from pathlib import Path
import tempfile
import unittest

import compare_fixture as comparator
import import_snapshot as importer
from contract_probe import snapshot, block
from prepare import HERE, ROOT, atomic_write
from probe import frozen_reference

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"
CALLER = "fixture-caller.near"
SEED = "public-transaction-size"


def call(arguments=b""):
    return {"FunctionCall": dict(method_name="read", args=base64.b64encode(arguments).decode(), gas=10**12, deposit="0")}


def sign(native, key_type, transactions):
    rows = [dict(row, blockHash=[0] * 32) for row in transactions]
    return importer.native_call(native, "--sign-transactions", dict(signerId=CALLER, seed=SEED,
        keyType=key_type, transactions=rows))


def prepare(version, key_type, transactions, target, caller_patch=None, codes=()):
    caller = dict(accountId=CALLER, seed=SEED, keyType=key_type, amount=str(100 * 10**24))
    caller.update(caller_patch or {})
    scenario = dict(caller=caller, blocks=[block(101, transactions)] + [block(i) for i in range(102, 106)])
    if codes:
        scenario["codeBlobs"] = list(codes)
    importer.prepare(snapshot(version), target, reference=REFERENCE, model=MODEL, scenario=scenario)
    return comparator.compare(target, REFERENCE, MODEL)


class TransactionSizeTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        atomic_write(ROOT / "audit/transaction-size-regressions.json",
            (json.dumps(dict(cases=cls.evidence), indent=2) + "\n").encode())

    def record(self, label, report):
        # Full large payloads remain in per-case artifacts; the index binds each file.
        path = ROOT / f"audit/transaction-size-cases/{label}.json"
        payload = (json.dumps(report, separators=(",", ":")) + "\n").encode()
        atomic_write(path, payload)
        self.evidence.append(dict(scenario=label, file=str(path.relative_to(ROOT)),
            sha256=hashlib.sha256(payload).hexdigest(), differences=len(report["differences"]),
            projectionError=report["projectionError"]))
        self.assertIsNone(report["projectionError"])
        self.assertEqual(report["differences"], [])
        for native, model in zip(report["native"]["blocks"], report["model"]["blocks"]):
            self.assertEqual(model["transactionSizes"], [
                {key: row[key] for key in ["bodySize", "wireSize", "sizeForLimits"]}
                for row in native["inputs"]["transactions"]])
            for row in native["inputs"]["transactions"]:
                self.assertEqual(row["wireSize"], len(row["borsh"]))

    def test_all_action_widths_envelopes_and_key_schemes(self):
        with frozen_reference(REFERENCE) as (native, _), tempfile.TemporaryDirectory() as directory:
            staking_key = sign(native, "ed25519", [])["publicKey"]
            key = "ed25519:" + "1" * 32
            actions = [{"CreateAccount": {}}, {"DeployContract": {"code": "AGFzbQEAAAA="}},
                {"FunctionCall": dict(method_name="é", args="AP8=", gas=1, deposit="2")},
                {"Transfer": {"deposit": "3"}}, {"Stake": {"stake": "4", "public_key": staking_key}},
                {"AddKey": dict(public_key=key, access_key=dict(nonce=9, permission="FullAccess"))},
                *[{"AddKey": dict(public_key=key, access_key=dict(nonce=11, permission={"FunctionCall": dict(
                    allowance=allowance, receiver_id="captured.near", method_names=["é", "", "alpha"])}))}
                    for allowance in [None, "123"]],
                {"DeleteKey": {"public_key": key}}, {"DeleteAccount": {"beneficiary_id": "callee.near"}}]
            for version in [83, 84, 85, 86]:
                for key_type in ["ed25519", "secp256k1"]:
                    for tag in [0, 1]:
                        label = f"widths-{version}-{key_type}-v{tag}"
                        with self.subTest(label=label):
                            transactions = [dict(version=tag, receiverId="captured.near", nonce=0, actions=[action]) for action in actions]
                            report = prepare(version, key_type, transactions, Path(directory) / label)
                            self.record(label, report)
                            for size in report["model"]["blocks"][0]["transactionSizes"]:
                                self.assertEqual(size["wireSize"] - size["bodySize"], 65 if key_type == "ed25519" else 66)
                                self.assertEqual(size["sizeForLimits"], size["wireSize"] if version >= 85 else size["bodySize"])

    def boundary(self, native, directory, version, key_type, tag, mode, caller_patch=None):
        config = json.loads((ROOT / f"near-lean/vm/configs/runtime_config_v{version}.json").read_text())
        limit = config["wasm_config"]["limit_config"]["max_transaction_size"]
        tx = dict(version=tag, receiverId="captured.near", nonce=1, actions=[call()])
        baseline = sign(native, key_type, [tx])["transactions"][0]
        includes_signature = config["runtime_admission"]["transaction_size_includes_signature"]
        base = baseline["wireSize"] if includes_signature and mode != "legacy-body" else baseline["bodySize"]
        extra = 1 if mode in {"over", "nonce", "missing-key", "balance", "unsupported-version"} else 0
        tx["actions"] = [call(bytes(limit - base + extra))]
        if mode == "nonce":
            tx["nonce"] = 0
        label = f"boundary-{version}-{key_type}-v{tag}-{mode}"
        report = prepare(version, key_type, [tx], Path(directory) / label, caller_patch)
        self.record(label, report)
        statuses = [row["outcome"]["status"] for row in report["model"]["blocks"][0]["outcomes"]]
        expected = "invalidTransactionVersion" if mode == "unsupported-version" else (
            "transactionSizeExceeded" if extra or mode == "legacy-body" and includes_signature else None)
        failures = [status for status in statuses if status["kind"] == "failure"]
        self.assertEqual(len(failures), 0 if expected is None else 1)
        if expected:
            self.assertEqual(failures[0]["details"]["kind"], expected)
            self.assertEqual(report["model"]["blocks"][0]["state"], report["model"]["initialState"])
            self.assertEqual(report["model"]["blocks"][0]["tokensBurnt"], "0")
            self.assertEqual(report["model"]["blocks"][0]["outgoingReceipts"], [])
        self.assertTrue(report["model"]["quiescent"])
        if mode == "at":
            self.assertEqual(report["model"]["blocks"][0]["transactionSizes"][0]["sizeForLimits"], limit)

    def test_native_limit_boundaries_and_signature_upgrade(self):
        with frozen_reference(REFERENCE) as (native, _), tempfile.TemporaryDirectory() as directory:
            for version in [83, 84, 85, 86]:
                for key_type in ["ed25519", "secp256k1"]:
                    for tag in ([0, 1] if version >= 85 else [0]):
                        for mode in ["at", "over"]:
                            with self.subTest(protocol=version, key=key_type, tag=tag, mode=mode):
                                self.boundary(native, directory, version, key_type, tag, mode)
                    if version in [84, 85]:
                        with self.subTest(protocol=version, key=key_type, mode="legacy-body"):
                            self.boundary(native, directory, version, key_type, 0, "legacy-body")
                print(f"protocol {version}: size boundaries complete", flush=True)

    def test_size_rejection_precedes_stateful_admission_but_follows_version_gate(self):
        with frozen_reference(REFERENCE) as (native, _), tempfile.TemporaryDirectory() as directory:
            for mode, patch in [("nonce", None), ("missing-key", dict(accessKey=None)), ("balance", dict(amount="0"))]:
                with self.subTest(mode=mode):
                    self.boundary(native, directory, 86, "ed25519", 0, mode, patch)
            self.boundary(native, directory, 84, "ed25519", 1, "unsupported-version")


if __name__ == "__main__":
    unittest.main()
