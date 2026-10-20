#!/usr/bin/env python3
"""Native staking eligibility: compressed Edwards decoding and prime-order subgroup."""
import json
from pathlib import Path
import random
import tempfile
import unittest

import compare_fixture as comparator
from contract_probe import snapshot, block
import import_snapshot as importer
from near_rpc import b58encode
from prepare import HERE, ROOT, atomic_write
from probe import frozen_reference

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"
CLASSIFIER = ROOT / "near-lean/runtime/.lake/build/bin/staking-key-replay"
PRIME = 2**255 - 19
BASE = bytes([0x58]) + bytes([0x66]) * 31
IDENTITY = (1).to_bytes(32, "little")
MIXED = (PRIME - int.from_bytes(BASE, "little") + 2**255).to_bytes(32, "little")
CALLER = "fixture-caller.near"


def key(data):
    return "ed25519:" + b58encode(data)


def vectors():
    rng = random.Random(5419)
    values = [rng.randbytes(32) for _ in range(2048)]
    for y in [0, 1, PRIME - 1, PRIME, PRIME + 1, PRIME + 18, *range(2, 20)]:
        for sign in [0, 1]:
            values.append((y + sign * 2**255).to_bytes(32, "little"))
    return [key(value) for value in values + [BASE, MIXED]] + ["secp256k1:" + b58encode(bytes(64))]


class StakingKeyTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        atomic_write(ROOT / "audit/staking-key-regressions.json",
            (json.dumps(dict(cases=cls.evidence), indent=2) + "\n").encode())

    def test_pure_classifier_matches_native_decoding_and_subgroup_checks(self):
        with frozen_reference(REFERENCE) as (native, build):
            source = dict(publicKeys=vectors(), seeds=[f"public-staking-{i}" for i in range(256)])
            expected = importer.native_call(native, "--classify-staking-keys", source)
            actual = importer.execute(CLASSIFIER, dict(publicKeys=[row["borsh"] for row in expected["results"]]), ROOT)
            self.evidence.append(dict(scenario="pure-key-classification", referenceBuild=build,
                modelBinarySha256=importer.file_digest(CLASSIFIER), request=source, native=expected, model=actual))
            self.assertEqual(len(actual["results"]), len(expected["results"]))
            for native_row, model_row in zip(expected["results"], actual["results"]):
                with self.subTest(public_key=native_row["publicKey"]):
                    self.assertEqual(model_row["publicKey"], native_row["borsh"])
                    self.assertEqual(model_row["suitable"], native_row["suitable"])
            eligible = {row["publicKey"]: row["suitable"] for row in expected["results"]}
            self.assertTrue(eligible[key(BASE)])
            self.assertTrue(eligible[key(IDENTITY)])
            self.assertTrue(eligible[key((PRIME + 1).to_bytes(32, "little"))])
            self.assertTrue(eligible[key((1 + 2**255).to_bytes(32, "little"))])
            self.assertFalse(eligible[key(bytes(32))])
            self.assertFalse(eligible[key((PRIME - 1).to_bytes(32, "little"))])
            self.assertFalse(eligible[key(MIXED)])
            self.assertTrue(all(row["suitable"] for row in expected["results"][-256:]))

    def test_staking_admission_and_failure_order_through_native_apply(self):
        cases = ["zero", "order-two", "mixed-torsion", "secp256k1", "invalid-before-nonce",
            "invalid-before-balance", "invalid-before-zero-gas", "zero-gas-before-invalid", "count-before-invalid",
            "transfer-before-invalid", "valid-basepoint", "identity", "noncanonical-identity", "negative-zero-identity",
            "valid-before-nonce", "valid-insufficient-balance", "accepted-around-rejected"]
        with tempfile.TemporaryDirectory() as directory:
            for version in [83, 84, 85, 86]:
                for name in cases:
                    with self.subTest(protocol=version, scenario=name):
                        public_key = key(BASE)
                        if name.startswith("invalid") or name in {"zero", "transfer-before-invalid", "zero-gas-before-invalid", "count-before-invalid"}:
                            public_key = key(bytes(32))
                        elif name == "order-two":
                            public_key = key((PRIME - 1).to_bytes(32, "little"))
                        elif name == "mixed-torsion":
                            public_key = key(MIXED)
                        elif name == "secp256k1":
                            public_key = "secp256k1:" + b58encode(bytes(64))
                        elif name == "identity":
                            public_key = key(IDENTITY)
                        elif name == "noncanonical-identity":
                            public_key = key((PRIME + 1).to_bytes(32, "little"))
                        elif name == "negative-zero-identity":
                            public_key = key((1 + 2**255).to_bytes(32, "little"))
                        amount = str(101 * 10**24) if name == "valid-insufficient-balance" else "0"
                        stake = {"Stake": dict(stake=amount, public_key=public_key)}
                        tx = dict(receiverId=CALLER, nonce=0 if name.endswith("nonce") else 1, actions=[stake])
                        caller = dict(accountId=CALLER, seed="public-staking-admission", amount="0" if name.endswith("before-balance") else str(100 * 10**24))
                        zero_call = {"FunctionCall": dict(method_name="read", args="", gas=0, deposit="0")}
                        if name == "invalid-before-zero-gas": tx["actions"].append(zero_call)
                        if name == "zero-gas-before-invalid": tx["actions"].insert(0, zero_call)
                        if name == "transfer-before-invalid": tx["actions"].insert(0, {"Transfer": {"deposit": "1"}})
                        if name == "count-before-invalid": tx["actions"] = [stake] * 101
                        txs = [tx]
                        if name == "accepted-around-rejected":
                            stake["Stake"]["public_key"] = key(bytes(32))
                            tx["nonce"] = 2
                            transfer = dict(receiverId="captured.near", nonce=1, actions=[{"Transfer": {"deposit": "1"}}])
                            txs = [transfer, tx, dict(transfer, nonce=2)]
                        scenario = dict(caller=caller, blocks=[block(101, txs)] + [block(i) for i in range(102, 106)])
                        target = Path(directory) / f"{version}-{name}"
                        importer.prepare(snapshot(version), target, reference=REFERENCE, model=MODEL, scenario=scenario)
                        report = comparator.compare(target, REFERENCE, MODEL)
                        self.evidence.append(dict(protocol=version, scenario=name, comparison=report))
                        self.assertIsNone(report["projectionError"])
                        self.assertEqual(report["differences"], [])
                        self.assertTrue(report["model"]["quiescent"])
                        outcomes = [row["outcome"]["status"] for row in report["model"]["blocks"][0]["outcomes"]]
                        failures = [status for status in outcomes if status["kind"] == "failure"]
                        self.assertEqual(len(failures), 1)
                        error = failures[0]["details"]
                        if name == "count-before-invalid": expected = "TotalNumberOfActionsExceeded"
                        elif name == "zero-gas-before-invalid": expected = "FunctionCallZeroAttachedGas"
                        elif name == "valid-before-nonce": expected = "invalidNonce"
                        elif name == "valid-insufficient-balance": expected = "triesToStake"
                        elif name in {"valid-basepoint", "identity", "noncanonical-identity", "negative-zero-identity"}: expected = "triesToUnstake"
                        else: expected = "UnsuitableStakingKey"
                        self.assertEqual(error["error"]["kind"] if error["kind"] == "actionsValidation" else error["kind"], expected)
                        if expected == "UnsuitableStakingKey":
                            self.assertEqual(error["error"]["public_key"], comparator.PublicKeys()[public_key] if name != "accepted-around-rejected" else [0] * 33)
                        if name == "accepted-around-rejected":
                            self.assertEqual([status["kind"] == "failure" for status in outcomes], [False, True, False])
                        elif expected not in {"triesToStake", "triesToUnstake"}:
                            self.assertEqual(report["model"]["blocks"][0]["state"], report["model"]["initialState"])
                            self.assertEqual(report["model"]["blocks"][0]["tokensBurnt"], "0")
                print(f"protocol {version}: staking admission complete", flush=True)


if __name__ == "__main__":
    unittest.main()
