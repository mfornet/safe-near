#!/usr/bin/env python3
"""Native differential tests for chunk cache, overlays and receipt rollback."""
import copy
import base64
import json
from pathlib import Path
import tempfile
import unittest

import compare_fixture as comparator
import contract_probe as corpus
import import_snapshot as importer
from prepare import HERE, ROOT, atomic_write

REFERENCE = HERE / "target/near-apply-reference"
MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"


class ChunkStorageTests(unittest.TestCase):
    evidence = []

    @classmethod
    def tearDownClass(cls):
        atomic_write(ROOT / "audit/chunk-storage-regressions.json",
                     (json.dumps(dict(cases=cls.evidence), indent=2) + "\n").encode())

    def compare(self, version, batches, *, storage=None, contexts=None, call_gas=None):
        scenario = corpus.scenario("write")
        template = scenario["blocks"][0]["transactions"][0]
        nonce = 0
        blocks = []
        for index, methods in enumerate(batches):
            transactions = []
            for actions in methods:
                nonce += 1
                tx = copy.deepcopy(template)
                tx["nonce"] = nonce
                tx["actions"] = []
                for method in actions:
                    action = copy.deepcopy(template["actions"][0])
                    if method == "deleteKey":
                        action = {"DeleteKey": {"public_key": "ed25519:" + "1" * 32}}
                    else:
                        action["FunctionCall"]["method_name"] = method
                        if call_gas is not None:
                            action["FunctionCall"]["gas"] = call_gas
                    tx["actions"].append(action)
                transactions.append(tx)
            blocks.append(corpus.block(101 + index, transactions))
        blocks += [corpus.block(101 + len(blocks) + i) for i in range(4)]
        for index, context in (contexts or {}).items():
            blocks[index].update(context)
        scenario["blocks"] = blocks
        snapshot = corpus.snapshot(version)
        if storage is not None:
            account = snapshot["accounts"][0]
            account["storage"]["values"] = storage
            account["account"]["storage_usage"] += sum(
                len(base64.b64decode(row["key"])) + len(base64.b64decode(row["value"]))
                for row in storage) - 6
        with tempfile.TemporaryDirectory() as temporary:
            directory = Path(temporary) / "fixture"
            importer.prepare(snapshot, directory, reference=REFERENCE, model=MODEL, scenario=scenario)
            report = comparator.compare(directory, REFERENCE, MODEL)
        self.evidence.append(dict(protocol=version, batches=batches, comparison=report))
        self.assertIsNone(report["projectionError"])
        self.assertEqual(report["differences"], [])
        if call_gas is None and not any(method == "read" for batch in batches for actions in batch for method in actions):
            costs = json.loads((ROOT / f"near-lean/vm/configs/runtime_config_v{version}.json").read_text())["wasm_config"]["ext_costs"]
            # The native tariffs are equal in these versions. Compare the fresh/cached
            # categories too, so accidentally resetting the cache cannot pass on totals.
            for native, model in zip(report["native"]["blocks"], report["registered"]["blocks"]):
                profile = {}
                for row in native["outcomes"]:
                    for charge in row["outcome"]["metadata"].get("gas_profile") or []:
                        profile[charge["cost"]] = profile.get(charge["cost"], 0) + int(charge["gas_used"])
                accounting = model["trieAccounting"]
                self.assertEqual(profile.get("TOUCHING_TRIE_NODE", 0), accounting["disk"] * costs["touching_trie_node"])
                self.assertEqual(profile.get("READ_CACHED_TRIE_NODE", 0), accounting["cached"] * costs["read_cached_trie_node"])
        return report

    def test_cache_and_overlay_lifetimes(self):
        scenarios = [
            # Later actions in one receipt read prospective updates.
            [[["write", "write", "remove", "write"]]],
            # Later receipts read committed updates in the same chunk.
            [[["write"], ["remove"], ["write"]]],
            # Flat-storage reads still warm value hashes before a mutation.
            [[["read"], ["panic_after_write"], ["write"]]],
            # Both failures warm the same base nodes and value without committing.
            [[["panic_after_write"], ["panic_after_write"], ["write"]]],
            # Earlier successful action is also rolled back on a later panic.
            [[["write", "fail"], ["remove"]]],
            # A non-VM failure after a successful write rolls back that write.
            [[["write", "deleteKey", "deleteKey"], ["remove"]]],
            # Repeated failures in different chunks start from fresh caches.
            [[["panic_after_write"]], [], [["panic_after_write"]]],
        ]
        for version in [83, 84, 85, 86]:
            for batches in scenarios:
                with self.subTest(protocol=version, batches=batches):
                    self.compare(version, batches)

    def test_exhaustion_warms_cache_without_committing_writes(self):
        for version in [83, 84, 85, 86]:
            for batches in [[[["write"], ["write"]]], [[["write"]], [], [["write"]]]]:
                with self.subTest(protocol=version, batches=batches):
                    report = self.compare(version, batches, call_gas=80_000_000_000)
                    outcomes = report["model"]["blocks"]
                    self.assertEqual(outcomes[1]["outcomes"][0]["outcome"]["status"]["kind"], "failure")
                    cached = report["registered"]["blocks"][1]["trieAccounting"]
                    self.assertGreater(cached["disk"], 0)
                    if len(batches) == 1:
                        self.assertEqual(outcomes[1]["outcomes"][1]["outcome"]["status"]["kind"], "failure")
                        self.assertGreater(cached["cached"], 0)
                        profiles = report["native"]["blocks"][1]["outcomes"]
                        second = {row["cost"]: int(row["gas_used"]) for row in profiles[1]["outcome"]["metadata"]["gas_profile"]}
                        self.assertGreater(second.get("READ_CACHED_TRIE_NODE", 0), 0)
                        self.assertEqual(second.get("TOUCHING_TRIE_NODE", 0), 0)
                    else:
                        self.assertEqual(outcomes[3]["outcomes"][0]["outcome"]["status"]["kind"], "failure")
                        self.assertEqual(cached["cached"], 0)
                        later = report["registered"]["blocks"][3]["trieAccounting"]
                        self.assertGreater(later["disk"], 0)
                        self.assertEqual(later["cached"], 0)

    def test_complete_state_shapes_and_large_values(self):
        states = [[],
            [dict(key="aw==", value=base64.b64encode(b"x" * 5001).decode())],
            [dict(key=base64.b64encode(key).decode(), value=base64.b64encode(value).decode())
             for key, value in [(b"k", b"hello"), (b"ka", b"shared"), (b"kb", b"shared"),
                                (b"\x00", b"other"), (b"\xff", b"tail")]]]
        for version in [83, 84, 85, 86]:
            for storage in states:
                with self.subTest(protocol=version, storageKeys=[row["key"] for row in storage]):
                    self.compare(version, [[["panic_after_write"], ["remove"], ["write"]]], storage=storage)

    def test_delete_and_recreate_account_in_same_chunk(self):
        blob = (HERE / "fixtures/storage_lifecycle.wasm").read_bytes()
        encoded = base64.b64encode(blob).decode()
        for version in [83, 84, 85, 86]:
            with self.subTest(protocol=version):
                snapshot = corpus.snapshot(version)
                scenario = corpus.scenario("write")
                # Local transactions already execute in order within one chunk.
                # The registrar can recreate its own top-level account after deletion.
                scenario["caller"]["accountId"] = "registrar"
                scenario["codeBlobs"] = [encoded]
                deploy = dict(receiverId="registrar", nonce=1, actions=[
                    {"DeployContract": {"code": encoded}},
                    {"FunctionCall": dict(method_name="write", args="", gas=150 * 10**12, deposit="0")}])
                deletion = dict(receiverId="registrar", nonce=2, actions=[
                    {"DeleteAccount": {"beneficiary_id": "callee.near"}}])
                recreation = dict(receiverId="registrar", nonce=3, actions=[
                    {"CreateAccount": {}}, *copy.deepcopy(deploy["actions"])])
                scenario["blocks"][0]["transactions"] = [deploy]
                scenario["blocks"][1]["transactions"] = [deletion, recreation]
                with tempfile.TemporaryDirectory() as temporary:
                    directory = Path(temporary) / "fixture"
                    importer.prepare(snapshot, directory, reference=REFERENCE, model=MODEL, scenario=scenario)
                    report = comparator.compare(directory, REFERENCE, MODEL)
                self.evidence.append(dict(protocol=version, accountLifecycle=True, comparison=report))
                self.assertIsNone(report["projectionError"])
                self.assertEqual(report["differences"], [])
                final = dict(report["model"]["blocks"][-1]["state"]["storage"])
                self.assertEqual(final["registrar"], [[list(b"k"), list(b"new")]])

    def test_scheduler_record_uses_original_context(self):
        # Borsh BTreeMap{0: V1([request(to_shard=0, highest bitmap bit)])}.
        request = list((1).to_bytes(4, "little") + bytes(8) + bytes(1) +
                       (1).to_bytes(4, "little") + bytes(2) + bytes(4) + bytes([128]))
        for version in [83, 84, 85, 86]:
            self.compare(version, [[["panic_after_write"]], [], [["write"]]],
                         contexts={0: dict(bandwidthRequests=request)})


if __name__ == "__main__":
    unittest.main()
