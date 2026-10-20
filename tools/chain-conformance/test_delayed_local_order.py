#!/usr/bin/env python3
"""Local execution priority must not reorder an existing persistent backlog."""
import json
from pathlib import Path
import tempfile
import unittest

import compare_fixture as comparator
import contract_probe
import import_snapshot as importer
from prepare import ROOT, atomic_write
from probe import frozen_reference
from trie_probe import REFERENCE

MODEL = ROOT / "near-lean/chain/.lake/build/bin/chain-replay"
CALLER = "fixture-caller.near"


def transaction(nonce, deposit, receiver=CALLER):
    return dict(receiverId=receiver, nonce=nonce, actions=[dict(Transfer=dict(deposit=str(deposit)))])


class DelayedLocalOrderTests(unittest.TestCase):
    def test_existing_backlog_precedes_new_local_and_incoming_deferrals(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for key in ["ed25519", "secp256k1"]:
                    with self.subTest(protocol=protocol, key=key):
                        blocks = [contract_probe.block(101, [transaction(1, 1)], gas_limit=0),
                            contract_probe.block(102, [transaction(2, 2), transaction(3, 3, "captured.near")], gas_limit=0),
                            contract_probe.block(103, [transaction(4, 4)], gas_limit=0),
                            contract_probe.block(104, [transaction(5, 5)]), contract_probe.block(105)]
                        scenario = dict(caller=dict(accountId=CALLER, seed="persistent-local-order", keyType=key, amount=str(100 * 10**24)), blocks=blocks)
                        # CongestionInfo is an explicit external chunk input. Plan it
                        # through native continuation, never through model gas guesses.
                        planning = Path(directory) / f"plan-{protocol}-{key}"
                        importer.prepare(contract_probe.snapshot(protocol), planning, reference=REFERENCE, model=MODEL, scenario=scenario)
                        original = json.loads((planning / "native.json").read_text())
                        source = {**original, "blocks": []}
                        previous = None
                        for block, specification in zip(original["blocks"], blocks):
                            if previous is not None:
                                block["congestionInfo"] = previous
                                specification["congestionInfo"] = previous
                            source["blocks"].append(block)
                            trace = importer.execute(native, source, planning)
                            previous = trace["blocks"][-1]["nextCongestionInfo"]
                        target = Path(directory) / f"run-{protocol}-{key}"
                        importer.prepare(contract_probe.snapshot(protocol), target, reference=REFERENCE, model=MODEL, scenario=scenario)
                        report = comparator.compare(target, REFERENCE, MODEL)
                        evidence.append(dict(protocol=protocol, keyType=key, scenario=scenario, comparison=report))
                        self.assertIsNone(report["projectionError"])
                        self.assertEqual(report["differences"], [])
                        states = [block["state"] for block in report["model"]["blocks"]]
                        def deposits(state):
                            return [int(row["receipt"]["actions"][0]["deposit"]) for row in state["delayed"]]
                        self.assertEqual([deposits(state) for state in states], [[1], [1, 2], [1, 2, 4, 3], [], []])
                        self.assertTrue(report["model"]["quiescent"])
                        delayed = report["model"]["blocks"][2]["state"]["delayed"]
                        expected_order = [row["receiptId"] for row in delayed]
                        resumed = report["model"]["blocks"][3]["outcomes"]
                        self.assertEqual(resumed[0]["id"], 0)
                        local = resumed[0]["outcome"]["status"]["receiptId"]
                        self.assertEqual([row["id"] for row in resumed[1:]], [local] + expected_order)
        atomic_write(ROOT / "audit/delayed-local-order-regressions.json", (json.dumps(dict(referenceBuild=build,
            scope="persistent FIFO during local/incoming deferral; compute/proof limits remain unmodeled", cases=evidence), indent=2) + "\n").encode())


if __name__ == "__main__":
    unittest.main()
