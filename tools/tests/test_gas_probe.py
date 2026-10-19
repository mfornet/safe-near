"""The targeted native/Lean financial comparison must fail on observation drift."""

import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "chain-conformance"))
import gas_probe


class GasObservationTests(unittest.TestCase):
    def test_nested_fields_queue_order_counts_and_extra_fields_are_observed(self):
        expected = {"blocks": [{"outcomes": [{"gasBurnt": 4, "tokensBurnt": "8"}],
                                "pendingReceipts": [{"receiptId": 1}, {"receiptId": 2}]}]}
        self.assertEqual(gas_probe.differences(expected, copy.deepcopy(expected)), [])
        changes = [
            lambda x: x["blocks"][0]["outcomes"][0].update(gasBurnt=0),
            lambda x: x["blocks"][0]["outcomes"][0].update(tokensBurnt="0"),
            lambda x: x["blocks"][0]["outcomes"].clear(),
            lambda x: x["blocks"][0]["pendingReceipts"].reverse(),
            lambda x: x["blocks"][0].update(extra=1),
            lambda x: x["blocks"][0]["outcomes"][0].update(gasBurnt=True),
        ]
        for change in changes:
            with self.subTest(change=change):
                actual = copy.deepcopy(expected)
                change(actual)
                self.assertTrue(gas_probe.differences(expected, actual))

    def test_unmodeled_actions_and_state_records_are_rejected(self):
        with self.assertRaises(ValueError):
            gas_probe.simple_action({"FunctionCall": {}})
        with self.assertRaises(ValueError):
            gas_probe.state({"decodedRecords": [{"record": {"Contract": {}}}]}, 1)
        self.assertEqual(gas_probe.public_key("ed25519:" + "1" * 32), [0] * 33)
        with self.assertRaises(ValueError):
            gas_probe.public_key("ed25519:1")
        with self.assertRaisesRegex(ValueError, "signed request bytes"):
            gas_probe.model_request(
                {"pendingReceipts": [], "protocolVersion": 86, "blocks": [{"transactions": [[1]]}]},
                {"initialState": {"decodedRecords": []}, "blocks": [{"inputs": {"transactions": []}}]},
                Path("."))


if __name__ == "__main__":
    unittest.main()
