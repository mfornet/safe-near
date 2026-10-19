"""The conformance gate must detect changes in every financial/receipt field."""
import copy
import unittest

from compare import differences


class StrictComparison(unittest.TestCase):
    def test_observation_changes_cannot_be_ignored(self):
        observation = {
            "balance": "1000000000000000000000000",
            "storageUsage": 42,
            "gasBurnt": 123,
            "gasUsed": 456,
            "returnData": {"kind": "receipt", "index": 1},
            "storage": [[[0, 255], [42]]],
            "logs": ["first", "second"],
            "receipts": [{"receiverId": [97], "dependencies": [0],
                          "actions": [{"kind": "transfer", "deposit": "1"}]}],
            "aborted": None,
            "issue": None,
        }
        for path, replacement in [
            (("balance",), "999999999999999999999999"),
            (("storageUsage",), 43),
            (("gasBurnt",), 124),
            (("gasUsed",), 457),
            (("returnData", "index"), 0),
            (("storage", 0, 1, 0), 43),
            (("logs",), ["second", "first"]),
            (("receipts", 0, "receiverId", 0), 98),
            (("receipts", 0, "dependencies"), []),
            (("receipts", 0, "actions", 0, "deposit"), "2"),
            (("aborted",), "panic"),
            (("issue",), "incomplete"),
        ]:
            changed = copy.deepcopy(observation)
            parent = changed
            for key in path[:-1]:
                parent = parent[key]
            parent[path[-1]] = replacement
            with self.subTest(path=path):
                self.assertTrue(differences(observation, changed))

    def test_missing_field_and_explicit_null_are_distinct(self):
        self.assertTrue(differences({"aborted": None}, {}))

    def test_boolean_is_not_an_integer(self):
        self.assertTrue(differences({"gasBurnt": 1}, {"gasBurnt": True}))

    def test_object_order_is_not_an_observation(self):
        self.assertFalse(differences({"gasBurnt": 1, "gasUsed": 2}, {"gasUsed": 2, "gasBurnt": 1}))


if __name__ == "__main__":
    unittest.main()
