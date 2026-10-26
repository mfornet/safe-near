"""The comparison of the RPC conformance run (`tools/localnet/rpc_conformance.py`): what it normalises and what it does not."""
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools/localnet"))
import rpc_conformance as rc  # noqa: E402


class Comparison(unittest.TestCase):
    def test_equal_documents_have_no_difference(self):
        self.assertEqual(rc.diff({"a": [1, {"b": "c"}]}, {"a": [1, {"b": "c"}]}), [])

    def test_a_difference_in_a_value_a_missing_member_and_a_length_are_reported(self):
        self.assertEqual(len(rc.diff({"a": 1}, {"a": 2})), 1)
        self.assertEqual(len(rc.diff({"a": 1}, {"a": 1, "b": 2})), 1)
        self.assertEqual(len(rc.diff({"a": [1, 2]}, {"a": [1]})), 1)

    def test_status_drops_only_the_listed_members(self):
        left = {"result": {"version": {"v": 1}, "uptime_sec": 3, "sync_info": {"latest_block_height": 7}}}
        right = {"result": {"version": {"v": 2}, "uptime_sec": 9, "sync_info": {"latest_block_height": 7}}}
        self.assertEqual(rc.diff(rc.normalise("status", left), rc.normalise("status", right)), [])
        right["result"]["sync_info"]["latest_block_height"] = 8
        self.assertEqual(len(rc.diff(rc.normalise("status", left), rc.normalise("status", right))), 1)

    def test_other_methods_are_not_normalised(self):
        left, right = {"result": {"version": 1}}, {"result": {"version": 2}}
        self.assertEqual(len(rc.diff(rc.normalise("block", left), rc.normalise("block", right))), 1)

    def test_a_failure_is_compared_unless_the_lean_node_says_it_does_not_render_it(self):
        left = {"result": {"status": {"Failure": {"ActionError": {"index": 0}}}}}
        right = {"result": {"status": {"Failure": {"ActionError": {"index": 1}}}}}
        self.assertEqual(len(rc.diff(rc.normalise("tx", left), rc.normalise("tx", right))), 1)
        right = {"result": {"status": {"Failure": rc.UNRENDERED}}}
        a, b = rc.normalise("tx", left), rc.normalise("tx", right)
        self.assertEqual(rc.unify_unrendered(a, b), 1)
        self.assertEqual(rc.diff(a, b), [])

    def test_the_outcome_metadata_is_compared_in_full(self):
        left = {"result": {"metadata": {"version": 4, "gas_profile": [1], "contracts": [None]}}}
        right = {"result": {"metadata": {"version": 4, "gas_profile": [1], "contracts": [None]}}}
        self.assertEqual(rc.diff(rc.normalise("tx", left), rc.normalise("tx", right)), [])
        right["result"]["metadata"].update(gas_profile=[], contracts=[])
        self.assertEqual(len(rc.diff(rc.normalise("tx", left), rc.normalise("tx", right))), 2)
        right["result"]["metadata"].update(version=3, gas_profile=[1], contracts=[None])
        self.assertEqual(len(rc.diff(rc.normalise("tx", left), rc.normalise("tx", right))), 1)

    def test_the_peers_of_network_info_are_compared_as_a_count(self):
        left = {"result": {"active_peers": [{"id": "a"}], "known_producers": [], "num_active_peers": 1}}
        right = {"result": {"active_peers": [{"id": "b"}], "known_producers": [], "num_active_peers": 1}}
        self.assertEqual(rc.diff(rc.normalise("network_info", left), rc.normalise("network_info", right)), [])


if __name__ == "__main__":
    unittest.main()
