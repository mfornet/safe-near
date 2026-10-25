"""The harness of the validator acceptance (`tools/localnet/validator_accept.py`) and its topology."""
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "tools/localnet"))
import localnet  # noqa: E402
import nearcodec as nc  # noqa: E402
import validator_accept as va  # noqa: E402


def row(height, author, root="a" * 40, new=True, shard=0):
    return {"height": height, "hash": nc.b58encode(bytes([height % 256]) * 32), "author": author,
            "chunks": [{"shard": shard, "new": new, "author": author, "prevStateRoot": nc.b58encode(bytes.fromhex(root + "0" * 24)),
                        "hash": "h"}], "approvals": 2, "lastFinal": ""}


def applied_line(height, root="a" * 40):
    return json.dumps({"height": height, "hash": (bytes([height % 256]) * 32).hex(),
                       "chunks": [{"shard": 0, "stateRoot": root + "0" * 24}]})


class Topology(unittest.TestCase):
    def test_two_validators_hold_equal_stakes_and_no_validator_is_kicked_out(self):
        spec = localnet.TOPOLOGIES["validator"]
        self.assertEqual((spec["validators"], spec["shards"], spec["neard"]), (2, 1, [0]))
        self.assertTrue(spec["noKickout"])

    def test_ports_do_not_clash(self):
        ports = {localnet.rpc_port(t, i) for t, s in localnet.TOPOLOGIES.items() for i in range(s["validators"])}
        ports |= {localnet.network_port(t, i) for t, s in localnet.TOPOLOGIES.items() for i in range(s["validators"])}
        self.assertEqual(len(ports), 2 * sum(s["validators"] for s in localnet.TOPOLOGIES.values()))


class Analysis(unittest.TestCase):
    def setUp(self):
        import tempfile
        self.directory = Path(tempfile.mkdtemp())
        self.rows = [row(1, "node0"), row(2, "node1"), row(3, "node1"), row(4, "node0")]
        self.stall = {"stalled": True, "resumed": True}

    def result(self, applied=None, report=None, stall=None, rows=None):
        applied = applied if applied is not None else [applied_line(h) for h in (1, 2, 3)]
        (self.directory / "applied.jsonl").write_text("\n".join(applied) + "\n")
        report = {"disconnects": [], "failure": None, "handshakes": 1} if report is None else report
        return va.analyse(self.directory, report, stall if stall is not None else self.stall,
                          rows if rows is not None else self.rows, head=40, final=38)

    def test_agreement_passes(self):
        r = self.result()
        self.assertTrue(r["ok"], r)
        self.assertEqual((r["blocksByLean"], r["chunksByLean"], r["stateRootsChecked"], r["stateRootsEqual"]), (2, 2, 3, 3))

    def test_a_different_state_root_fails(self):
        r = self.result(applied=[applied_line(1), applied_line(2, root="b" * 40), applied_line(3)])
        self.assertFalse(r["ok"])
        self.assertTrue(any("state root" in p for p in r["problems"]))

    def test_a_different_block_fails(self):
        bad = json.loads(applied_line(2))
        bad["hash"] = "00" * 32
        r = self.result(applied=[applied_line(1), json.dumps(bad), applied_line(3)])
        self.assertFalse(r["ok"])

    def test_a_disconnect_fails(self):
        self.assertFalse(self.result(report={"disconnects": ["closed"], "failure": None, "handshakes": 1})["ok"])

    def test_a_refused_connection_before_neard_listens_is_not_a_disconnect(self):
        report = {"disconnects": ["no such thing (error code: 111, connection refused)"], "failure": None, "handshakes": 1}
        self.assertTrue(self.result(report=report)["ok"])

    def test_a_second_handshake_fails(self):
        self.assertFalse(self.result(report={"disconnects": [], "failure": None, "handshakes": 2})["ok"])

    def test_a_failure_fails(self):
        self.assertFalse(self.result(report={"disconnects": [], "failure": "block 7: applying", "handshakes": 1})["ok"])

    def test_no_block_by_the_lean_node_fails(self):
        rows = [row(h, "node0") for h in (1, 2, 3, 4)]
        self.assertFalse(self.result(rows=rows)["ok"])

    def test_a_chain_that_does_not_stop_without_the_lean_node_fails(self):
        self.assertFalse(self.result(stall={"stalled": False, "resumed": True})["ok"])

    def test_finality_that_stays_behind_fails(self):
        (self.directory / "applied.jsonl").write_text(applied_line(1) + "\n")
        r = va.analyse(self.directory, {"disconnects": [], "failure": None}, self.stall, self.rows, head=100, final=3)
        self.assertFalse(r["finalityAdvanced"])
        self.assertFalse(r["ok"])


if __name__ == "__main__":
    unittest.main()
