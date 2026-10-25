"""The inputs of the Lean chain apply (`tools/localnet/chain_apply.py`): the corpus extras and the runner."""
import json
from pathlib import Path
import sys
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[0] / "localnet"))
import chain_apply  # noqa: E402
import chain_corpus  # noqa: E402

CORPUS = chain_corpus.DEFAULT_CORPUS


class Extras(unittest.TestCase):
    def test_listed_in_the_manifest(self):
        manifest = json.loads((CORPUS / "manifest.json").read_text())
        for topology, summary in manifest["topologies"].items():
            self.assertIn("genesis.json", summary["files"], topology)
            self.assertIn("chunks.jsonl.gz", summary["files"], topology)
        self.assertEqual(chain_corpus.check(CORPUS), [])

    def test_genesis_layout_is_the_first_epoch_layout(self):
        for topology in chain_corpus.TOPOLOGIES:
            genesis = json.loads((CORPUS / topology / "genesis.json").read_text())
            epochs = chain_corpus.read_lines(CORPUS / topology / "epochs.jsonl.gz")
            first = next(e for e in epochs if e["epochId"] == "0" * 64)
            self.assertEqual(genesis["shardLayout"], first["shardLayout"], topology)
            self.assertGreaterEqual(len(genesis["validators"]), 1)
            kinds = {next(iter(r)) for r in genesis["records"]}
            self.assertEqual(kinds, {"account", "accessKey"})

    def test_chunk_rows(self):
        for topology in chain_corpus.TOPOLOGIES:
            rows = chain_corpus.read_lines(CORPUS / topology / "chunks.jsonl.gz")
            keys = [(r["height"], r["shardId"]) for r in rows]
            self.assertEqual(keys, sorted(set(keys)), topology)
            self.assertGreater(len(rows), 100)
            for row in rows:
                for field in ("transactions", "incomingReceipts", "outgoingReceipts"):
                    self.assertTrue(all(isinstance(x, str) and bytes.fromhex(x) for x in row[field]), field)
                self.assertIn("validatorAccountsUpdate", row["context"])

    def test_shard_layout_encoder(self):
        layout = {"V2": {"boundary_accounts": ["b"], "shard_ids": [1, 0], "id_to_index_map": {"0": 1, "1": 0},
                         "index_to_id_map": {"0": 1, "1": 0}, "shards_split_map": None, "shards_parent_map": None,
                         "version": 0}}
        raw = chain_apply.shard_layout_v2(layout)
        self.assertEqual(raw[0], 2)
        self.assertEqual(raw[1:5], (1).to_bytes(4, "little"))
        self.assertEqual(raw[-4:], bytes(4))


class Runner(unittest.TestCase):
    def test_report_line(self):
        line = ("safe-near-localnet-1s: epochs 19/19 equal, validator accounts updates 148/148 equal, chunks: "
                "ChunkExtra equal 514/514, pre-state round trip 514/514, incoming receipts equal 148/148, "
                "outgoing receipts equal 148/148, blocks 513/513 accepted (1234 ms)")
        match = chain_apply.REPORT.search(line)
        self.assertEqual([int(x) for x in match.groups()][:4], [19, 19, 148, 148])
        self.assertEqual(len(match.groups()), 15)


if __name__ == "__main__":
    unittest.main()
