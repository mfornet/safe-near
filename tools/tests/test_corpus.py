"""Corpus bundles: packing, tags, comparison, selection and the committed manifest (no neard, no Lean)."""
import copy
import gzip
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[0] / "localnet"))
import corpus  # noqa: E402

CORPUS = HERE.parents[1] / "near-lean/chain/corpus"
BIG = "ab" * 4000                       # an 4000-byte value: stored as a blob


def bundle(height=10, shard=0):
    transfer = {"signer_id": "a.near", "receiver_id": "b.near", "nonce": 1,
                "actions": [{"Transfer": {"deposit": "5"}}, "CreateAccount",
                            {"DeployContract": {"code": "A" * 2000}}]}
    outcome = {"logs": ["hi"], "status": {"SuccessValue": ""}, "receipt_ids": [], "gas_burnt": 1,
               "tokens_burnt": "1", "executor_id": "b.near",
               "metadata": {"version": 3, "gas_profile": [
                   {"cost_category": "WASM_HOST_COST", "cost": "SHA256_BASE", "gas_used": 5},
                   {"cost_category": "ACTION_COST", "cost": "TRANSFER", "gas_used": 5}]}}
    return {
        "formatVersion": 1,
        "meta": {"chainId": "c", "height": height, "blockHash": "00" * 32, "prevBlockHash": "11" * 32,
                 "chunkHash": "22" * 32, "shardId": shard, "shardUId": {"version": 3, "shardId": shard},
                 "protocolVersion": 86},
        "context": {"currentProtocolVersion": 86, "validatorAccountsUpdate": None,
                    "congestionInfo": [[0, "00", 0]], "blockHeight": height},
        "preState": {"root": "33" * 32, "entries": [["00" + "61", "0102"], ["01" + "61", BIG], ["0261", "03"]]},
        "inputs": {"transactions": [{"borsh": BIG, "valid": True, "hash": "44" * 32, "view": transfer,
                                     "actions": [{"DeployContract": {"code": "B" * 2000}}]}],
                   "incomingReceipts": [], "incomingReceiptTyped": [],
                   "incomingReceiptViews": [
                       {"predecessor_id": "x.near", "receiver_id": "b.near", "receipt_id": "55" * 32,
                        "receipt": {"Action": {"actions": [{"FunctionCall": {}}], "input_data_ids": ["z"]}}}]},
        "expected": {
            "postStateRoot": "66" * 32, "outcomes": [{"id": "44" * 32, "borsh": "00", "view": outcome, "computeUsage": 9}],
            "outcomeRoot": "77" * 32, "outgoingReceipts": [], "outgoingReceiptViews": [],
            "stateChanges": "00000000", "stateDiff": [["00" + "61", "0103"], ["0161", BIG], ["0261", None]],
            "gasUsed": 1, "balanceBurnt": "1", "balanceStats": {}, "validatorProposals": "00000000",
            "congestionInfo": "00", "bandwidthRequests": None, "bandwidthSchedulerStateHash": "00" * 32,
            "delayedReceiptsCount": 0, "processedYieldTimeouts": "00000000", "contractUpdates": {}},
    }


class Packing(unittest.TestCase):
    def test_round_trip_and_blob_sharing(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            first, second = bundle(10), bundle(11)
            corpus.pack(first, "single", root)
            corpus.pack(second, "single", root)
            blobs = list((root / "blobs").iterdir())
            digest = hashlib.sha256(bytes.fromhex(BIG)).hexdigest()
            self.assertIn(digest + ".bin.gz", [blob.name for blob in blobs])      # stored once for both chunks
            self.assertEqual(len(blobs), 3)
            restored = corpus.unpack(root / "chunks" / "single-h00000010-s0")
            self.assertEqual(restored, dict(first, decoded=None))
            self.assertEqual(len(list((root / "blobs").iterdir())), 3)   # the value, the view's and the typed code

    def test_decoded_records_round_trip_with_shared_code(self):
        decoded = {"preState": [{"key": "01", "record": {"Contract": {"account_id": "a.near", "code": "A" * 2000}}},
                                {"key": "0f", "opaque": True}]}
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus.pack(bundle(), "single", root)
            chunk = root / "chunks" / "single-h00000010-s0"
            corpus.pack_decoded(chunk, root, decoded)
            self.assertEqual(corpus.unpack(chunk)["decoded"], decoded)
            # the contract code is the same blob the transaction view uses
            self.assertEqual(len(list((root / "blobs").iterdir())), 3)

    def test_packing_is_deterministic(self):
        files = []
        for _ in range(2):
            with tempfile.TemporaryDirectory() as directory:
                root = Path(directory)
                corpus.pack(bundle(), "sharded", root)
                files.append({str(p.relative_to(root)): p.read_bytes() for p in sorted(root.rglob("*")) if p.is_file()})
        self.assertEqual(files[0], files[1])

    def test_corrupt_blob_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            corpus.pack(bundle(), "single", root)
            path = root / "blobs" / (hashlib.sha256(bytes.fromhex(BIG)).hexdigest() + ".bin.gz")
            path.write_bytes(gzip.compress(b"tampered"))
            with self.assertRaises(ValueError):
                corpus.unpack(root / "chunks" / "single-h00000010-s0")


class Tags(unittest.TestCase):
    def test_features_are_derived_from_views(self):
        found = corpus.tags(bundle())
        for tag in ["tx", "action:Transfer", "action:CreateAccount", "action:DeployContract", "incoming-receipt",
                    "receipt:Action", "receipt:callback", "status:SuccessValue", "logs", "host:sha256",
                    "cost:transfer", "state-column:account", "state-column:contract-code", "state-change:access-key",
                    "shard-layout:1", "protocol:86"]:
            self.assertIn(tag, found)
        self.assertEqual(found, sorted(set(found)))
        self.assertNotIn("multi-shard", found)

    def test_failures_and_epoch_start(self):
        value = bundle()
        value["expected"]["outcomes"][0]["view"]["status"] = {"Failure": {"ActionError": {"index": 0, "kind": {"FunctionCallError": {}}}}}
        value["context"]["validatorAccountsUpdate"] = {}
        value["context"]["congestionInfo"] = [[0, "00", 0], [1, "00", 0]]
        found = corpus.tags(value)
        for tag in ["status:Failure", "failure:ActionError", "failure:FunctionCallError", "epoch-start", "multi-shard"]:
            self.assertIn(tag, found)

    def test_host_function_names(self):
        self.assertEqual(corpus.host_function("ED25519_VERIFY_BASE"), "ed25519_verify")
        self.assertEqual(corpus.host_function("STORAGE_WRITE_VALUE_BYTE"), "storage_write_value")
        self.assertEqual(corpus.host_function("ECRECOVER_BASE"), "ecrecover")


class Comparison(unittest.TestCase):
    def test_first_difference_paths(self):
        self.assertIsNone(corpus.first_difference({"a": [1, {"b": 2}]}, {"a": [1, {"b": 2}]}))
        self.assertEqual(corpus.first_difference({"a": [1, {"b": 2}]}, {"a": [1, {"b": 3}]}), ".a[1].b")
        self.assertEqual(corpus.first_difference({"a": [1]}, {"a": [1, 2]}), ".a (length 1 != 2)")
        self.assertEqual(corpus.first_difference({"a": 1}, {}), ".a (missing)")
        self.assertEqual(corpus.first_difference({}, {"a": 1}), ".a (unexpected)")

    def test_oracle_comparison_reports_the_first_field_in_order(self):
        expected = bundle()["expected"]
        actual = copy.deepcopy(expected)
        self.assertIsNone(corpus.compare_oracle(expected, actual))
        actual["gasUsed"] = 2
        actual["postStateRoot"] = "00" * 32
        self.assertEqual(corpus.compare_oracle(expected, actual), "postStateRoot")
        del actual["delayedReceiptsCount"]
        self.assertEqual(corpus.compare_oracle(expected, actual), "postStateRoot")
        actual["postStateRoot"] = expected["postStateRoot"]
        self.assertEqual(corpus.compare_oracle(expected, actual), "gasUsed")


class Selection(unittest.TestCase):
    ENTRIES = [{"name": "a", "size": 10, "blobs": {}, "tags": ["x", "y"]},
               {"name": "b", "size": 10, "blobs": {}, "tags": ["y", "z"]},
               {"name": "c", "size": 500, "blobs": {}, "tags": ["w"]},
               {"name": "d", "size": 10, "blobs": {}, "tags": ["x"]}]

    def test_greedy_cover_is_deterministic_and_within_budget(self):
        chosen = corpus.select(self.ENTRIES, budget=40)
        self.assertEqual(chosen, corpus.select(list(reversed(self.ENTRIES)), budget=40))
        self.assertLessEqual(sum(e["size"] for e in self.ENTRIES if e["name"] in chosen), 40)
        covered = {t for e in self.ENTRIES if e["name"] in chosen for t in e["tags"]}
        self.assertEqual(covered, {"x", "y", "z"})

    def test_always_chunks_come_first_and_shared_blobs_are_paid_once(self):
        entries = [{"name": "p", "size": 10, "blobs": {"h": 1000}, "tags": ["a"]},
                   {"name": "q", "size": 10, "blobs": {"h": 1000}, "tags": ["b"]},
                   {"name": "r", "size": 10, "blobs": {"k": 1000}, "tags": ["c"]}]
        self.assertEqual(corpus.select(entries, budget=1030, always={"p"}), ["p", "q"])   # q reuses p's blob
        self.assertEqual(corpus.select(entries, budget=1030), ["p", "q"])
        self.assertEqual(corpus.select(entries, budget=2040), ["p", "q", "r"])

    def test_chunks_with_work_fill_the_remaining_budget(self):
        entries = [{"name": "a", "size": 10, "blobs": {}, "tags": ["x", "tx"]},
                   {"name": "b", "size": 20, "blobs": {}, "tags": ["tx"]},
                   {"name": "c", "size": 30, "blobs": {}, "tags": ["tx"]},
                   {"name": "d", "size": 5, "blobs": {}, "tags": []}]
        self.assertEqual(corpus.select(entries, budget=60), ["a", "b", "c"])
        self.assertEqual(corpus.select(entries, budget=35), ["a", "b"])


@unittest.skipUnless((CORPUS / "manifest.json").exists(), "no committed corpus")
class CommittedCorpus(unittest.TestCase):
    def setUp(self):
        self.manifest = json.loads((CORPUS / "manifest.json").read_text())

    def test_manifest_lists_every_chunk_with_tags(self):
        directories = sorted(p.name for p in (CORPUS / "chunks").iterdir() if p.is_dir())
        self.assertEqual([row["name"] for row in self.manifest["chunks"]], directories)
        for row in self.manifest["chunks"]:
            self.assertTrue(row["tags"], row["name"])
            self.assertEqual(row["tags"], sorted(set(row["tags"])))
            self.assertEqual(row["protocolVersion"], 86)
            self.assertIn(row["topology"], {"single", "sharded"})
            for name in ["meta.json", "context.json", "pre_state.json.gz", "decoded.json.gz", "inputs.json.gz", "expected.json.gz"]:
                self.assertTrue((CORPUS / "chunks" / row["name"] / name).is_file(), (row["name"], name))

    def test_manifest_matches_the_chunks_it_describes(self):
        rebuilt = corpus.manifest(CORPUS, self.manifest.get("build"))
        self.assertEqual(rebuilt, self.manifest)

    def test_every_blob_is_referenced_and_intact(self):
        referenced = set()
        for directory in corpus.chunk_dirs(CORPUS):
            text = gzip.decompress((directory / "pre_state.json.gz").read_bytes()).decode()
            text += gzip.decompress((directory / "inputs.json.gz").read_bytes()).decode()
            text += gzip.decompress((directory / "expected.json.gz").read_bytes()).decode()
            for blob in (CORPUS / "blobs").iterdir():
                if blob.name.removesuffix(".bin.gz") in text:
                    referenced.add(blob.name)
        for blob in (CORPUS / "blobs").iterdir():
            self.assertIn(blob.name, referenced)
            digest = blob.name.removesuffix(".bin.gz")
            self.assertEqual(hashlib.sha256(gzip.decompress(blob.read_bytes())).hexdigest(), digest)

    def test_corpus_size_budget(self):
        total = sum(p.stat().st_size for p in CORPUS.rglob("*") if p.is_file())
        self.assertLess(total, 30 * 1024 * 1024)

    def test_required_features_are_covered(self):
        for tag in ["action:Transfer", "action:CreateAccount", "action:DeployContract", "action:FunctionCall",
                    "action:AddKey", "action:DeleteKey", "action:DeleteAccount", "action:Stake", "receipt:Data",
                    "multi-shard", "shard-layout:1", "status:Failure", "logs"]:
            self.assertIn(tag, self.manifest["tagCoverage"])


if __name__ == "__main__":
    unittest.main()
