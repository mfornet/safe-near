"""The block corpus of the chain validator (`tools/localnet/chain_corpus.py`, `chain_validate.py`)."""
import gzip
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[0] / "localnet"))
import chain_corpus  # noqa: E402
import chain_validate  # noqa: E402

CORPUS = chain_corpus.DEFAULT_CORPUS
# every check of `validate_header`, `preprocess_block` and `validate_block` that has a variant
EXPECTED_ERRORS = {
    "InvalidSignature", "Orphan", "InvalidApprovals", "NotEnoughApprovals", "InvalidFinalityInfo",
    "InvalidBlockMerkleRoot", "InvalidBlockOrdinal", "InvalidEpochSyncDataHash", "InvalidEpochHash",
    "InvalidNextBPHash", "InvalidBlockPastTime", "InvalidGasPrice", "InvalidTotalSupply",
    "InvalidRandomnessBeaconOutput", "InvalidChunk", "InvalidChunkMask", "InvalidChunkEndorsement",
    "InvalidChunkEndorsementBitmap", "InvalidValidatorProposals", "InvalidProtocolVersion",
    "EpochOutOfBounds", "InvalidStateRoot", "InvalidTxRoot", "InvalidChunkReceiptsRoot",
    "InvalidChunkHeadersRoot", "Other",
}


class CorpusFiles(unittest.TestCase):
    def test_well_formed(self):
        self.assertEqual(chain_corpus.check(CORPUS), [])

    def test_manifest(self):
        manifest = json.loads((CORPUS / "manifest.json").read_text())
        self.assertEqual(manifest["format"], chain_corpus.FORMAT)
        self.assertEqual(set(manifest["topologies"]), set(chain_corpus.TOPOLOGIES))
        self.assertLessEqual(manifest["totalBytes"], chain_corpus.SIZE_BUDGET)
        reference = json.loads((chain_corpus.ROOT / "near-lean/runtime/reference.json").read_text())
        self.assertEqual(manifest["sourceRevision"], reference["revision"])
        for summary in manifest["topologies"].values():
            self.assertEqual(summary["protocolVersion"], reference["reference_protocol_version"])
            self.assertGreater(summary["blocks"], 500)
            self.assertEqual(sum(summary["variantKinds"].values()), summary["variants"])
            self.assertEqual(sum(summary["variantErrors"].values()), summary["variants"])
            self.assertTrue(set(summary["variantErrors"]) <= EXPECTED_ERRORS, summary["variantErrors"])
            # 39 kinds of invalid block, each on several base blocks
            self.assertGreaterEqual(len(summary["variantKinds"]), 39)
            self.assertTrue(all(n >= 5 for n in summary["variantKinds"].values()), summary["variantKinds"])

    def test_every_check_has_a_variant(self):
        manifest = json.loads((CORPUS / "manifest.json").read_text())
        for topology, summary in manifest["topologies"].items():
            self.assertEqual(set(summary["variantErrors"]), EXPECTED_ERRORS, topology)

    def test_epochs_cover_the_chain(self):
        for topology in chain_corpus.TOPOLOGIES:
            epochs = chain_corpus.read_lines(CORPUS / topology / "epochs.jsonl.gz")
            heights = [e["epochHeight"] for e in epochs]
            self.assertEqual(len(set(e["epochId"] for e in epochs)), len(epochs))
            self.assertGreaterEqual(max(heights), 15)
            self.assertTrue(all(e["protocolVersion"] == 86 for e in epochs))

    def test_sharded_chain_has_two_producers_and_next_epoch_approvals(self):
        blocks = chain_corpus.read_lines(CORPUS / "sharded" / "blocks.jsonl.gz")
        producers = {b["derived"]["blockProducer"] for b in blocks if b["derived"]["blockProducer"]}
        self.assertEqual(producers, {"node0", "node1"})
        for topology in chain_corpus.TOPOLOGIES:
            blocks = chain_corpus.read_lines(CORPUS / topology / "blocks.jsonl.gz")
            self.assertTrue(any(any(int(a[2]) > 0 for a in b["derived"]["approvers"] or [])
                                for b in blocks), topology)


class Tampering(unittest.TestCase):
    """The checks detect a corrupted corpus."""

    def copy(self) -> Path:
        directory = Path(tempfile.mkdtemp(prefix="safe-near-chain-test-"))
        self.addCleanup(shutil.rmtree, directory, ignore_errors=True)
        shutil.copytree(CORPUS, directory / "blocks")
        return directory / "blocks"

    def test_check_detects_a_changed_file(self):
        corpus = self.copy()
        path = corpus / "single" / "blocks.jsonl.gz"
        path.write_bytes(path.read_bytes()[:-8] + b"\0" * 8)
        self.assertTrue(chain_corpus.check(corpus))

    def test_check_detects_an_accepted_variant(self):
        corpus = self.copy()
        for topology in chain_corpus.TOPOLOGIES:
            variants = chain_corpus.read_lines(corpus / topology / "variants.jsonl.gz")
            variants[0]["expected"]["accepted"] = True
            raw = "".join(json.dumps(v, separators=(",", ":")) + "\n" for v in variants).encode()
            (corpus / topology / "variants.jsonl.gz").write_bytes(chain_corpus.gz(raw))
        problems = chain_corpus.check(corpus)
        self.assertTrue(any("not a recorded rejection" in p or "differs" in p for p in problems))

    def test_pack_is_deterministic(self):
        with tempfile.TemporaryDirectory() as temporary:
            raw = Path(temporary) / "raw"
            chain_corpus.unpack(CORPUS, raw, "single")
            first = chain_corpus.gz((raw / "single" / "blocks.jsonl").read_bytes())
            self.assertEqual(first, (CORPUS / "single" / "blocks.jsonl.gz").read_bytes())
            self.assertEqual(gzip.decompress(first), (raw / "single" / "blocks.jsonl").read_bytes())


@unittest.skipUnless(chain_validate.BINARY.exists(), "node-chain-validate is not built")
class LeanDisagreement(unittest.TestCase):
    """The Lean harness fails when its verdict differs from the recorded one."""

    def run_on(self, mutate) -> subprocess.CompletedProcess:
        with tempfile.TemporaryDirectory() as temporary:
            directory = chain_corpus.unpack(CORPUS, Path(temporary), "single")
            mutate(directory)
            return subprocess.run([str(chain_validate.BINARY), str(directory)], capture_output=True, text=True)

    def test_agrees_on_the_corpus(self):
        result = self.run_on(lambda directory: None)
        self.assertEqual(result.returncode, 0, result.stdout)

    def test_fails_on_a_wrong_expected_error(self):
        def mutate(directory: Path):
            path = directory / "variants.jsonl"
            lines = path.read_text().splitlines()
            first = json.loads(lines[0])
            first["expected"]["error"] = "InvalidApprovals" if first["expected"]["error"] != "InvalidApprovals" else "Orphan"
            lines[0] = json.dumps(first, separators=(",", ":"))
            path.write_text("\n".join(lines) + "\n")
        result = self.run_on(mutate)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("FAIL variant", result.stdout)

    def test_fails_on_a_wrong_derived_value(self):
        def mutate(directory: Path):
            path = directory / "blocks.jsonl"
            lines = path.read_text().splitlines()
            block = json.loads(lines[5])
            block["derived"]["blockProducer"] = "somebody-else"
            lines[5] = json.dumps(block, separators=(",", ":"))
            path.write_text("\n".join(lines) + "\n")
        result = self.run_on(mutate)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("block producer", result.stdout)

    def test_fails_when_a_block_is_corrupt(self):
        def mutate(directory: Path):
            path = directory / "blocks.jsonl"
            lines = path.read_text().splitlines()
            block = json.loads(lines[3])
            raw = bytearray(bytes.fromhex(block["block"]))
            raw[-5] ^= 1
            block["block"] = raw.hex()
            lines[3] = json.dumps(block, separators=(",", ":"))
            path.write_text("\n".join(lines) + "\n")
        result = self.run_on(mutate)
        self.assertNotEqual(result.returncode, 0)


if __name__ == "__main__":
    unittest.main()
