"""The state sync oracle fixtures (`tools/node-conformance/native-trie/src/bin/state_sync_oracle.rs`)."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FIXTURES = ROOT / "near-lean/node/fixtures/state-sync"
BINARY = ROOT / "near-lean/node/.lake/build/bin/node-conformance-sync"
HEX = re.compile(r"^([0-9a-f]{2})*$")


def rows(name):
    return [json.loads(line) for line in (FIXTURES / name).read_text().splitlines() if line.strip()]


class Zstd(unittest.TestCase):
    def test_frames_are_frames(self):
        for row in rows("zstd.jsonl"):
            frame = bytes.fromhex(row["frame"])
            self.assertEqual(frame[:4], bytes.fromhex("28b52ffd"), row["name"])
            if "raw" in row:
                raw = bytes.fromhex(row["raw"])
                self.assertEqual(len(raw), row["rawLength"], row["name"])
                self.assertEqual(hashlib.sha256(raw).hexdigest(), row["rawSha256"], row["name"])

    def test_the_shapes_the_decoder_has_to_know_are_present(self):
        styles = {row["style"] for row in rows("zstd.jsonl")}
        self.assertEqual(styles, {"stream", "bulk", "checksum", "concat"})
        levels = {row["level"] for row in rows("zstd.jsonl")}
        self.assertIn(1, levels)       # what nearcore uses
        self.assertTrue(any(level < 0 for level in levels) and any(level > 15 for level in levels))
        sizes = [row["rawLength"] for row in rows("zstd.jsonl")]
        self.assertTrue(min(sizes) == 0 and max(sizes) > 256 * 1024)     # several blocks

    def test_checksum_frames_carry_the_flag(self):
        for row in rows("zstd.jsonl"):
            descriptor = bytes.fromhex(row["frame"])[4]
            self.assertEqual(bool(descriptor & 4), row["style"] == "checksum" and row["rawLength"] >= 0, row["name"])


class Parts(unittest.TestCase):
    def test_every_part_follows_its_trie(self):
        tries = {}
        parts = {}
        for row in rows("parts.jsonl"):
            if "entries" in row:
                self.assertRegex(row["root"], HEX)
                tries[row["case"]] = row
            elif "mutation" in row:
                self.assertIn((row["case"], row["baseIdx"], row["baseTotal"]), parts)
                self.assertIsInstance(row["valid"], bool)
            else:
                self.assertIn(row["case"], tries)
                self.assertLess(row["idx"], row["total"])
                for node in row["nodes"]:
                    self.assertRegex(node, HEX)
                parts[(row["case"], row["idx"], row["total"])] = row
        self.assertGreaterEqual(len(tries), 8)

    def test_the_trie_hash_is_the_first_node_of_the_only_part(self):
        for row in rows("parts.jsonl"):
            if "nodes" in row and row["total"] == 1 and row["nodes"]:
                hashes = {hashlib.sha256(bytes.fromhex(n)).hexdigest() for n in row["nodes"]}
                roots = {r["root"] for r in rows("parts.jsonl") if "entries" in r and r["case"] == row["case"]}
                self.assertTrue(roots <= hashes, row["case"])

    def test_both_verdicts_are_there(self):
        verdicts = {row["valid"] for row in rows("parts.jsonl") if "mutation" in row}
        self.assertEqual(verdicts, {True, False})
        kinds = {row["mutation"] for row in rows("parts.jsonl") if "mutation" in row}
        self.assertTrue({"remove", "flip", "repeat", "add", "empty", "keep"} <= kinds)


@unittest.skipUnless(BINARY.exists(), "node-conformance-sync is not built")
class Harness(unittest.TestCase):
    """The Lean check fails when a fixture is changed."""

    def run_on(self, edit):
        with tempfile.TemporaryDirectory() as t:
            copy = Path(t) / "state-sync"
            shutil.copytree(FIXTURES, copy)
            edit(copy)
            return subprocess.run([str(BINARY), str(copy)], capture_output=True, text=True).returncode

    def test_unchanged_passes(self):
        self.assertEqual(self.run_on(lambda d: None), 0)

    def test_a_flipped_verdict_fails(self):
        def flip(d):
            path = d / "parts.jsonl"
            text = path.read_text()
            at = text.index('"valid":true')
            path.write_text(text[:at] + '"valid":false' + text[at + len('"valid":true'):])
        self.assertNotEqual(self.run_on(flip), 0)

    def test_a_changed_frame_fails(self):
        def change(d):
            path = d / "zstd.jsonl"
            lines = path.read_text().splitlines()
            row = json.loads(lines[0])
            for i, line in enumerate(lines):
                r = json.loads(line)
                if r["rawLength"] > 0 and "raw" in r:
                    r["rawSha256"] = "00" * 32
                    lines[i] = json.dumps(r, separators=(",", ":"))
                    break
            path.write_text("\n".join(lines) + "\n")
        self.assertNotEqual(self.run_on(change), 0)

    def test_a_changed_part_fails(self):
        def change(d):
            path = d / "parts.jsonl"
            lines = path.read_text().splitlines()
            for i, line in enumerate(lines):
                r = json.loads(line)
                if "nodes" in r and "mutation" not in r and r["nodes"] and r["total"] == 3:
                    r["nodes"][0] = r["nodes"][0][:-2] + ("00" if r["nodes"][0][-2:] != "00" else "01")
                    lines[i] = json.dumps(r, separators=(",", ":"))
                    break
            path.write_text("\n".join(lines) + "\n")
        self.assertNotEqual(self.run_on(change), 0)


if __name__ == "__main__":
    unittest.main()
