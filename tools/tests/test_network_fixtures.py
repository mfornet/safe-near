"""The network oracle fixtures (`tools/localnet/network_oracle.rs`) and its build adapter."""
import json
from pathlib import Path
import re
import sys
import unittest

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
sys.path.insert(0, str(ROOT / "tools/localnet"))
import build  # noqa: E402

FIXTURES = ROOT / "near-lean/node/fixtures/network"
VARIANTS = {"PeerMessage", "Edge", "RoutedBody", "TieredBody", "RoutedMessageV1", "PeerInfo", "SocketAddr"}


def lines(name):
    return [json.loads(line) for line in (FIXTURES / f"{name}.jsonl").read_text().splitlines()]


class Fixtures(unittest.TestCase):
    def test_manifest_matches_files(self):
        manifest = json.loads((FIXTURES / "manifest.json").read_text())
        reference = json.loads((ROOT / "near-lean/runtime/reference.json").read_text())
        self.assertEqual(manifest["protocol_version"], reference["reference_protocol_version"])
        self.assertEqual(manifest["nearcore_release"], reference["release"])
        self.assertTrue(VARIANTS <= set(manifest["types"]))
        for name, counts in manifest["types"].items():
            rows = lines(name)
            self.assertEqual(sum(1 for r in rows if "reject" not in r), counts["accept"], name)
            self.assertEqual(sum(1 for r in rows if "reject" in r), counts["reject"], name)

    def test_lines_are_well_formed(self):
        for path in FIXTURES.glob("*.jsonl"):
            key = "proto" if path.stem == "PeerMessage" else "borsh"
            for row in lines(path.stem):
                self.assertEqual(row["type"], path.stem)
                self.assertRegex(row[key], r"^([0-9a-f]{2})*$")
                if row.get("reject"):
                    self.assertEqual(set(row) - {"type", "name", key, "reject"}, set())
                for k, v in row.items():
                    if k not in ("type", "name", "reject"):
                        self.assertRegex(v, r"^([0-9a-f]{2})*$", (path.stem, row["name"], k))

    def test_every_peer_message_variant_is_covered(self):
        tags = set()
        for row in lines("PeerMessage"):
            if "reject" in row or "/" in row["name"]:
                continue
            raw = bytes.fromhex(row["proto"])
            tag = raw[0] & 0x7f
            if raw[0] & 0x80:
                tag |= (raw[1] & 0x7f) << 7
            tags.add(tag >> 3)
        # the oneof members of network.proto that nearcore sends or accepts
        expected = {4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 25, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37}
        self.assertEqual(expected - tags, set())

    def test_both_verdicts_for_every_type(self):
        for name in json.loads((FIXTURES / "manifest.json").read_text())["types"]:
            rows = lines(name)
            self.assertTrue(any("reject" in r for r in rows), name)
            self.assertTrue(any("reject" not in r for r in rows), name)


BINARY = ROOT / "near-lean/node/.lake/build/bin/node-conformance-network"


@unittest.skipUnless(BINARY.exists(), "node-conformance-network is not built")
class Harness(unittest.TestCase):
    """The Lean check fails when a verdict of nearcore is flipped."""

    def run_on(self, edit):
        import shutil
        import subprocess
        import tempfile
        with tempfile.TemporaryDirectory() as t:
            copy = Path(t) / "network"
            shutil.copytree(FIXTURES, copy)
            edit(copy)
            return subprocess.run([str(BINARY), str(copy)], capture_output=True, text=True).returncode

    def test_unchanged_passes(self):
        self.assertEqual(self.run_on(lambda d: None), 0)

    def test_flipped_verdict_fails(self):
        def flip(d):
            path = d / "PeerInfo.jsonl"
            rows = path.read_text().splitlines()
            rows = [r.replace(',"reject":true', "", 1) if '"reject":true' in r else r for r in rows[:1]] + rows[1:]
            # the first rejected line becomes an accepted one
            for i, r in enumerate(rows):
                if '"reject":true' in r:
                    rows[i] = r.replace(',"reject":true', "")
                    break
            path.write_text("\n".join(rows) + "\n")
        self.assertNotEqual(self.run_on(flip), 0)

    def test_changed_derived_value_fails(self):
        def change(d):
            path = d / "Edge.jsonl"
            text = path.read_text()
            path.write_text(re.sub(r'"verify":"0([01])"', lambda m: '"verify":"0%d"' % (1 - int(m.group(1))), text, count=1))
        self.assertNotEqual(self.run_on(change), 0)


class Adapter(unittest.TestCase):
    def test_network_oracle_is_an_overlay_of_near_network(self):
        binary = "safe-near-network-oracle"
        overlay = [o for o in build.OVERLAYS if o[4] == binary]
        self.assertEqual(len(overlay), 1)
        self.assertEqual(overlay[0][0], "near-network")
        for path, local in build.ADAPTER_FILES[binary]:
            self.assertTrue((ROOT / "tools/localnet" / local).is_file())
            self.assertTrue(path.startswith("chain/network/src/"))
        # the only edit of an existing file is one appended `pub mod`
        for path, text in build.ADAPTER_APPENDS[binary]:
            self.assertEqual(path, "chain/network/src/lib.rs")
            self.assertRegex(text.decode(), r"^\s*#\[path = \"[a-z_.]+\"\]\s*pub mod [a-z_]+;\s*$")

    def test_oracle_source_has_no_network_io(self):
        source = (ROOT / "tools/localnet/network_oracle.rs").read_text()
        self.assertNotRegex(source, re.compile(r"TcpStream|tokio::net"))


if __name__ == "__main__":
    unittest.main()
