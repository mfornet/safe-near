import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest


spec = importlib.util.spec_from_file_location(
    "node_isolation", Path(__file__).resolve().parents[1] / "check_node_isolation.py")
isolation = importlib.util.module_from_spec(spec)
spec.loader.exec_module(isolation)

PROTOCOL = 'def nearcoreRelease : String := "2.13.4"\ndef protocolVersion : Nat := 86\n'


class NodeIsolationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        subprocess.run(["git", "init", "-q", str(self.root)], check=True)
        self.write("near-lean/runtime/reference.json",
                   json.dumps({"release": "2.13.4", "reference_protocol_version": 86}))
        self.package("near-lean/vm", [])
        self.package("near-lean/runtime", ["../vm"])
        self.package("near-lean/chain", ["../runtime"])
        self.package("near-lean/crypto", [])
        self.package("near-lean/node", ["../chain", "../crypto"])
        self.write("near-lean/node/NearNode/Protocol.lean", PROTOCOL)
        self.package("contracts/c/verification", ["../../../near-lean/runtime"])

    def write(self, name, value):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(value)

    def package(self, directory, requires):
        lines = ['name = "P"\n'] + [f'[[require]]\nname = "R{i}"\npath = "{path}"\n'
                                     for i, path in enumerate(requires)]
        self.write(f"{directory}/lakefile.toml", "".join(lines))

    def test_current_layout_passes(self):
        self.assertEqual(isolation.check(self.root), [])

    def test_contract_reaching_chain_transitively_fails(self):
        self.package("near-lean/vm", ["../chain"])
        errors = isolation.check(self.root)
        self.assertIn("contracts/c/verification: contract verification depends on near-lean/chain", errors)

    def test_only_node_may_require_node(self):
        self.package("near-lean/tool", ["../node"])
        self.assertEqual(isolation.check(self.root), ["near-lean/tool: only the node may depend on near-lean/node"])

    def test_crypto_requires_no_repository_package(self):
        self.package("near-lean/crypto", ["../vm"])
        self.assertEqual(
            isolation.check(self.root),
            ["near-lean/crypto: the crypto package must not require repository packages (near-lean/vm)"])

    def test_crypto_may_not_require_the_node(self):
        self.package("near-lean/crypto", ["../node"])
        errors = isolation.check(self.root)
        self.assertIn("near-lean/crypto: only the node may depend on near-lean/node", errors)

    def test_native_attributes_and_link_settings_fail(self):
        self.write("near-lean/vm/A.lean", "-- prose about extern is fine\n@[extern \"f\"] opaque f : Nat\n")
        self.write("near-lean/vm/B.lean", "attribute [implemented_by g] f\n")
        self.write("near-lean/vm/lakefile.toml", 'name = "P"\nmoreLinkArgs = ["-lsodium"]\n')
        errors = isolation.check(self.root)
        self.assertEqual(len(errors), 3, errors)
        self.assertTrue(errors[0].startswith("near-lean/vm/A.lean:2:"))

    def test_protocol_pin_must_match_reference(self):
        self.write("near-lean/node/NearNode/Protocol.lean", PROTOCOL.replace("86", "87"))
        self.assertEqual(isolation.check(self.root), ["NearNode.Protocol: protocolVersion must be 86"])


if __name__ == "__main__":
    unittest.main()
