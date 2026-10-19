import base64
from copy import deepcopy
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import near_snapshot as snapshot


def b64(value):
    return base64.b64encode(value).decode()


class FakeRPC:
    def __init__(self):
        self.calls = []
        self.code = b"\x00asm\x01\x00\x00\x00"
        self.account = {"amount": "123", "locked": "0", "storage_usage": 48,
                        "code_hash": snapshot.code_hash(self.code)}
        self.data = {b"": b"root", b"STATE": b"state", b"a\x00": b"\xff"}
        self.wrong_block = False

    def __call__(self, method, params, **kwargs):
        self.calls.append((method, params, kwargs))
        if method == "block":
            return {"header": {"hash": "fixed-hash", "height": 123, "gas_price": "100"}}
        if method == "EXPERIMENTAL_protocol_config":
            return {"protocol_version": 86, "runtime_config": {}}
        kind = params["request_type"]
        result = {"block_hash": "other" if self.wrong_block else "fixed-hash", "block_height": 123}
        if kind == "view_account":
            result.update(self.account)
        elif kind == "view_code":
            result.update(code_base64=b64(self.code), hash=snapshot.code_hash(self.code))
        elif kind == "view_access_key_list":
            result["keys"] = [{"public_key": "ed25519:key", "access_key": {
                "nonce": 8, "permission": {"FunctionCall": {
                    "allowance": None, "receiver_id": "app.near", "method_names": ["go"]}}}}]
        elif kind == "view_state":
            prefix = snapshot.decode(params["prefix_base64"])
            result["values"] = [{"key": b64(k), "value": b64(v)} for k, v in self.data.items()
                                if k.startswith(prefix)]
        else:
            raise AssertionError(kind)
        return deepcopy(result)


class SnapshotTests(unittest.TestCase):
    def setUp(self):
        self.rpc = FakeRPC()

    def capture(self, **kwargs):
        return snapshot.capture(["app.near"], request=self.rpc, **kwargs)

    def test_every_read_uses_one_resolved_block(self):
        result = self.capture(block=123)
        self.assertEqual(self.rpc.calls[0][1], {"block_id": 123})
        for _, params, _ in self.rpc.calls[1:]:
            self.assertEqual(params["block_id"], "fixed-hash")
            self.assertNotIn("finality", params)
        account = result["accounts"][0]
        self.assertTrue(account["storage"]["complete"])
        self.assertEqual(len(account["storage"]["values"]), 3)
        self.assertEqual(account["access_keys"][0]["access_key"]["permission"]["FunctionCall"]["allowance"], None)
        self.assertFalse(result["scope"]["receipt_queues"])

    def test_mixed_blocks_are_rejected(self):
        self.rpc.wrong_block = True
        with self.assertRaisesRegex(ValueError, "different block"):
            self.capture()

    def test_tampered_code_is_rejected(self):
        self.rpc.account["code_hash"] = "wrong"
        with self.assertRaisesRegex(ValueError, "code hash"):
            self.capture()

    def test_prefixes_are_explicit_and_overlaps_deduplicated(self):
        result = self.capture(prefixes=[b"S", b"STATE"])["accounts"][0]["storage"]
        self.assertFalse(result["complete"])
        self.assertEqual(len(result["values"]), 1)
        self.assertEqual(result["prefixes_base64"], [b64(b"S"), b64(b"STATE")])

    def test_full_prefix_subsumes_narrow_prefixes(self):
        result = self.capture(prefixes=[b"", b"S"])["accounts"][0]["storage"]
        self.assertTrue(result["complete"])
        self.assertEqual(result["prefixes_base64"], [""])

    def test_account_without_code(self):
        self.rpc.account["code_hash"] = snapshot.EMPTY_CODE_HASH
        self.assertIsNone(self.capture()["accounts"][0]["code"])
        self.assertFalse(any(params.get("request_type") == "view_code" for _, params, _ in self.rpc.calls))

    def test_global_code_is_not_silently_ignored(self):
        self.rpc.account["global_contract_account_id"] = "global.near"
        with self.assertRaisesRegex(ValueError, "global contract"):
            self.capture()

    def test_rpc_error_propagates_without_partial_fixture(self):
        def fail(method, params, **kwargs):
            if params.get("request_type") == "view_state":
                raise RuntimeError("TOO_LARGE_CONTRACT_STATE")
            return self.rpc(method, params, **kwargs)
        with self.assertRaisesRegex(RuntimeError, "TOO_LARGE"):
            snapshot.capture(["app.near"], request=fail)

    def test_invalid_base64_is_rejected(self):
        with self.assertRaises(ValueError):
            snapshot.decode("!!")

    def test_invalid_account_selection(self):
        for accounts in [[], ["app.near", "app.near"], ["../escape"], ["x"]]:
            with self.assertRaises(ValueError):
                snapshot.capture(accounts, request=self.rpc)

    def test_atomic_file_and_no_overwrite(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "fixture.json"
            result = self.capture()
            snapshot.write_snapshot(path, result)
            self.assertEqual(json.loads(path.read_text()), result)
            with self.assertRaises(FileExistsError):
                snapshot.write_snapshot(path, {"replaced": True})
            self.assertEqual(json.loads(path.read_text()), result)
            self.assertEqual(list(Path(directory).iterdir()), [path])


if __name__ == "__main__":
    unittest.main()
