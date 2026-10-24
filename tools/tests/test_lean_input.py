"""Bundle -> Lean request conversion and comparison helpers (no neard, no Lean binary)."""
import base64
import hashlib
from pathlib import Path
import sys
import tempfile
import unittest

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parents[0] / "localnet"))
import corpus  # noqa: E402
import lean_input as li  # noqa: E402
import nearcodec as nc  # noqa: E402

KEY = nc.Key.derive("lean-input")
PK = "ed25519:" + nc.b58encode(KEY.public)


def tx_bundle(actions=None, receipts=(), entries=None, shards=1):
    block_hash = bytes(range(32))
    raw = nc.transaction("alice.near", KEY, 5, "bob.near", block_hash, [nc.transfer(7)])
    view = {"signer_id": "alice.near", "receiver_id": "bob.near", "public_key": PK, "nonce": 5,
            "actions": actions or [{"Transfer": {"deposit": "7"}}]}
    return {
        "formatVersion": 1, "meta": {"height": 9, "shardId": 0, "chainId": "safe-near-localnet-1s"},
        "context": {"currentProtocolVersion": 86, "validatorAccountsUpdate": None, "blockHeight": 9,
                    "blockTimestamp": 5, "epochHeight": 1, "gasPrice": "100", "gasLimit": 10**15,
                    "randomSeed": "ab" * 32, "bandwidthRequests": "0100000000000000000000000000000000",
                    "congestionInfo": [[i, "00" * 43, 0] for i in range(shards)]},
        "preState": {"root": "00" * 32, "entries": entries or []},
        "inputs": {"transactions": [{"borsh": raw.hex(), "valid": True, "hash": nc.transaction_hash(raw).hex(), "view": view,
                                     "actions": [{"Transfer": {"deposit": "7"}}]}],
                   "incomingReceipts": [], "incomingReceiptViews": list(receipts),
                   "incomingReceiptTyped": [{"receipt": {"Action": {"actions": [{"Transfer": {"deposit": "3"}}]}}}
                                            for _ in receipts]},
        "expected": {"outcomes": [], "outgoingReceipts": [], "stateDiff": [], "balanceStats": {}},
    }


def decoded(account="alice.near"):
    return {"preState": [
        {"key": "00", "record": {"Account": {"account_id": account, "account": {
            "amount": "1000", "locked": "0", "code_hash": "1" * 32, "storage_usage": 182, "version": "V1"}}}},
        {"key": "02", "record": {"AccessKey": {"account_id": account, "public_key": PK,
                                               "access_key": {"nonce": 0, "permission": "FullAccess"}}}},
        {"key": "0f", "opaque": True}], "postChanged": []}


class Parsing(unittest.TestCase):
    def test_transaction_block_hash(self):
        block_hash = bytes(range(32))
        raw = nc.transaction("alice.near", KEY, 5, "bob.near", block_hash, [nc.transfer(7)])
        self.assertEqual(bytes(li.transaction_block_hash(raw)), block_hash)
        strict = nc.transaction_v1_strict("alice.near", KEY, 5, "bob.near", block_hash, [])
        self.assertEqual(bytes(li.transaction_block_hash(strict)), block_hash)

    def test_receipt_format_tags(self):
        header = nc.string("a.near") + nc.string("b.near") + bytes(32)
        self.assertEqual(li.receipt_format(header + b"\x00" + nc.string("s.near")), ("legacy", False))
        self.assertEqual(li.receipt_format(header + b"\x01"), ("data", False))
        self.assertEqual(li.receipt_format(header + b"\x05" + nc.string("s.near") + b"\x00"), ("v2", False))
        self.assertEqual(li.receipt_format(header + b"\x05" + nc.string("s.near") + b"\x01"), ("v2", True))
        self.assertEqual(li.receipt_format(header + b"\x03")[0], "resume")
        self.assertEqual(li.receipt_format(header + b"\x04")[0], "distribution")
        self.assertEqual(li.receipt_format(header + b"\x09")[0], "tag 9")

    def test_public_keys(self):
        self.assertEqual(li.public_key(PK), [0] + list(KEY.public))
        with self.assertRaises(li.Unsupported):
            li.public_key("mldsa65:abc")


class Blockers(unittest.TestCase):
    def test_a_plain_transfer_has_none(self):
        self.assertEqual(li.blockers(tx_bundle()), [])

    def test_each_unrepresented_feature_is_named(self):
        bundle = tx_bundle(actions=[{"DeterministicStateInit": {}}, "CreateAccount"], shards=4)
        bundle["preState"]["entries"] = [["0a", "00"], ["0f", "00"], ["0d", "00"]]
        bundle["context"]["validatorAccountsUpdate"] = {}
        bundle["inputs"]["transactions"][0]["valid"] = False
        found = li.blockers(bundle)
        for text in ["multi-shard layout", "pre-state column buffered-receipt",
                     "action DeterministicStateInit", "epoch boundary", "transaction rejected"]:
            self.assertTrue(any(text in reason for reason in found), (text, found))
        self.assertFalse(any("bandwidth" in reason for reason in found))      # column 15 is the modelled scheduler
        self.assertEqual(found, list(dict.fromkeys(found)))

    def test_model_actions(self):
        self.assertEqual(li.model_action_blockers(["Transfer", "FunctionCall"]), [])
        self.assertEqual(li.model_action_blockers(["Transfer", "UseGlobalContract", "Delegate", "TransferToGasKey"]), [])
        self.assertEqual(li.model_action_blockers(["Transfer", "DeterministicStateInit"]),
                         ["action DeterministicStateInit"])

    def test_host_functions_that_need_the_epoch(self):
        bundle = tx_bundle()
        bundle["expected"]["outcomes"] = [{"view": {"metadata": {"gas_profile": [
            {"cost_category": "WASM_HOST_COST", "cost": "VALIDATOR_STAKE_BASE", "gas_used": "1"}]}}}]
        self.assertTrue(any("validator_stake" in reason for reason in li.blockers(bundle)))


class Conversion(unittest.TestCase):
    def convert(self, bundle, rows=None):
        with tempfile.TemporaryDirectory() as directory:
            return li.Converter(bundle, rows or decoded(), Path(directory)).build()

    def test_state_transactions_and_context(self):
        bundle = tx_bundle()
        request = self.convert(bundle)
        self.assertEqual(request["initialState"]["accounts"],
                         [["alice.near", {"amount": "1000", "locked": "0", "storageUsage": 182, "codeHash": None,
                           "global": None, "versionTwo": False}]])
        self.assertEqual(request["initialState"]["accessKeys"][0][0], ["alice.near", [0] + list(KEY.public)])
        tx = request["blocks"][0]["transactions"][0]
        self.assertEqual((tx["signerId"], tx["receiverId"], tx["nonce"]), ("alice.near", "bob.near", 5))
        self.assertEqual(tx["actions"], [{"kind": "transfer", "deposit": "7"}])
        self.assertEqual(request["transactionBlockHashes"], [[list(range(32))]])
        self.assertEqual(request["blocks"][0]["randomSeed"], [0xAB] * 32)
        self.assertIsNone(request["blocks"][0]["incomingIndices"])
        self.assertNotIn("initialScheduler", request)

    def test_scheduler_state_is_read_from_column_15(self):
        value = bytes([0]) + (1).to_bytes(4, "little") + bytes(16) + (123).to_bytes(8, "little") + bytes(range(32))
        bundle = tx_bundle(entries=[["0f", value.hex()]])
        self.assertEqual(self.convert(bundle)["initialScheduler"], {"allowance": 123, "sanity": list(range(32))})
        bundle = tx_bundle(entries=[["0f", "00"]])
        with self.assertRaises(li.Unsupported):
            self.convert(bundle)

    def test_incoming_receipts_get_model_identities(self):
        header = nc.string("x.near") + nc.string("alice.near") + bytes(range(32))
        raw = header + b"\x05" + nc.string("x.near") + b"\x00" + bytes(33)
        view = {"predecessor_id": "x.near", "receiver_id": "alice.near", "receipt_id": nc.b58encode(bytes(range(32))),
                "receipt": {"Action": {"signer_id": "x.near", "signer_public_key": PK, "gas_price": "10",
                                       "output_data_receivers": [{"data_id": nc.b58encode(bytes([1]) * 32), "receiver_id": "y.near"}],
                                       "input_data_ids": [nc.b58encode(bytes([2]) * 32)], "is_promise_yield": False,
                                       "actions": [{"Transfer": {"deposit": "3"}}]}}}
        bundle = tx_bundle(receipts=[view])
        bundle["inputs"]["incomingReceipts"] = [raw.hex()]
        request = self.convert(bundle)
        pending = request["pendingReceipts"][0]
        self.assertEqual(pending["receiptId"], 3)       # the two data ids are numbered first: inputs, then outputs
        self.assertEqual(pending["receipt"]["inputDataIds"], [1])
        self.assertEqual(pending["receipt"]["outputDataReceivers"], [[2, "y.near"]])
        context = request["queueContext"]
        self.assertEqual(context["receiptIds"], [[3, list(range(32))]])
        self.assertEqual(context["actionFormats"], [[3, "v2"]])
        self.assertEqual({row["receiverId"] for row in context["dataIds"]}, {"alice.near", "y.near"})
        self.assertEqual(request["initialState"]["nextId"], 4)

    def test_unknown_state_is_reported_not_dropped(self):
        rows = decoded()
        rows["preState"].append({"key": "06", "record": {"PostponedReceipt": {}}})
        with self.assertRaises(li.Unsupported) as caught:
            self.convert(tx_bundle(), rows)
        self.assertIn("PostponedReceipt", caught.exception.reasons[0])
        rows = decoded()
        rows["preState"][0]["record"]["Account"]["account"]["mystery_field"] = 1
        with self.assertRaises(li.Unsupported):
            self.convert(tx_bundle(), rows)

    def test_contract_code_is_catalogued_by_its_hash(self):
        code = b"\0asm\1\0\0\0" + b"x" * 40
        label = nc.b58encode(hashlib.sha256(code).digest())
        rows = decoded()
        rows["preState"][0]["record"]["Account"]["account"]["code_hash"] = label
        rows["preState"].append({"key": "01", "record": {"Contract": {"account_id": "alice.near",
                                                                      "code": base64.b64encode(code).decode()}}})
        with tempfile.TemporaryDirectory() as directory:
            request = li.Converter(tx_bundle(), rows, Path(directory)).build()
            self.assertEqual(request["codes"][0]["hash"], label)
            self.assertEqual(Path(request["codes"][0]["codePath"]).read_bytes(), code)


class Comparison(unittest.TestCase):
    def test_expected_outcomes_projection(self):
        bundle = tx_bundle()
        bundle["expected"]["outcomes"] = [
            {"id": "aa", "view": {"executor_id": "alice.near", "status": {"SuccessReceiptId": nc.b58encode(bytes([7]) * 32)},
                                  "logs": ["l"], "receipt_ids": [nc.b58encode(bytes([7]) * 32)], "gas_burnt": 5,
                                  "tokens_burnt": "50"}},
            {"id": "bb", "view": {"executor_id": "bob.near", "status": {"SuccessValue": base64.b64encode(b"hi").decode()},
                                  "logs": [], "receipt_ids": [], "gas_burnt": 1, "tokens_burnt": "10"}},
            {"id": "cc", "view": {"executor_id": "bob.near", "status": {"Failure": {}}, "logs": [], "receipt_ids": [],
                                  "gas_burnt": 0, "tokens_burnt": "0"}}]
        rows = li.expected_outcomes(bundle)
        self.assertEqual(rows[0]["status"], ["receipt", (bytes([7]) * 32).hex()])
        self.assertEqual(rows[0]["tokensBurnt"], 50)
        self.assertEqual(rows[1]["status"], ["value", list(b"hi")])
        self.assertEqual(rows[2]["status"], ["failure"])

    def test_post_state_and_first_difference(self):
        bundle = tx_bundle(entries=[["0001", "aa"], ["0002", "bb"]])
        bundle["expected"]["stateDiff"] = [["0001", "cc"], ["0002", None], ["0203", "dd"]]
        post = li.expected_post_state(bundle)
        self.assertEqual(post, {bytes([0, 1]): b"\xcc", bytes([2, 3]): b"\xdd"})
        self.assertIsNone(li.first_state_difference(post, dict(post), "post"))
        changed = {**post, bytes([0, 1]): b"\x00"}
        self.assertIn("account value differs", li.first_state_difference(post, changed, "post"))
        self.assertIn("access-key entry missing", li.first_state_difference(post, {bytes([0, 1]): b"\xcc"}, "post"))
        self.assertIn("unexpected", li.first_state_difference(post, {**post, b"\x0a": b""}, "post"))


class Report(unittest.TestCase):
    def test_summary_counts(self):
        import replay_corpus as rc
        rows = [{"status": "pass", "detail": "", "blockers": []},
                {"status": "unsupported", "detail": "a", "blockers": ["a", "b"]},
                {"status": "unsupported", "detail": "a", "blockers": ["a"]},
                {"status": "fail", "detail": "outcomes[0].gasBurnt", "blockers": []}]
        summary = rc.summarize(rows)
        self.assertEqual(summary["byStatus"], {"unsupported": 2, "pass": 1, "fail": 1})
        self.assertEqual(summary["byReason"]["a"], 2)
        self.assertEqual(summary["byBlocker"], {"a": 2, "b": 1})
        self.assertIn("unsupported  2", rc.render(summary))


if __name__ == "__main__":
    unittest.main()
