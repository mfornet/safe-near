"""Fail-closed boundaries of native receipt/state projection."""
import base64
import copy
from pathlib import Path
import sys
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "chain-conformance"))
import compare_fixture as comparator


def action_receipt():
    return dict(receipt_id="r", predecessor_id="alice.near", receiver_id="bob.near", receipt={"Action": {
        "signer_id": "alice.near", "signer_public_key": "ed25519:" + "1" * 32, "gas_price": "0",
        "input_data_ids": [], "output_data_receivers": [], "actions": [{"Transfer": {"deposit": "3"}}]}})


class ChainProjectionTests(unittest.TestCase):
    def test_native_creation_events_are_unique_and_references_require_an_owner(self):
        p = comparator.Projection({})
        self.assertEqual(p.fresh(p.receipt_ids, "r"), 1)
        self.assertEqual(p.fresh(p.data_ids, "d"), 2)
        p.data_owners["d"] = "bob.near"
        self.assertEqual(p.rid("r"), 1)
        self.assertEqual(p.data("d", "bob.near"), 2)
        with self.assertRaises(ValueError):
            p.fresh(p.receipt_ids, "r")
        with self.assertRaises(ValueError):
            p.rid("absent")
        with self.assertRaises(ValueError):
            p.data("d", "other.near")

    def test_nonempty_v2_refund_target_and_unknown_receipt_variants_are_rejected(self):
        r = action_receipt()
        self.assertIsNotNone(comparator.action_payload(r))
        action = r["receipt"].pop("Action")
        r["receipt"]["ActionV2"] = {**action, "refund_to": None}
        self.assertEqual(comparator.action_payload(r), action)
        r["receipt"]["ActionV2"]["refund_to"] = "other.near"
        with self.assertRaises(ValueError):
            comparator.action_payload(r)
        r["receipt"] = {"GlobalContractDistribution": {}}
        with self.assertRaises(ValueError):
            comparator.action_payload(r)

    def test_extra_native_data_fields_and_unfrozen_deployment_are_not_dropped(self):
        p = comparator.Projection({})
        p.fresh(p.receipt_ids, "r")
        p.fresh(p.data_ids, "d")
        p.data_owners["d"] = "bob.near"
        r = action_receipt()
        r["receipt"] = {"Data": {"data_id": "d", "data": "AP8="}}
        self.assertEqual(p.receipt(r)["receipt"]["data"], [0, 255])
        r["receipt"]["Data"]["unknown"] = 4
        with self.assertRaises(ValueError):
            p.receipt(r)
        r = action_receipt()
        r["receipt"]["Action"]["actions"] = [{"DeployContract": {"code": base64.b64encode(b"\0asm\1\0\0\0").decode()}}]
        with self.assertRaisesRegex(ValueError, "frozen code catalogue"):
            p.receipt(r)

    def test_modeled_trie_columns_and_missing_raw_records_cannot_be_silently_omitted(self):
        p = comparator.Projection({})
        for value in [dict(entries=[[[5], []]], decodedRecords=[dict(key=[5], opaque=True)]),
                      dict(entries=[[[0], []]], decodedRecords=[])]:
            with self.assertRaises(ValueError):
                p.state(value)
        with self.assertRaises(ValueError):
            p.status({"Failure": {"ActionError": {"index": True, "kind": {"FunctionCallError": {
                "ExecutionError": "Smart contract panicked: panic"}}}}})
        with self.assertRaises(ValueError):
            p.status({"Failure": {"InvalidTxError": "InvalidSignerId"}})

    def test_action_error_parameters_and_nonzero_indices_are_preserved(self):
        p = comparator.Projection({})
        value = {"Failure": {"ActionError": {"index": 3, "kind": {"DeleteKeyDoesNotExist": {
            "account_id": "bob.near", "public_key": "ed25519:" + "1" * 32}}}}}
        projected = p.status(value)
        self.assertEqual(projected, dict(kind="failure", actionIndex=3,
            error=dict(kind="deleteKeyDoesNotExist", accountId="bob.near", publicKey=[0] * 33)))
        value["Failure"]["ActionError"]["kind"]["DeleteKeyDoesNotExist"]["unknown"] = 1
        with self.assertRaises(ValueError):
            p.status(value)

    def test_restricted_key_error_parameters_are_lossless(self):
        p = comparator.Projection({})
        key = "ed25519:" + "1" * 32
        vectors = [
            ("AccessKeyNotFound", {"account_id": "alice.near", "public_key": key},
                {"accountId": "alice.near", "publicKey": [0] * 33}),
            ("ReceiverMismatch", {"tx_receiver": "bob.near", "ak_receiver": "other.near"},
                {"txReceiver": "bob.near", "keyReceiver": "other.near"}),
            ("MethodNameMismatch", {"method_name": "denied"}, {"methodName": "denied"}),
            ("NotEnoughAllowance", {"account_id": "alice.near", "public_key": key, "allowance": "2", "cost": "3"},
                {"accountId": "alice.near", "publicKey": [0] * 33, "allowance": "2", "cost": "3"}),
        ]
        for reason, parameters, expected in vectors:
            with self.subTest(reason=reason):
                value = {"Failure": {"InvalidTxError": {"InvalidAccessKeyError": {reason: parameters}}}}
                self.assertEqual(p.status(value), dict(kind="failure", actionIndex=None,
                    error=dict(kind="invalidAccessKey", reason=reason, **expected)))
                parameters["unrepresented"] = 1
                with self.assertRaises(ValueError):
                    p.status(value)

    def test_stateless_action_errors_preserve_parameters_and_reject_extras(self):
        projection = comparator.Projection({})
        for variant, parameters in [
            ("TotalPrepaidGasExceeded", {"total_prepaid_gas": 2**64 - 1, "limit": 10**15}),
            ("TotalNumberOfDeployActionsExceeded", {"number_of_deploy_actions": 11, "limit": 10}),
            ("FunctionCallMethodNameLengthExceeded", {"length": 257, "limit": 256}),
            ("InvalidAccountId", {"account_id": "UPPER.near"}),
        ]:
            with self.subTest(variant=variant):
                status = {"Failure": {"InvalidTxError": {"ActionsValidation": {variant: parameters}}}}
                self.assertEqual(projection.status(status), dict(kind="failure", actionIndex=None,
                    error=dict(kind="actionsValidation", error=dict(kind=variant, **parameters))))
                parameters["extra"] = 1
                with self.assertRaises(ValueError):
                    projection.status(status)
        for variant in ["DeleteActionMustBeFinal", "FunctionCallZeroAttachedGas", "IntegerOverflow"]:
            status = {"Failure": {"InvalidTxError": {"ActionsValidation": variant}}}
            self.assertEqual(projection.status(status)["error"],
                dict(kind="actionsValidation", error=dict(kind=variant)))
        with self.assertRaises(ValueError):
            projection.status({"Failure": {"InvalidTxError": {"ActionsValidation": "unknown"}}})

    def test_transaction_size_error_preserves_native_size_and_limit(self):
        projection = comparator.Projection({})
        fields = {"size": 1572865, "limit": 1572864}
        status = {"Failure": {"InvalidTxError": {"TransactionSizeExceeded": fields}}}
        self.assertEqual(projection.status(status), dict(kind="failure", actionIndex=None,
            error=dict(kind="transactionSizeExceeded", **fields)))
        fields["unknown"] = 1
        with self.assertRaises(ValueError):
            projection.status(status)

    def test_unrepresented_function_call_errors_fail_closed(self):
        p = comparator.Projection({})
        for error in [{"CompilationError": {"CodeDoesNotExist": 7}},
                      {"MethodResolveError": {"unexpected": "MethodNotFound"}},
                      {"CompilationError": {"CodeDoesNotExist": {"account_id": "other.near"}}}]:
            with self.subTest(error=error), self.assertRaises(ValueError):
                p.status({"Failure": {"ActionError": {"index": 0, "kind": {"FunctionCallError": error}}}}, "bob.near")

    def test_postponed_indices_cannot_change_the_native_receiver(self):
        p = comparator.Projection({})
        p.fresh(p.receipt_ids, "r")
        p.remember(action_receipt())
        p.fresh(p.data_ids, "d")
        p.data_owners["d"] = "bob.near"
        for record in [{"PendingDataCount": {"receipt_id": "r", "account_id": "alice.near", "count": 1}},
                       {"PostponedReceiptId": {"receipt_id": "r", "account_id": "alice.near", "data_id": "d"}}]:
            with self.assertRaisesRegex(ValueError, "different receiver"):
                p.state(dict(entries=[[[5], []]], decodedRecords=[dict(key=[5], record=record)]))

    def test_empty_storage_map_normalization_preserves_ordered_work(self):
        state = comparator.Projection({}).state(dict(entries=[], decodedRecords=[]))
        state["storage"] = [["alice.near", []], ["bob.near", [[[2], [3]], [[1], [4]]]]]
        value = dict(initialState=state, blocks=[], codeCatalogue=[], initialPendingReceipts=[2, 1])
        before = copy.deepcopy(value)
        actual = comparator.canonical_trace(value)
        self.assertEqual(value, before)
        self.assertEqual(actual["initialState"]["storage"], [["bob.near", [[[1], [4]], [[2], [3]]]]])
        self.assertEqual(actual["initialPendingReceipts"], [2, 1])


if __name__ == "__main__":
    unittest.main()
