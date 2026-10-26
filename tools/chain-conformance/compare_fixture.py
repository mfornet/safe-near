#!/usr/bin/env python3
"""Compare imported synthetic chains against pinned trie-backed Runtime::apply.

No mismatching fields are removed. Unsupported projections fail closed. Native
hashes are renamed from native creation events. Optional independently derived
registries bind logical names while native events still determine allocation
counts; missing, extra, reused and non-contiguous bindings fail closed.
Raw traces, inputs, assets and projection differences remain in the report.
"""
from __future__ import annotations

import argparse
import base64
import copy
import json
from pathlib import Path
import shutil
import tempfile

import import_snapshot as importer
from gas_probe import canonical_state, differences, public_key
from prepare import HERE, ROOT, atomic_write, digest
from probe import frozen_reference


class PublicKeys(dict):
    def __missing__(self, text):
        value = public_key(text)
        self[text] = value
        return value


def action_payload(receipt):
    payload = receipt["receipt"]
    if list(payload) == ["Action"]:
        return payload["Action"]
    if list(payload) == ["ActionV2"]:
        value = payload["ActionV2"]
        if value["refund_to"] is not None:
            raise ValueError("explicit refund_to is not represented by the model")
        return {k: v for k, v in value.items() if k != "refund_to"}
    if list(payload) == ["Data"]:
        return None
    raise ValueError(f"unsupported native receipt variant: {list(payload)}")


class Projection:
    def __init__(self, codes, registries=None):
        self.registries = registries
        self.bound_receipts = self.bound_data = self.bound_owners = None
        self.codes = codes
        self.keys = PublicKeys()
        self.receipts = {}
        self.receipt_ids = {}
        self.data_ids = {}
        self.data_owners = {}
        self.next_id = 1

    def fresh(self, table, identifier):
        if identifier in table:
            raise ValueError(f"duplicate native creation event: {identifier}")
        bound = self.bound_receipts if table is self.receipt_ids else self.bound_data
        if bound is not None and identifier not in bound:
            raise ValueError("native creation has no independently derived identity binding")
        table[identifier] = self.next_id if bound is None else bound[identifier]
        self.next_id += 1
        return table[identifier]

    def bind_registry(self, registry):
        from near_rpc import b58encode
        def bindings(rows):
            result = {}
            for identifier, raw in rows:
                if type(identifier) is not int or identifier <= 0:
                    raise ValueError("invalid registered logical identity")
                if len(raw) != 32 or any(type(byte) is not int or not 0 <= byte < 256 for byte in raw):
                    raise ValueError("invalid registered native identity")
                text = b58encode(bytes(raw))
                if text in result: raise ValueError("duplicate registered native identity")
                result[text] = identifier
            return result
        receipts = bindings(registry["receiptIds"])
        data = bindings([(row["id"], row["hash"]) for row in registry["dataIds"]])
        owners = {b58encode(bytes(row["hash"])): row["receiverId"] for row in registry["dataIds"]}
        values = list(receipts.values()) + list(data.values())
        if len(values) != len(set(values)): raise ValueError("aliased registered logical identity")
        for old, new in [(self.receipt_ids, receipts), (self.data_ids, data), (self.data_owners, owners)]:
            if any(new.get(key) != value for key, value in old.items()):
                raise ValueError("registration rewrote an established native identity")
        self.bound_receipts, self.bound_data, self.bound_owners = receipts, data, owners

    def check_registry(self):
        if (self.receipt_ids != self.bound_receipts or self.data_ids != self.bound_data
                or self.data_owners != self.bound_owners):
            raise ValueError("registered identities differ from actual native creation events")
        # Native creation events determine the count independently of logical
        # names. Two VM calls may interleave receipt/data allocations.
        values = list(self.receipt_ids.values()) + list(self.data_ids.values())
        if sorted(values) != list(range(1, self.next_id)):
            raise ValueError("registered allocation is not contiguous with native creation count")

    def rid(self, identifier):
        if identifier not in self.receipt_ids:
            raise ValueError(f"receipt has no earlier native creation event: {identifier}")
        return self.receipt_ids[identifier]

    def data(self, identifier, owner):
        if identifier not in self.data_ids:
            raise ValueError(f"data has no earlier native dependency event: {identifier}")
        if self.data_owners[identifier] != owner:
            raise ValueError("native data receiver differs from its dependency receiver")
        return self.data_ids[identifier]

    def remember(self, receipt):
        identifier = receipt["receipt_id"]
        if identifier in self.receipts and self.receipts[identifier] != receipt:
            raise ValueError("native receipt changed after creation")
        self.receipts[identifier] = receipt

    def creations(self, block):
        for receipt in block["outgoingReceipts"] + block["processedReceipts"]:
            self.remember(receipt)
        # A signer-is-receiver receipt can be created and delayed without
        # appearing in either outgoing or processed work in this chunk.
        for row in block["state"]["decodedRecords"]:
            for name in ["PostponedReceipt", "DelayedReceipt"]:
                if name in row.get("record", {}):
                    self.remember(row["record"][name])
        outgoing = {r["receipt_id"]: r for r in block["outgoingReceipts"]}
        created = set()
        for row in block["outcomes"]:
            identifiers = row["outcome"]["receipt_ids"]
            if len(identifiers) != len(set(identifiers)):
                raise ValueError("native outcome repeats a receipt creation")
            # VM action receipts are allocated first; dependency ids follow;
            # protocol refunds and final data receipts are emitted afterward.
            promises, refunds = [], []
            for identifier in identifiers:
                receipt = self.receipts[identifier]
                if action_payload(receipt) is None:
                    raise ValueError("native outcome unexpectedly lists a data receipt")
                (refunds if receipt["predecessor_id"] == "system" else promises).append(receipt)
            for receipt in promises:
                self.fresh(self.receipt_ids, receipt["receipt_id"])
                created.add(receipt["receipt_id"])
            for receipt in promises:
                action = action_payload(receipt)
                for identifier in action["input_data_ids"]:
                    if identifier not in self.data_ids:
                        self.fresh(self.data_ids, identifier)
                        self.data_owners[identifier] = receipt["receiver_id"]
            for receipt in promises:
                action = action_payload(receipt)
                for receiver in action["output_data_receivers"]:
                    self.data(receiver["data_id"], receiver["receiver_id"])
            for receipt in refunds:
                self.fresh(self.receipt_ids, receipt["receipt_id"])
                created.add(receipt["receipt_id"])
            parent = self.receipts.get(row["id"])
            if parent is not None:
                action = action_payload(parent)
                if action is None:
                    raise ValueError("data receipt produced an execution outcome")
                outputs = {r["data_id"] for r in action["output_data_receivers"]}
                for receipt in block["outgoingReceipts"]:
                    payload = receipt["receipt"].get("Data")
                    if payload is not None and payload["data_id"] in outputs:
                        self.fresh(self.receipt_ids, receipt["receipt_id"])
                        created.add(receipt["receipt_id"])
        if set(outgoing) - created:
            raise ValueError("native outgoing work has no matching outcome/dependency creation event")

    def receipt(self, value):
        action = action_payload(value)
        if action is None:
            d = value["receipt"]["Data"]
            if set(d) != {"data_id", "data"}:
                raise ValueError("unknown native data receipt fields")
            payload = dict(kind="data", dataId=self.data(d["data_id"], value["receiver_id"]),
                           data=None if d["data"] is None else list(importer.decode(d["data"])))
        else:
            expected = {"signer_id", "signer_public_key", "gas_price", "input_data_ids", "output_data_receivers", "actions"}
            if set(action) != expected:
                raise ValueError("unknown native action receipt fields")
            codes = copy.copy(self.codes)
            actions = [importer.action(a, self.keys, codes) for a in action["actions"]]
            if codes != self.codes:
                raise ValueError("native deployment is absent from the frozen code catalogue")
            payload = dict(kind="action", signerId=action["signer_id"], signerPublicKey=self.keys[action["signer_public_key"]],
                gasPrice=action["gas_price"], inputDataIds=[self.data(d, value["receiver_id"]) for d in action["input_data_ids"]],
                outputDataReceivers=[[self.data(d["data_id"], d["receiver_id"]), d["receiver_id"]] for d in action["output_data_receivers"]], actions=actions)
        return dict(predecessorId=value["predecessor_id"], receiverId=value["receiver_id"],
                    receiptId=self.rid(value["receipt_id"]), receipt=payload)

    def state(self, value):
        basic, queues = [], []
        if {tuple(row["key"]) for row in value["decodedRecords"]} != {tuple(key) for key, _ in value["entries"]}:
            raise ValueError("decoded records do not cover the complete raw trie")
        for row in value["decodedRecords"]:
            if row.get("opaque"):
                # These raw columns have no model field (scheduler state and
                # delayed-queue indices). Known modeled columns must decode.
                if row["key"][0] <= 6 or "decodeError" in row:
                    raise ValueError("opaque modeled trie column")
                continue
            if "decodeError" in row:
                raise ValueError("undecodable native trie record")
            if len(row["record"]) != 1:
                raise ValueError("ambiguous native trie record")
            kind = next(iter(row["record"]))
            if kind in {"Account", "AccessKey", "Data", "Contract"}:
                basic.append(dict(key=row["key"], record=row["record"]))
            else:
                queues.append(row)
        result = importer.initial_state({"initialState": {"decodedRecords": basic}}, self.keys, self.codes)
        result["nextId"] = self.next_id
        delayed = []
        for row in queues:
            kind, value = next(iter(row["record"].items()))
            if kind == "PostponedReceipt":
                result["postponed"].append([self.rid(value["receipt_id"]), self.receipt(value)])
            elif kind == "PendingDataCount":
                if self.receipts[value["receipt_id"]]["receiver_id"] != value["account_id"]:
                    raise ValueError("postponed count is stored under a different receiver")
                result["pendingDataCount"].append([self.rid(value["receipt_id"]), value["count"]])
            elif kind == "PostponedReceiptId":
                if self.receipts[value["receipt_id"]]["receiver_id"] != value["account_id"]:
                    raise ValueError("postponed dependency is stored under a different receiver")
                result["postponedByData"].append([self.data(value["data_id"], value["account_id"]), self.rid(value["receipt_id"])])
            elif kind == "ReceivedData":
                result["receivedData"].append([self.data(value["data_id"], value["account_id"]),
                    None if value["data"] is None else list(importer.decode(value["data"]))])
            elif kind == "DelayedReceipt":
                delayed.append((row["queueIndex"], self.receipt(value)))
            else:
                raise ValueError(f"unsupported native state record: {kind}")
        if len({index for index, _ in delayed}) != len(delayed):
            raise ValueError("duplicate delayed queue index")
        result["delayed"] = [receipt for _, receipt in sorted(delayed)]
        for entries in result["storage"]:
            entries[1].sort(key=lambda pair: pair[0])
        return canonical_state(result)

    def status(self, value, executor=None):
        if list(value) == ["SuccessReceiptId"]:
            return dict(kind="successReceiptId", receiptId=self.rid(value["SuccessReceiptId"]))
        if list(value) == ["SuccessValue"]:
            return dict(kind="successValue", value=list(importer.decode(value["SuccessValue"])))
        if list(value) != ["Failure"] or not isinstance(value["Failure"], dict):
            raise ValueError(f"unmapped native execution status: {value}")
        failure = value["Failure"]
        index, context = None, None
        if list(failure) == ["ActionError"]:
            error = failure["ActionError"]
            if set(error) != {"index", "kind"}:
                raise ValueError("unknown native action error fields")
            index = error["index"]
            if index is not None and (type(index) is not int or not 0 <= index < 2**64):
                raise ValueError("invalid native failed-action index")
            context, error = "action", error["kind"]
        elif list(failure) == ["InvalidTxError"]:
            context, error = "transaction", failure["InvalidTxError"]
        else:
            raise ValueError(f"unmapped native execution status: {value}")
        details = None
        if context == "transaction" and error == "InvalidTransactionVersion":
            details = dict(kind="invalidTransactionVersion")
        fields = {
            "action": {
                "AccountAlreadyExists": ("accountAlreadyExists", {"account_id": "accountId"}),
                "AccountDoesNotExist": ("accountDoesNotExist", {"account_id": "accountId"}),
                "CreateAccountNotAllowed": ("createAccountNotAllowed", {"account_id": "accountId", "predecessor_id": "predecessorId"}),
                "CreateAccountOnlyByRegistrar": ("createAccountOnlyByRegistrar", {"account_id": "accountId", "registrar_account_id": "registrarId", "predecessor_id": "predecessorId"}),
                "ActorNoPermission": ("actorNoPermission", {"account_id": "accountId", "actor_id": "actorId"}),
                "DeleteKeyDoesNotExist": ("deleteKeyDoesNotExist", {"account_id": "accountId", "public_key": "publicKey"}),
                "AddKeyAlreadyExists": ("addKeyAlreadyExists", {"account_id": "accountId", "public_key": "publicKey"}),
                "DeleteAccountStaking": ("deleteAccountStaking", {"account_id": "accountId"}),
                "LackBalanceForState": ("lackBalanceForState", {"account_id": "accountId", "amount": "amount"}),
                "TriesToUnstake": ("triesToUnstake", {"account_id": "accountId"}),
                "TriesToStake": ("triesToStake", {"account_id": "accountId", "stake": "stake", "locked": "locked", "balance": "balance"}),
                "OnlyImplicitAccountCreationAllowed": ("onlyImplicitAccountCreationAllowed", {"account_id": "accountId"}),
                "DeleteAccountWithLargeState": ("deleteAccountWithLargeState", {"account_id": "accountId"}),
            },
            "transaction": {
                "InvalidNonce": ("invalidNonce", {"tx_nonce": "nonce", "ak_nonce": "currentNonce"}),
                "TransactionSizeExceeded": ("transactionSizeExceeded", {"size": "size", "limit": "limit"}),
                "NonceTooLarge": ("nonceTooLarge", {"tx_nonce": "nonce", "upper_bound": "upperBound"}),
                "SignerDoesNotExist": ("invalidSigner", {"signer_id": "accountId"}),
                "InvalidReceiverId": ("invalidReceiver", {"receiver_id": "accountId"}),
                "NotEnoughBalance": ("notEnoughBalance", {"signer_id": "accountId", "balance": "balance", "cost": "cost"}),
                "LackBalanceForState": ("lackBalanceForState", {"signer_id": "accountId", "amount": "amount"}),
            },
        }[context]
        if isinstance(error, dict) and len(error) == 1:
            native, data = next(iter(error.items()))
            if native in fields:
                modeled, names = fields[native]
                if not isinstance(data, dict) or set(data) != set(names):
                    raise ValueError(f"unrepresented native error parameters: {native}")
                details = {"kind": modeled, **{name: self.keys[data[key]] if key == "public_key" else data[key]
                    for key, name in names.items()}}
            elif context == "action" and native == "FunctionCallError":
                if not isinstance(data, dict) or len(data) != 1:
                    raise ValueError("unknown native function-call error shape")
                category, payload = next(iter(data.items()))
                if category == "ExecutionError" and isinstance(payload, str):
                    details = dict(kind="functionCallError", error=dict(kind="executionError", message=payload))
                elif category == "MethodResolveError" and isinstance(payload, str) and payload in {"MethodNotFound", "MethodEmptyName", "MethodInvalidSignature"}:
                    details = dict(kind="functionCallError", error=dict(kind="methodResolveError", error=payload))
                elif category == "CompilationError" and isinstance(payload, dict) and list(payload) == ["PrepareError"] \
                        and isinstance(payload["PrepareError"], str):
                    details = dict(kind="functionCallError", error=dict(kind="compilationError", prepareError=payload["PrepareError"]))
                elif category == "CompilationError" and isinstance(payload, dict) and list(payload) == ["CodeDoesNotExist"]:
                    account = payload["CodeDoesNotExist"]
                    if isinstance(account, dict) and set(account) == {"account_id"} and account["account_id"] == executor:
                        details = dict(kind="functionCallError", error=dict(kind="compilationError", message="CodeDoesNotExist", accountId=executor))
            elif context == "transaction" and native == "ActionsValidation":
                unit_errors = {"DeleteActionMustBeFinal", "FunctionCallZeroAttachedGas", "IntegerOverflow"}
                parameters = {
                    "TotalPrepaidGasExceeded": {"total_prepaid_gas", "limit"},
                    "TotalNumberOfActionsExceeded": {"total_number_of_actions", "limit"},
                    "TotalNumberOfDeployActionsExceeded": {"number_of_deploy_actions", "limit"},
                    "AddKeyMethodNamesNumberOfBytesExceeded": {"total_number_of_bytes", "limit"},
                    "AddKeyMethodNameLengthExceeded": {"length", "limit"},
                    "UnsuitableStakingKey": {"public_key"},
                    "InvalidAccountId": {"account_id"}, "ContractSizeExceeded": {"size", "limit"},
                    "FunctionCallMethodNameLengthExceeded": {"length", "limit"},
                    "FunctionCallArgumentsLengthExceeded": {"length", "limit"},
                }
                if isinstance(data, str) and data in unit_errors:
                    details = dict(kind="actionsValidation", error=dict(kind=data))
                elif isinstance(data, dict) and len(data) == 1:
                    variant, fields = next(iter(data.items()))
                    if variant in parameters and isinstance(fields, dict) and set(fields) == parameters[variant]:
                        details = dict(kind="actionsValidation", error=dict(kind=variant, **{
                            key: self.keys[value] if key == "public_key" else value for key, value in fields.items()}))
            elif context == "transaction" and native == "InvalidAccessKeyError":
                if data in ["RequiresFullAccess", "DepositWithFunctionCall"]:
                    details = dict(kind="invalidAccessKey", reason=data)
                elif isinstance(data, dict) and len(data) == 1:
                    reason, parameters = next(iter(data.items()))
                    names = {
                        "AccessKeyNotFound": {"account_id": "accountId", "public_key": "publicKey"},
                        "ReceiverMismatch": {"tx_receiver": "txReceiver", "ak_receiver": "keyReceiver"},
                        "MethodNameMismatch": {"method_name": "methodName"},
                        "NotEnoughAllowance": {"account_id": "accountId", "public_key": "publicKey", "allowance": "allowance", "cost": "cost"},
                    }.get(reason)
                    if names is not None and isinstance(parameters, dict) and set(parameters) == set(names):
                        details = dict(kind="invalidAccessKey", reason=reason, **{name:
                            self.keys[parameters[key]] if key == "public_key" else parameters[key]
                            for key, name in names.items()})
        if details is None:
            raise ValueError(f"unmapped native execution status: {value}")
        return dict(kind="failure", error=details, actionIndex=index)

    def project(self, source, trace, model_request):
        if source["pendingReceipts"] or trace["initialPendingReceiptViews"] or model_request["pendingReceipts"]:
            raise ValueError("imported genesis must have an empty receipt queue")
        initial = self.state(trace["initialState"])
        pending, pending_borsh, blocks = [], [], []
        if trace["stop"] != "blocksExhausted" or trace["unrunBlocks"] or len(source["blocks"]) != len(trace["blocks"]):
            raise ValueError("native execution did not commit every requested block")
        if source["protocolVersion"] != model_request["protocolVersion"] or len(source["blocks"]) != len(model_request["blocks"]):
            raise ValueError("native/model protocol or block count differs")
        if self.registries is not None and len(self.registries) != len(trace["blocks"]):
            raise ValueError("identity registry block count mismatch")
        for header, block, modeled in zip(source["blocks"], trace["blocks"], model_request["blocks"]):
            for field in ["blockHeight", "blockTimestamp", "epochHeight", "gasPrice", "gasLimit", "randomSeed", "incomingIndices"]:
                if differences(header[field], modeled[field]):
                    raise ValueError(f"native/model block context differs: {field}")
            if [r["borsh"] for r in block["inputs"]["transactions"]] != header["transactions"]:
                raise ValueError("decoded native transactions do not bind the signed request")
            converted = []
            for row in block["inputs"]["transactions"]:
                if row["version"] not in {0, 1}:
                    raise ValueError("unsupported native transaction envelope tag")
                tx = row["view"]
                if tx.get("nonce_index") is not None:
                    raise ValueError("gas-key nonce lanes are not represented by the model")
                value = dict(signerId=tx["signer_id"], receiverId=tx["receiver_id"],
                    nonce=tx["nonce"], publicKey=self.keys[tx["public_key"]],
                    actions=[importer.action(a, self.keys, copy.copy(self.codes)) for a in row["actions"]])
                if row["version"] == 1:
                    mode = tx.get("nonce_mode", "monotonic")
                    if mode not in {"monotonic", "strict"}:
                        raise ValueError("unknown native nonce mode")
                    value.update(version=1, nonceMode=mode)
                elif "nonce_mode" in tx:
                    raise ValueError("V0 transactions have no explicit nonce mode")
                converted.append(value)
            def explicit_envelope(tx):
                return {**tx, "version": tx.get("version", 0), "nonceMode": tx.get("nonceMode", "monotonic")}
            if differences([explicit_envelope(tx) for tx in converted],
                           [explicit_envelope(tx) for tx in modeled["transactions"]]):
                raise ValueError("model transactions differ from native signed input views")
            if self.registries is not None: self.bind_registry(self.registries[len(blocks)])
            self.creations(block)
            if self.registries is not None: self.check_registry()
            positions = header["incomingIndices"]
            positions = list(range(len(pending))) if positions is None else positions
            if [pending[i] for i in positions] != block["inputs"]["incomingReceipts"]:
                raise ValueError("native delivery differs from the selected pending frontier")
            pending = [r for i, r in enumerate(pending) if i not in positions] + block["outgoingReceipts"]
            pending_borsh = [r for i, r in enumerate(pending_borsh) if i not in positions] + block["outgoingReceiptBorsh"]
            if pending_borsh != block["pendingReceipts"]:
                raise ValueError("native pending Borsh differs from its exported frontier")
            tx_hashes = {r["view"]["hash"] for r in block["inputs"]["transactions"]}
            outcomes = []
            for row in block["outcomes"]:
                o = row["outcome"]
                outcomes.append(dict(id=0 if row["id"] in tx_hashes else self.rid(row["id"]), outcome=dict(
                    executorId=o["executor_id"], status=self.status(o["status"], o["executor_id"]), logs=o["logs"],
                    receiptIds=[self.rid(r) for r in o["receipt_ids"]], gasBurnt=o["gas_burnt"], tokensBurnt=o["tokens_burnt"])))
            balance = block["balanceStats"]
            blocks.append(dict(transactionSizes=[{field: row[field] for field in ["bodySize", "wireSize", "sizeForLimits"]}
                for row in block["inputs"]["transactions"]], state=self.state(block["state"]), pendingReceipts=[self.receipt(r) for r in pending],
                outgoingReceipts=[self.receipt(r) for r in block["outgoingReceipts"]], outcomes=outcomes, issue=None,
                tokensBurnt=str(sum(int(balance[k]) for k in ["txBurntAmount", "otherBurntAmount", "slashedBurntAmount"])),
                subsidizedAmount=balance["subsidizedAmount"]))
        return dict(formatVersion=1, protocolVersion=source["protocolVersion"], model="near-lean-chain",
            initialState=initial, initialPendingReceipts=[], blocks=blocks, stop="blocksExhausted", unrunBlocks=0,
            quiescent=not pending and not blocks[-1]["state"]["delayed"] and not blocks[-1]["state"]["postponed"] if blocks else True,
            codeCatalogue=[dict(hash=label, size=len(blob)) for label, blob in sorted(self.codes.items())])


def canonical_trace(value, *, model_output=False):
    value = copy.deepcopy(value)
    for state in [value["initialState"], *[b["state"] for b in value["blocks"]]]:
        for _, entries in state["storage"]:
            entries.sort(key=lambda pair: pair[0])
        # Empty per-account storage and an absent per-account storage map both
        # denote the same empty key/value function in ChainState.contractStorage.
        state["storage"] = [[account, entries] for account, entries in state["storage"] if entries]
        state.update(canonical_state(state))
    for block in value["blocks"]:
        for row in block.get("outcomes", []):
            status = row["outcome"]["status"]
            if status["kind"] == "failure" and (model_output or "details" in status):
                if set(status) != {"kind", "error", "message", "details", "actionIndex"}:
                    raise ValueError("model failure must include structured details and action index")
                if not isinstance(status["error"], str) or not isinstance(status["message"], str) or not isinstance(status["details"], dict):
                    raise ValueError("malformed model diagnostic or semantic error fields")
                row["outcome"]["status"] = dict(kind="failure", error=status["details"], actionIndex=status["actionIndex"])
    value["codeCatalogue"].sort(key=lambda row: row["hash"])
    return value


def _input_shape(request):
    value = copy.deepcopy(request)
    for block in value["blocks"]:
        for tx in block["transactions"]:
            tx.setdefault("version", 0); tx.setdefault("nonceMode", "monotonic")
    return json.dumps(value, sort_keys=True, separators=(",", ":"))


def validate_registered_request(direct, registered, source=None):
    base = {key: value for key, value in registered.items() if key not in {"transactionBlockHashes", "schedulerInputs"}}
    if _input_shape(base) != _input_shape(direct):
        raise ValueError("model transactions differ or registered request diverges from direct fixture inputs")
    if source is not None:
        original = [{key: block[key] for key in ["congestionInfo", "bandwidthRequests"]} for block in source["blocks"]]
        if registered.get("schedulerInputs") != original:
            raise ValueError("scheduler inputs differ from original block context")
    hashes = registered["transactionBlockHashes"]
    if len(hashes) != len(direct["blocks"]) or any(len(batch) != len(block["transactions"]) for batch, block in zip(hashes, direct["blocks"])):
        raise ValueError("registered transaction block-hash counts differ from original inputs")


def registered_shape(trace):
    if trace.get("nativeActionRandomness") is not True:
        raise ValueError("registered executor did not enable native action randomness")
    fields = ["formatVersion", "protocolVersion", "model", "initialState", "initialPendingReceipts", "codeCatalogue", "stop", "unrunBlocks", "quiescent"]
    result = {name: trace[name] for name in fields}
    result["blocks"] = [row["execution"] for row in trace["blocks"]]
    return result


def registered_differences(native, registered):
    from near_rpc import b58encode
    def hash_text(raw):
        if not isinstance(raw, list) or len(raw) != 32 or any(type(byte) is not int or not 0 <= byte < 256 for byte in raw):
            raise ValueError("invalid registered transaction hash")
        return b58encode(bytes(raw))
    def records(expected, actual, path, *, complete=False):
        return differences(importer.canonical_entries(expected, complete=complete), importer.canonical_entries(actual, complete=complete), path)
    diffs = records(importer.represented_entries(native["initialState"]["entries"]), registered["initialEntries"], "initialEntries")
    if registered["stop"] != "blocksExhausted" or registered["unrunBlocks"] or len(registered["blocks"]) != len(native["blocks"]):
        raise ValueError("registered replay did not commit every requested block")
    for index, (left, right) in enumerate(zip(native["blocks"], registered["blocks"])):
        prefix = f"blocks[{index}]"
        before = native["initialState"] if index == 0 else native["blocks"][index - 1]["state"]
        diffs += differences(before["root"], right["chunkBaseRoot"], prefix + ".chunkBaseRoot")
        if right.get("admissionCommitted") is not True: raise ValueError("registered transaction admission was not committed")
        diffs += differences([row["receiptId"] for row in right["execution"]["outgoingReceipts"]],
            [row["id"] for row in right["outgoingBytes"]], prefix + ".outgoingByteIdentities")
        diffs += differences(left["outgoingReceiptBorsh"], [row["bytes"] for row in right["outgoingBytes"]], prefix + ".outgoingReceiptBorsh")
        diffs += records(importer.represented_entries(left["state"]["entries"]), right["stateEntries"], prefix + ".stateEntries")
        diffs += records(left["state"]["entries"], right["chunkEntries"], prefix + ".chunkEntries", complete=True)
        queue = [row for row in left["state"]["entries"] if row[0][0] in [3, 4, 5, 6, 7]]
        diffs += records(queue, right["queueEntries"], prefix + ".queueEntries")
        bindings = {logical: hash_text(raw) for logical, raw in right["registry"]["receiptIds"]}
        attempts = right["transactionIdentities"]
        if len(attempts) != len(left["inputs"]["transactions"]): raise ValueError("registered transaction identity count mismatch")
        for position, (original, attempt) in enumerate(zip(left["inputs"]["transactions"], attempts)):
            success = left["outcomes"][position]["outcome"]["status"].get("SuccessReceiptId")
            expected = dict(index=position, bodySize=original["bodySize"], hash=original["view"]["hash"],
                receiptPresent=success is not None, receiptHash=success, receiptBinding=success)
            actual = dict(index=attempt["index"], bodySize=attempt["bodySize"], hash=hash_text(attempt["hash"]),
                receiptPresent=attempt["receiptId"] is not None,
                receiptHash=None if attempt["receiptHash"] is None else hash_text(attempt["receiptHash"]),
                receiptBinding=None if attempt["receiptId"] is None else bindings.get(attempt["receiptId"]))
            diffs += differences(expected, actual, prefix + f".transactionIdentities[{position}]")
    return diffs


def compare(directory, reference, model, *, registered_model=None, legacy=False):
    manifest = json.loads((directory / "manifest.json").read_text())
    registered_model = importer.REGISTERED_MODEL if registered_model is None else Path(registered_model)
    if manifest["format"] != "safe-near-chain-fixture-v1" or not manifest["genesisProjectionMatches"]:
        raise ValueError("expected a validated captured-account chain fixture")
    with frozen_reference(reference) as (native, build), tempfile.TemporaryDirectory(prefix="safe-near-chain-compare-") as temporary:
        stage = Path(temporary) / "fixture"
        stage.mkdir()
        assets = {}
        for name, checksum in manifest["files"].items():
            path = Path(name)
            if path.is_absolute() or ".." in path.parts:
                raise ValueError("fixture manifest path escapes its root")
            contents = (directory / path).read_bytes()
            if digest(contents) != checksum:
                raise ValueError(f"fixture asset hash mismatch: {name}")
            target = stage / path
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(contents)
            assets[name] = base64.b64encode(contents).decode()
        lean = Path(temporary) / "chain-replay"
        shutil.copy2(model, lean)
        if importer.file_digest(lean) != manifest["modelBinarySha256"] or build != manifest["referenceBuild"]:
            raise ValueError("executor provenance changed since fixture import; re-import with these executors")
        registered = None
        if not legacy:
            if not manifest.get("representedGenesisBytesMatch") or "registeredModelBinarySha256" not in manifest:
                raise ValueError("fixture lacks registered executor provenance; re-import it")
            registered = Path(temporary) / "registered-replay"
            shutil.copy2(registered_model, registered)
            if importer.file_digest(registered) != manifest["registeredModelBinarySha256"]:
                raise ValueError("registered executor provenance changed since fixture import; re-import it")
        source = json.loads((stage / "native.json").read_text())
        request = json.loads((stage / "model.json").read_text())
        if request["configDir"] != "configs":
            raise ValueError("expected frozen relative configuration directory")
        codes = {}
        for code in request["codes"]:
            for field in ("codePath", "watPath"):
                if code[field] not in assets:
                    raise ValueError("code asset is outside the manifest")
            blob = (stage / code["codePath"]).read_bytes()
            if importer.code_hash(blob) != code["hash"]:
                raise ValueError("frozen code label does not match bytes")
            codes[code["hash"]] = blob
        registered_request = None if legacy else json.loads((stage / "registered.json").read_text())
        left = importer.execute(native, source, stage)
        raw = importer.execute(lean if legacy else registered, request if legacy else registered_request, stage)
        right, expected, diffs, error = raw, None, [], None
        try:
            right = raw if legacy else registered_shape(raw)
            if not legacy: validate_registered_request(request, registered_request, source)
            if not legacy: diffs += registered_differences(left, raw)
            registries = None if legacy else [row["registry"] for row in raw["blocks"]]
            expected = Projection(codes, registries=registries).project(source, left, request)
            diffs += differences(canonical_trace(expected), canonical_trace(right, model_output=True), "trace")
        except (ValueError, KeyError, IndexError) as issue:
            error = str(issue)
            diffs.append(dict(path="projection", error=error))
        return dict(scope="synthetic captured-account chain execution; not historical replay or general conformance",
            referenceBuild=build, modelBinarySha256=importer.file_digest(lean if legacy else registered),
            directModelBinarySha256=importer.file_digest(lean), executionMode="legacy-event-projection" if legacy else "registered",
            registered=None if legacy else raw, manifest=manifest, fixtureFilesBase64=assets,
            native=left, model=right, expected=expected, projectionError=error, differences=diffs,
            unmodeledObservations=["native compute and execution metadata", "unsupported shard/yield/buffer features",
                "original shard roots and complete raw shard capture", "statistics beyond represented balance burn/subsidy",
                "model diagnostic repr/message formatting (structured semantic errors and action indices are compared)"] +
                (["native hash generation (event-based renaming)", "transaction hash identity", "raw state/receipt bytes and delayed queue indices"] if legacy else []))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path)
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay", help="direct frontend pinned at import; registered execution is the default")
    parser.add_argument("--registered-model", type=Path, default=importer.REGISTERED_MODEL)
    parser.add_argument("--legacy-event-projection", action="store_true", help="explicit direct-seed diagnostic; no automatic fallback")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/chain-fixture-comparison.json")
    args = parser.parse_args()
    report = compare(args.fixture.resolve(), args.reference.resolve(), args.model.resolve(),
        registered_model=args.registered_model.resolve(), legacy=args.legacy_event_projection)
    atomic_write(args.report.resolve(), (json.dumps(report, indent=2) + "\n").encode())
    print(f"Chain comparison: {len(report['differences'])} differences; evidence: {args.report.resolve()}")
    if report["projectionError"]:
        print(f"Unsupported projection: {report['projectionError']}")
    raise SystemExit(bool(report["differences"]))


if __name__ == "__main__":
    main()
