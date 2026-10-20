#!/usr/bin/env python3
"""Compare imported synthetic chains against pinned trie-backed Runtime::apply.

No mismatching fields are removed. Unsupported projections fail closed. Native
hashes are renamed from native creation events, independently of the Lean trace.
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
    def __init__(self, codes):
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
        table[identifier] = self.next_id
        self.next_id += 1
        return table[identifier]

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

    def status(self, value):
        if list(value) == ["SuccessReceiptId"]:
            return dict(kind="successReceiptId", receiptId=self.rid(value["SuccessReceiptId"]))
        if list(value) == ["SuccessValue"]:
            return dict(kind="successValue", value=list(importer.decode(value["SuccessValue"])))
        # Preserve structured transaction-admission parameters and the exact
        # guest-panic message. Other failure correspondences remain rejected.
        if list(value) == ["Failure"]:
            error = value["Failure"]
            if list(error) == ["InvalidTxError"]:
                failure = error["InvalidTxError"]
                if failure == "InvalidTransactionVersion":
                    text = "Near.RuntimeError.invalidTransactionVersion"
                    return dict(kind="failure", error=text, message=text)
                for native, modeled, fields in [
                    ("InvalidNonce", "invalidNonce", ["tx_nonce", "ak_nonce"]),
                    ("NonceTooLarge", "nonceTooLarge", ["tx_nonce", "upper_bound"]),
                ]:
                    if isinstance(failure, dict) and list(failure) == [native] and set(failure[native]) == set(fields):
                        text = "Near.RuntimeError." + modeled + " " + " ".join(str(failure[native][f]) for f in fields)
                        return dict(kind="failure", error=text, message=text)
            if list(error) == ["ActionError"]:
                error = error["ActionError"]
                if error["index"] == 0 and list(error["kind"]) == ["FunctionCallError"]:
                    call = error["kind"]["FunctionCallError"]
                    prefix = "Smart contract panicked: "
                    if list(call) == ["ExecutionError"] and call["ExecutionError"].startswith(prefix):
                        message = call["ExecutionError"]
                        panic = json.dumps(message[len(prefix):], ensure_ascii=False)
                        return dict(kind="failure", message=message, error="Near.RuntimeError.functionCallError "
                            "(Wasm.Near.FunctionCallError.hostError (Wasm.Near.HostError.guestPanic " + panic + "))")
        raise ValueError(f"unmapped native execution status: {value}")

    def project(self, source, trace, model_request):
        if source["pendingReceipts"] or trace["initialPendingReceiptViews"] or model_request["pendingReceipts"]:
            raise ValueError("imported genesis must have an empty receipt queue")
        initial = self.state(trace["initialState"])
        pending, pending_borsh, blocks = [], [], []
        if trace["stop"] != "blocksExhausted" or trace["unrunBlocks"] or len(source["blocks"]) != len(trace["blocks"]):
            raise ValueError("native execution did not commit every requested block")
        if source["protocolVersion"] != model_request["protocolVersion"] or len(source["blocks"]) != len(model_request["blocks"]):
            raise ValueError("native/model protocol or block count differs")
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
                    actions=[importer.action(a, self.keys, copy.copy(self.codes)) for a in tx["actions"]])
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
            self.creations(block)
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
                    executorId=o["executor_id"], status=self.status(o["status"]), logs=o["logs"],
                    receiptIds=[self.rid(r) for r in o["receipt_ids"]], gasBurnt=o["gas_burnt"], tokensBurnt=o["tokens_burnt"])))
            balance = block["balanceStats"]
            blocks.append(dict(state=self.state(block["state"]), pendingReceipts=[self.receipt(r) for r in pending],
                outgoingReceipts=[self.receipt(r) for r in block["outgoingReceipts"]], outcomes=outcomes, issue=None,
                tokensBurnt=str(sum(int(balance[k]) for k in ["txBurntAmount", "otherBurntAmount", "slashedBurntAmount"])),
                subsidizedAmount=balance["subsidizedAmount"]))
        return dict(formatVersion=1, protocolVersion=source["protocolVersion"], model="near-lean-chain",
            initialState=initial, initialPendingReceipts=[], blocks=blocks, stop="blocksExhausted", unrunBlocks=0,
            quiescent=not pending and not blocks[-1]["state"]["delayed"] and not blocks[-1]["state"]["postponed"] if blocks else True,
            codeCatalogue=[dict(hash=label, size=len(blob)) for label, blob in sorted(self.codes.items())])


def canonical_trace(value):
    value = copy.deepcopy(value)
    for state in [value["initialState"], *[b["state"] for b in value["blocks"]]]:
        for _, entries in state["storage"]:
            entries.sort(key=lambda pair: pair[0])
        # Empty per-account storage and an absent per-account storage map both
        # denote the same empty key/value function in ChainState.contractStorage.
        state["storage"] = [[account, entries] for account, entries in state["storage"] if entries]
        state.update(canonical_state(state))
    value["codeCatalogue"].sort(key=lambda row: row["hash"])
    return value


def compare(directory, reference, model):
    manifest = json.loads((directory / "manifest.json").read_text())
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
        left = importer.execute(native, source, stage)
        right = importer.execute(lean, request, stage)
        try:
            expected = Projection(codes).project(source, left, request)
            diffs = differences(canonical_trace(expected), canonical_trace(right), "trace")
            error = None
        except (ValueError, KeyError, IndexError) as issue:
            expected = None
            error = str(issue)
            diffs = [dict(path="projection", error=error)]
        return dict(scope="synthetic captured-account chain execution; not historical replay or general conformance",
            referenceBuild=build, modelBinarySha256=importer.file_digest(lean), manifest=manifest, fixtureFilesBase64=assets,
            native=left, model=right, expected=expected, projectionError=error, differences=diffs,
            unmodeledObservations=["native compute and execution metadata", "account/receipt representation versions",
                "native shard scheduler columns and delayed queue indices", "native hash generation (event-based renaming)",
                "transaction hash identity (transaction outcome ids map to zero)",
                "statistics beyond represented balance burn/subsidy", "native action failure index (only index-zero guest panic mapped)"])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path)
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay")
    parser.add_argument("--report", type=Path, default=ROOT / "audit/chain-fixture-comparison.json")
    args = parser.parse_args()
    report = compare(args.fixture.resolve(), args.reference.resolve(), args.model.resolve())
    atomic_write(args.report.resolve(), (json.dumps(report, indent=2) + "\n").encode())
    print(f"Chain comparison: {len(report['differences'])} differences; evidence: {args.report.resolve()}")
    if report["projectionError"]:
        print(f"Unsupported projection: {report['projectionError']}")
    raise SystemExit(bool(report["differences"]))


if __name__ == "__main__":
    main()
