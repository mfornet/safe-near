#!/usr/bin/env python3
"""Typed queue columns, persisted wrappers, canonical roots and runtime states."""
import copy
import json
from pathlib import Path
import random
import subprocess
import tempfile
import unittest

import contract_probe
import import_snapshot as importer
from near_rpc import b58encode
from prepare import ROOT, atomic_write
from probe import frozen_reference
from test_receipt_encoding import CHAIN, MODEL as IDENTITIES, native_source as receipt_source, source as receipt_request
from test_receipt_encoding import cases as receipt_cases
from test_replay import empty_state, action_receipt, receipt
from test_state_encoding import MODEL, entries, native_source as account_source
from trie_probe import REFERENCE, frozen_model


def source(protocol=86):
    return dict(formatVersion=1, codes=[], initialState=empty_state(),
        runtimeConfig=dict(configDir=str(ROOT / "near-lean/vm/configs"), protocolVersion=protocol),
        queueContext=dict(receiptIds=[], dataIds=[], actionFormats=[], delayed=None))


def rich(protocol=86):
    value = source(protocol)
    state, context = value["initialState"], value["queueContext"]
    context["receiptIds"] = [[id, [id] * 32] for id in range(20, 25)]
    context["dataIds"] = [dict(id=40, hash=[40] * 32, receiverId="bob.near"),
        dict(id=41, hash=[41] * 32, receiverId="alice.near")]
    context["actionFormats"] = [[id, "v2" if id % 2 == 0 else "legacy"] for id in range(20, 25)]
    state["postponed"] = [[20, action_receipt([])]]
    state["pendingDataCount"] = [[20, 1]]
    state["postponedByData"] = [[40, 20]]
    state["receivedData"] = [[41, []]]
    for id in range(21, 25):
        row = action_receipt([dict(kind="transfer", deposit="123")], id)
        row["receipt"]["inputDataIds"] = []
        row["receipt"]["outputDataReceivers"] = []
        state["delayed"].append(row)
    context["delayed"] = dict(firstIndex=17, forms=[dict(kind="receipt"),
        dict(kind="storedV0", gas=2**64 - 1, size=0), dict(kind="storedV1", gas=0, size=2**64 - 1), dict(kind="newStored")])
    return dict(formatVersion=1, codes=[], initialState=state,
        runtimeConfig=dict(configDir=str(ROOT / "near-lean/vm/configs"), protocolVersion=protocol), queueContext=context)


def native_source(request):
    """Project original logical values/explicit context into native typed inputs."""
    state, context = request["initialState"], request["queueContext"]
    rs, formats = dict(context["receiptIds"]), dict(context["actionFormats"])
    ds = {row["id"]: row for row in context["dataIds"]}
    def native_receipt(value):
        transport = receipt_request()
        transport.update(codes=request["codes"], receipts=[value], actionFormats=[formats[value["receiptId"]]])
        result = receipt_source(transport)["receipts"][0]
        result["receipt_id"] = b58encode(bytes(rs[value["receiptId"]]))
        if "Data" in result["receipt"]:
            payload = result["receipt"]["Data"]
            payload["data_id"] = b58encode(bytes(ds[payload["data_id"]]["hash"]))
        else:
            payload = next(iter(result["receipt"].values()))
            for output in payload["output_data_receivers"]:
                output["data_id"] = b58encode(bytes(ds[output["data_id"]]["hash"]))
            payload["input_data_ids"] = [b58encode(bytes(ds[id]["hash"])) for id in payload["input_data_ids"]]
        return result
    postponed = dict(state["postponed"])
    delayed = context["delayed"]
    return dict(protocolVersion=request["runtimeConfig"]["protocolVersion"],
        postponed=[native_receipt(row) for _, row in state["postponed"]],
        pendingDataCount=[dict(receiverId=postponed[id]["receiverId"], receiptId=rs[id], count=count) for id, count in state["pendingDataCount"]],
        postponedByData=[dict(receiverId=ds[data]["receiverId"], dataId=ds[data]["hash"], receiptId=rs[id]) for data, id in state["postponedByData"]],
        receivedData=[dict(receiverId=ds[id]["receiverId"], dataId=ds[id]["hash"], data=data) for id, data in state["receivedData"]],
        delayed=None if delayed is None else dict(firstIndex=delayed["firstIndex"], receipts=[
            dict(receipt=native_receipt(row), storage=form) for row, form in zip(state["delayed"], delayed["forms"])]))


def cases():
    yield "absent-queue-header", source()
    for first in [0, 17, 2**64 - 1]:
        value = source(); value["queueContext"]["delayed"] = dict(firstIndex=first, forms=[])
        yield f"empty-persistent-queue-{first}", value
    for protocol in [83, 84, 85, 86]:
        yield f"all-queue-columns-{protocol}", rich(protocol)
        value = rich(protocol)
        value["initialState"]["pendingDataCount"] = [[20, 2**32 - 1]]
        value["initialState"]["receivedData"] = [[41, None]]
        yield f"stored-values-preserved-{protocol}", value
        for payload in [None, [], [0, 255, 44]]:
            value = rich(protocol)
            for row in value["initialState"]["delayed"]:
                row["receipt"] = dict(kind="data", dataId=40, data=payload)
            value["queueContext"]["actionFormats"] = [[id, "v2" if id == 20 else "legacy"] for id in range(20, 25)]
            yield f"delayed-data-{protocol}-{payload}", value
        for receiver in ["bob.near", "a" * 64, "0x" + "a" * 40, "0s" + "a" * 40, "0x" + "g" * 40, "0s" + "g" * 40]:
            value = rich(protocol)
            _, actions = next(receipt_cases())
            value["codes"] = actions["codes"]
            row = actions["receipts"][0]
            row.update(receiptId=21, receiverId=receiver)
            row["receipt"].update(inputDataIds=[], outputDataReceivers=[])
            for action in row["receipt"]["actions"]:
                if action["kind"] == "functionCall": action["gas"] = 120 * 10**12
            value["initialState"]["delayed"][0] = row
            value["queueContext"]["delayed"]["forms"][0] = dict(kind="newStored")
            yield f"all-action-congestion-{protocol}-{receiver}", value
    rng = random.Random(816217)
    for index in range(40):
        value = rich(83 + index % 4)
        state, context = value["initialState"], value["queueContext"]
        for _, hash in context["receiptIds"]: hash[:] = rng.randbytes(32)
        for row in context["dataIds"]: row["hash"] = list(rng.randbytes(32))
        context["delayed"]["firstIndex"] = rng.getrandbits(56)
        context["delayed"]["forms"] = [rng.choice([dict(kind="receipt"), dict(kind="storedV0", gas=rng.getrandbits(64), size=rng.getrandbits(64)),
            dict(kind="storedV1", gas=rng.getrandbits(64), size=rng.getrandbits(64)), dict(kind="newStored")]) for _ in state["delayed"]]
        state["receivedData"] = [[41, None if rng.randrange(2) else list(rng.randbytes(rng.randrange(40)))]]
        for row in state["delayed"]:
            row["receipt"]["actions"] = [dict(kind="functionCall", methodName="call\0漢字", args=list(rng.randbytes(8)),
                gas=rng.randrange(10**14), deposit=str(rng.getrandbits(128)))]
        if index % 2 == 0:
            state["delayed"].reverse()
            context["dataIds"].reverse(); context["receiptIds"].reverse(); context["actionFormats"].reverse()
        yield f"random-{index}", value


class QueueEncodingTests(unittest.TestCase):
    def test_all_columns_wrappers_and_canonical_roots(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum):
            for name, request in cases():
                with self.subTest(scenario=name):
                    projected = native_source(request)
                    queue = importer.native_call(native, "--encode-queues", projected)
                    accounts = importer.native_call(native, "--encode-state", account_source(request))
                    expected = accounts["initialEntries"] + queue["entries"]
                    actual = importer.execute(model, request, ROOT)
                    self.assertEqual(set(actual), {"initialEntries", "queueEntries", "root", "witness"})
                    self.assertEqual(entries(actual["queueEntries"]), entries(queue["entries"]))
                    self.assertEqual(entries(actual["initialEntries"]), entries(expected))
                    trie = importer.native_call(native, "--trie-lookups", dict(formatVersion=1, entries=expected, lookups=[]))
                    self.assertTrue(trie["witnessComplete"])
                    self.assertEqual(actual["root"], trie["root"])
                    self.assertEqual(entries(actual["witness"]), entries(trie["witness"]))
                    evidence.append(dict(scenario=name, request=request, nativeRequest=projected, nativeQueues=queue, nativeAccounts=accounts,
                        nativeTrie=trie, model=actual))
        atomic_write(ROOT / "audit/queue-encoding-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, runtimeIntegrated=False, originalShardRoots=False, cases=evidence), indent=2) + "\n").encode())

    def test_actual_callback_data_and_delayed_queue_bytes_without_native_context_inputs(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum), frozen_model(IDENTITIES) as (identities, id_checksum), tempfile.TemporaryDirectory() as directory:
            for protocol in [83, 84, 85, 86]:
                for method in ["spawn", "spawn_fail"]:
                    for schedule in ["callback-first", "data-first", "delayed"]:
                        with self.subTest(protocol=protocol, method=method, schedule=schedule):
                            target = Path(directory) / f"{protocol}-{method}-{schedule}"
                            origin = contract_probe.run_case(protocol, method, schedule, target, REFERENCE, CHAIN)
                            self.assertEqual(origin["differences"], [])
                            original = json.loads((target / "native.json").read_text())
                            replay = json.loads((target / "model.json").read_text())
                            signed = original["blocks"][0]["transactions"][0]
                            self.assertEqual(signed[-65], 0)
                            graph = receipt_request()
                            graph["identities"] = [dict(kind="hash", bytes=signed[:-65]), dict(kind="transaction", base=0, blockHeight=101),
                                dict(kind="action", base=1, blockHeight=102, index=0), dict(kind="data", base=2, blockHeight=102, index=0)] + [
                                dict(kind="receipt", base=1, blockHeight=102, index=index) for index in range(3)]
                            hashes = importer.execute(identities, graph, ROOT)["hashes"]
                            # Model allocation is independently checked; native IDs never enter context.
                            self.assertEqual([r["receiptId"] for r in origin["model"]["blocks"][0]["outgoingReceipts"]], [1])
                            self.assertEqual([r["receiptId"] for r in origin["model"]["blocks"][1]["outgoingReceipts"]], [2, 3, 5])
                            context = dict(receiptIds=[[1, hashes[1]], [2, hashes[4]], [3, hashes[5]], [5, hashes[6]]],
                                dataIds=[dict(id=4, hash=hashes[3], receiverId="captured.near")],
                                actionFormats=[[1, "legacy"], [2, "v2"], [3, "v2"], [5, "legacy"]], delayed=None)
                            codes = copy.deepcopy(replay["codes"])
                            for row in codes:
                                for field in ["codePath", "watPath"]: row[field] = str(target / row[field])
                            snapshots, previous, first, present = [], [], 0, False
                            for index, (left, right) in enumerate(zip(origin["native"]["blocks"], origin["model"]["blocks"])):
                                delayed = [row["receiptId"] for row in right["state"]["delayed"]]
                                # Persisted queue positions follow the model's FIFO transitions.
                                consumed = next(offset for offset in range(len(previous) + 1)
                                    if previous[offset:] == delayed[:len(previous) - offset])
                                first += consumed
                                if len(delayed) > len(previous) - consumed: present = True
                                previous = delayed
                                ctx = copy.deepcopy(context)
                                if present: ctx["delayed"] = dict(firstIndex=first, forms=[dict(kind="newStored") for _ in delayed])
                                request = dict(formatVersion=1, codes=codes, initialState=right["state"], queueContext=ctx,
                                    runtimeConfig=dict(configDir=str(target / "configs"), protocolVersion=protocol))
                                actual = importer.execute(model, request, ROOT)
                                expected = [row for row in left["state"]["entries"] if row[0][0] in [3, 4, 5, 6, 7]]
                                self.assertEqual(entries(actual["queueEntries"]), entries(expected))
                                snapshots.append(dict(block=index, request=request, expectedQueueEntries=expected, model=actual))
                            evidence.append(dict(protocol=protocol, method=method, schedule=schedule, origin=origin,
                                originalRequest=original, identityRequest=graph, hashes=hashes, snapshots=snapshots))
        atomic_write(ROOT / "audit/runtime-queue-encoding-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, identityBinarySha256=id_checksum, runtimeIntegrated=False,
            contextSource="original signed body, supplied schedule and Lean FIFO transitions; no native generated IDs or queue metadata", cases=evidence), indent=2) + "\n").encode())

    def test_incomplete_ambiguous_overflowing_context_fails_closed(self):
        variants = []
        for field in ["receiptIds", "dataIds", "actionFormats"]:
            value = rich(); value["queueContext"][field] = []; variants.append(value)
            value = rich(); value["queueContext"][field] *= 2; variants.append(value)
        value = rich(); value["queueContext"]["delayed"] = None; variants.append(value)
        value = rich(); value["queueContext"]["delayed"]["forms"].pop(); variants.append(value)
        value = rich(); value["queueContext"]["delayed"]["firstIndex"] = 2**64 - 1; variants.append(value)
        value = rich(); value["queueContext"]["dataIds"][0]["receiverId"] = "other.near"; variants.append(value)
        value = rich(); value["queueContext"]["receiptIds"][0][1] = [0] * 31; variants.append(value)
        value = rich(); value["queueContext"]["receiptIds"][1][1] = value["queueContext"]["receiptIds"][0][1]; variants.append(value)
        value = rich(); value["initialState"]["pendingDataCount"] = [[99, 1]]; variants.append(value)
        value = rich(); value["initialState"]["pendingDataCount"] = [[20, 2**32]]; variants.append(value)
        value = rich(); value["initialState"]["postponedByData"] = [[40, 99]]; variants.append(value)
        value = rich(); value["initialState"]["postponed"][0][1] = receipt(dict(kind="data", dataId=40, data=None)); variants.append(value)
        value = rich(); value.pop("runtimeConfig"); variants.append(value)
        value = rich(); value["queueContext"]["delayed"]["forms"][1]["gas"] = 2**64; variants.append(value)
        value = rich(); value["queueContext"]["delayed"]["forms"] = [dict(kind="newStored")] * 4
        value["initialState"]["delayed"][0]["receipt"]["actions"] = [dict(kind="functionCall", methodName="f", args=[], gas=2**64 - 1, deposit="0")]
        variants.append(value)
        with frozen_model(MODEL) as (model, _):
            for value in variants:
                with self.subTest(request=value):
                    result = subprocess.run([str(model)], input=json.dumps(value), text=True, capture_output=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertTrue(result.stderr)

    def test_native_adapter_rejects_malformed_typed_queue_inputs(self):
        template = native_source(rich())
        variants = []
        value = copy.deepcopy(template); value["receivedData"] *= 2; variants.append(value)
        value = copy.deepcopy(template); value["receivedData"][0]["receiverId"] = "Bad.near"; variants.append(value)
        value = copy.deepcopy(template); value["receivedData"][0]["dataId"] = [0] * 31; variants.append(value)
        value = copy.deepcopy(template); value["pendingDataCount"][0]["count"] = 2**32; variants.append(value)
        value = copy.deepcopy(template); value["delayed"]["firstIndex"] = 2**64 - 1; variants.append(value)
        value = copy.deepcopy(template); value["delayed"]["receipts"][0]["storage"]["kind"] = "unknown"; variants.append(value)
        value = copy.deepcopy(template); value["delayed"]["receipts"][1]["storage"]["gas"] = 2**64; variants.append(value)
        value = copy.deepcopy(template); value["postponed"][0]["receipt"]["ActionV2"]["refund_to"] = "other.near"; variants.append(value)
        value = copy.deepcopy(template); value["postponed"][0]["extra"] = True; variants.append(value)
        value = copy.deepcopy(template)
        value["delayed"]["receipts"][0]["storage"] = dict(kind="newStored")
        value["delayed"]["receipts"][0]["receipt"]["receipt"]["Action"]["actions"] = [dict(FunctionCall=dict(
            method_name="f", args="", gas=2**64 - 1, deposit="0"))]
        variants.append(value)
        with frozen_reference(REFERENCE) as (native, _):
            for value in variants:
                with self.subTest(request=value):
                    with self.assertRaises(subprocess.CalledProcessError): importer.native_call(native, "--encode-queues", value)


if __name__ == "__main__":
    unittest.main()
