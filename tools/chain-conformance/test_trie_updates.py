#!/usr/bin/env python3
"""Actual native TrieUpdate overlays, memory reads, rollbacks and root finalization."""
import json
import random
import subprocess
import unittest

from import_snapshot import execute, native_call
from near_rpc import b58encode
from prepare import ROOT, atomic_write
from probe import frozen_reference
from trie_probe import REFERENCE, MODEL, compare_updates, frozen_model


def raw(account, key):
    return [9] + list(account.encode()) + [44] + list(key)


def get(key=b"a", account=True, dereference=True):
    return dict(kind="get", key=list(key), accountNodes=account, dereference=dereference)


def put(key=b"a", value=b"new"):
    return dict(kind="set", key=list(key), value=list(value))


def op(kind, key=None):
    return dict(kind=kind, **({} if key is None else dict(key=list(key))))


def source(account="fixture.near", entries=None, operations=()):
    if entries is None: entries = [(b"a", b"old"), (b"ab", b"nested"), (b"b", b"shared")]
    return dict(formatVersion=1, accountId=account,
        entries=[[raw(account, key), list(value)] for key, value in entries] + [[[0, 1, 2], [42]]],
        operations=list(operations))


def cases():
    yield "visibility", source(operations=[get(), op("has", b"a"), put(), get(), op("commit"), get(),
        put(value=b"second"), get(), op("rollback"), get(), op("remove", b"b"), op("has", b"b"), get(b"b"),
        op("rollback"), get(b"b"), op("checkpoint"), get(), op("resetCache"), op("has", b"a"), get()])
    yield "rollback-cache", source(operations=[get(), put(), get(), op("rollback"), get()])
    yield "commit-memory-reset", source(operations=[get(), put(), op("commit"), op("resetCache"), get(), op("checkpoint"), get()])
    yield "tombstone-priority", source(operations=[get(), op("remove", b"a"), op("commit"), get(), put(), get(),
        op("rollback"), get(), op("checkpoint"), get(), op("has", b"a")])
    yield "repeated-keys", source(operations=[put(), put(value=b""), put(value=b"final"), op("commit"),
        put(value=b"old"), op("commit"), get(), op("checkpoint"), get()])
    yield "subtree-cache-across-roots", source(entries=[(b"a", b"shared"), (b"b", b"shared")],
        operations=[get(), put(b"b"), op("commit"), op("checkpoint"), get()])
    empty = source(entries=[], operations=[put(b"", b""), put(b"a", b"one"), put(b"ab", b"two"), op("commit"), op("checkpoint"),
        op("remove", b""), op("remove", b"a"), op("remove", b"ab"), op("commit"), op("checkpoint"), get(b"")])
    empty["entries"] = []
    yield "empty-root-roundtrip", empty
    for account in ["aa", "a" * 64, "0" * 64, "a-b.c_d"]:
        yield "key-encoding-" + account, source(account=account, entries=[(b"\0,\xff", b"binary")],
            operations=[get(b"\0,\xff"), put(b",\0\xff", b""), op("commit"), op("checkpoint"), get(b",\0\xff")])
    rng = random.Random(341791)
    keys = [b"", b"a", b"ab", b"ac", b"\0", b"\xff", b"\0,\xff"]
    for index in range(24):
        operations, pending = [], False
        for _ in range(128):
            kind = rng.choice(["set", "remove", "get", "get", "has", "commit", "rollback", "resetCache", "checkpoint"])
            key = rng.choice(keys)
            if kind == "set": operations.append(put(key, rng.choice([b"", b"shared", rng.randbytes(rng.randrange(1, 64))]))); pending = True
            elif kind == "remove": operations.append(op(kind, key)); pending = True
            elif kind == "get": operations.append(get(key, bool(rng.randrange(2)), bool(rng.randrange(2))))
            elif kind == "has": operations.append(op(kind, key))
            elif kind == "checkpoint" and pending: operations.append(op("commit")); operations.append(op(kind)); pending = False
            else:
                operations.append(op(kind))
                if kind in {"commit", "rollback"}: pending = False
        operations += [op("commit"), op("checkpoint")]
        yield f"random-{index}", source(operations=operations)


class TrieUpdateTests(unittest.TestCase):
    def test_native_overlays_memory_pointers_and_incremental_roots(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum):
            programs = list(cases())
            runtime_source = json.loads(subprocess.check_output([str(native), "--example"], text=True))
            runtime_trace = execute(native, runtime_source, ROOT)
            roots = {}
            for index, state in enumerate([runtime_trace["initialState"]] + [row["state"] for row in runtime_trace["blocks"]]):
                name = f"runtime-state-{index}"
                roots[name] = state["root"]
                program = source(account="alice.near", operations=[get(b"probe"), put(b"probe"), get(b"probe"),
                    op("commit"), get(b"probe"), op("checkpoint"), get(b"probe"), op("remove", b"probe"),
                    op("rollback"), get(b"probe"), op("remove", b"probe"), op("commit"), op("checkpoint")])
                program["entries"] = state["entries"]
                programs.append((name, program))
            for name, request in programs:
                with self.subTest(scenario=name):
                    report = compare_updates(request, native, model)
                    evidence.append(dict(scenario=name, **report))
                    self.assertEqual(report["differences"], [])
                    if name in roots:
                        self.assertEqual(b58encode(bytes(report["native"]["initialRoot"])), roots[name])
                    steps = report["native"]["steps"]
                    if name == "visibility":
                        self.assertEqual([steps[i]["lookup"]["reference"]["kind"] for i in [0, 3, 5, 7, 9, 16]],
                            ["trie", "memory", "memory", "memory", "memory", "trie"])
                        self.assertEqual(steps[9]["lookup"]["value"], list(b"new"))
                        self.assertEqual(steps[12]["events"], [])
                        self.assertEqual(steps[18]["events"], [])
                        self.assertTrue(all(not event["cached"] for event in steps[19]["events"]))
                    if name == "rollback-cache":
                        self.assertEqual(steps[-1]["counts"]["disk"], 0)
                        self.assertGreater(steps[-1]["counts"]["mem"], 0)
                        self.assertEqual(steps[2]["events"], [])
                    if name == "commit-memory-reset":
                        self.assertEqual(steps[4]["events"], [])
                        self.assertEqual(steps[4]["lookup"]["reference"]["kind"], "memory")
                        self.assertGreater(steps[-1]["counts"]["disk"], 0)
                    if name == "repeated-keys":
                        self.assertEqual(steps[2]["prospectiveCount"], 1)
                        self.assertEqual(steps[5]["committedCount"], 1)
                    if name == "subtree-cache-across-roots":
                        self.assertGreater(steps[-1]["counts"]["disk"], 0)
                        self.assertGreater(steps[-1]["counts"]["mem"], 0)
                    if name == "empty-root-roundtrip":
                        self.assertEqual(steps[-1]["baseRoot"], [0] * 32)
                        self.assertEqual(steps[-1]["viewEntries"], [])
        atomic_write(ROOT / "audit/trie-update-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, runtimeIntegrated=False,
            runtimeOrigin=dict(request=runtime_source, trace=runtime_trace), cases=evidence), indent=2) + "\n").encode())

    def test_invalid_operations_and_checkpoint_preconditions_fail_closed(self):
        variants = [source(operations=[put(), op("checkpoint")]), source(operations=[op("unknown")]),
            source(account="A.near"), source(operations=[{**get(), "dereference": 1}]),
            source(operations=[{**put(), "value": [256]}]), source(operations=[{**op("commit"), "key": []}]),
            source(operations=[{**op("has", b"a"), "accountNodes": True}])]
        with frozen_reference(REFERENCE) as (native, _), frozen_model(MODEL) as (model, _):
            for request in variants:
                with self.subTest(request=request):
                    with self.assertRaises(subprocess.CalledProcessError): native_call(native, "--trie-updates", request)
                    result = subprocess.run([str(model)], input=json.dumps(request), text=True, capture_output=True)
                    self.assertNotEqual(result.returncode, 0)
                    self.assertTrue(result.stderr)


if __name__ == "__main__":
    unittest.main()
