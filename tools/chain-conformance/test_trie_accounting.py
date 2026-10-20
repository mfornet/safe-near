#!/usr/bin/env python3
"""Canonical Borsh trie paths, values and accounting-cache reuse against near-store."""
import copy
import hashlib
import json
import random
import subprocess
import unittest
from unittest import mock

from import_snapshot import execute, native_call
from near_rpc import b58encode
from prepare import ROOT, atomic_write
from probe import frozen_reference
from trie_probe import REFERENCE, MODEL, checked_model_request, compare, frozen_model


def query(key, account=True, dereference=True, reset=False):
    return dict(key=list(key), accountNodes=account, dereference=dereference, resetCache=reset)


def request(entries, keys):
    lookups = []
    for index, key in enumerate(keys):
        lookups += [query(key, reset=index % 3 == 0), query(key), query(key, account=False),
                    query(key, dereference=False)]
    return dict(formatVersion=1, entries=[[list(key), list(value)] for key, value in entries], lookups=lookups)


def corpus():
    fixed = [[], [(b"", b"")], [(b"a", b"")], [(b"a", b"hello")],
        [(key, b"shared") for key in [b"", b"\0", b"\0\1", b"\0\1\2", b"\x10", b"\xff"]],
        [(bytes([n * 16]), bytes([n])) for n in range(16)],
        [(bytes([n * 16, 1]), b"identical") for n in range(16)],
        [(b"prefix" * 20 + bytes([n]), bytes(range(n))) for n in range(8)],
        [(b"a", b"x" * 4096), (b"b", b"x" * 4096), (b"c", b"\0" * 33)]]
    for index, entries in enumerate(fixed):
        yield f"fixed-{index}", request(entries, [key for key, _ in entries] + [b"missing", b"", b"\0", b"\xff\xff"])
    rng = random.Random(927318)
    for index in range(24):
        keys = sorted({rng.randbytes(rng.randrange(0, 10)) for _ in range(index + 1)})
        entries = [(key, rng.choice([b"", b"same", rng.randbytes(rng.randrange(1, 80))])) for key in keys]
        yield f"random-{index}", request(entries, keys + [rng.randbytes(10), b"\xff"])


class TrieAccountingTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.native_context = frozen_reference(REFERENCE)
        cls.native, cls.build = cls.native_context.__enter__()
        cls.model_context = frozen_model(MODEL)
        cls.model, cls.checksum = cls.model_context.__enter__()
        cls.evidence = []
        cls.runtime_origin = None

    @classmethod
    def tearDownClass(cls):
        cls.model_context.__exit__(None, None, None)
        cls.native_context.__exit__(None, None, None)
        atomic_write(ROOT / "audit/trie-accounting-regressions.json", (json.dumps(dict(
            referenceBuild=cls.build, modelBinarySha256=cls.checksum, runtimeIntegrated=False,
            witnessHashBinding="external SHA256 check", runtimeOrigin=cls.runtime_origin, cases=cls.evidence), indent=2) + "\n").encode())

    def test_native_trie_paths_and_cache_counts(self):
        kinds, flags = set(), set()
        lookups = 0
        for name, source in corpus():
            with self.subTest(scenario=name):
                report = compare(source, self.native, self.model)
                self.evidence.append(dict(scenario=name, **report))
                self.assertEqual(report["differences"], [])
                lookups += len(report["native"]["results"])
                witness = {tuple(key): value for key, value in report["native"]["witness"]}
                for result in report["native"]["results"]:
                    self.assertEqual(sum(result["counts"].values()), len(result["events"]))
                    for event in result["events"]:
                        flags.add((event["kind"], event["cached"]))
                        if event["kind"] == "node": kinds.add(witness[tuple(event["hash"])][0])
        self.assertGreater(lookups, 1000)
        self.assertEqual(kinds, {0, 1, 2, 3})
        self.assertEqual(flags, {("node", False), ("node", True), ("value", False), ("value", True)})

    def test_actual_runtime_states_rebuild_the_same_canonical_roots(self):
        source = json.loads(subprocess.check_output([str(self.native), "--example"], text=True))
        trace = execute(self.native, source, ROOT)
        type(self).runtime_origin = dict(request=source, trace=trace)
        states = [trace["initialState"]] + [block["state"] for block in trace["blocks"]]
        for index, state in enumerate(states):
            with self.subTest(state=index):
                entries = [(bytes(key), bytes(value)) for key, value in state["entries"]]
                source = request(entries, [key for key, _ in entries] + [b"", b"missing-key", b"\xff"])
                report = compare(source, self.native, self.model)
                self.evidence.append(dict(scenario=f"runtime-state-{index}", runtimeRoot=state["root"],
                    originRootMatches=b58encode(bytes(report["native"]["root"])) == state["root"], **report))
                self.assertEqual(report["differences"], [])
                self.assertEqual(b58encode(bytes(report["native"]["root"])), state["root"])
                for result, (_, value) in zip(report["native"]["results"][::4], entries):
                    self.assertEqual(result["value"], list(value))

    def test_identical_node_and_value_bytes_share_one_cache_identity(self):
        entries = [(b"\0", b"alpha"), (b"\x10", b"beta")]
        first = native_call(self.native, "--trie-lookups", request(entries, [b"\0"]))
        event = [event for event in first["results"][0]["events"] if event["kind"] == "node"][-1]
        payload = dict((tuple(key), value) for key, value in first["witness"])[tuple(event["hash"])]
        entries.append((b"\xf0", bytes(payload)))
        source = dict(formatVersion=1, entries=[[list(k), list(v)] for k, v in entries],
                      lookups=[query(b"\0"), query(b"\xf0"), query(b"\xf0", reset=True), query(b"\0")])
        report = compare(source, self.native, self.model)
        self.evidence.append(dict(scenario="cross-role-cache-alias", **report))
        self.assertEqual(report["differences"], [])
        forward = report["native"]["results"][1]
        self.assertEqual(forward["reference"]["hash"], event["hash"])
        self.assertEqual(forward["events"][-1], dict(hash=event["hash"], kind="value", cached=True))
        reverse = [row for row in report["native"]["results"][3]["events"] if row["kind"] == "node"]
        self.assertEqual(reverse[-1], dict(hash=event["hash"], kind="node", cached=True))

    def test_hash_binding_and_comparison_reject_tampered_observations(self):
        source = request([(b"a", b"hello")], [b"a"])
        expected = native_call(self.native, "--trie-lookups", source)
        changed = copy.deepcopy(expected)
        changed["witness"][0][1].append(0)
        with self.assertRaisesRegex(ValueError, "does not bind"):
            checked_model_request(source, changed)
        changed = copy.deepcopy(expected)
        changed["witness"].append(changed["witness"][0])
        with self.assertRaisesRegex(ValueError, "duplicate"):
            checked_model_request(source, changed)
        modeled = checked_model_request(source, expected)
        result = execute(self.model, modeled, ROOT)
        self.assertEqual(result["results"], expected["results"])
        reordered = {**modeled, "witness": list(reversed(modeled["witness"]))}
        self.assertEqual(execute(self.model, reordered, ROOT), result)
        for field in ["counts", "events", "reference", "value"]:
            altered = copy.deepcopy(result)
            altered["results"][0][field] = "changed"
            self.assertNotEqual(altered["results"], expected["results"])

    def test_model_execution_failure_retains_native_witness_and_is_not_a_match(self):
        source = request([(b"a", b"hello")], [b"a"])
        failure = subprocess.CalledProcessError(1, "trie-replay", stderr="missing trie witness object")
        with mock.patch("trie_probe.execute", side_effect=failure):
            report = compare(source, self.native, self.model)
        self.assertEqual(report["request"], source)
        self.assertTrue(report["native"]["witness"])
        self.assertIsNone(report["model"])
        self.assertEqual(report["modelExecutionError"], failure.stderr)
        self.assertTrue(report["differences"])

    def test_malformed_witnesses_and_wire_input_fail_closed(self):
        source = request([(b"a", b"hello")], [b"a"])
        expected = native_call(self.native, "--trie-lookups", source)
        modeled = checked_model_request(source, expected)
        variants = []
        for patch in [dict(formatVersion=2), dict(root=[0]), dict(root=[True] * 32),
                      dict(witness=[]), dict(extra=True), dict(results=expected["results"])]:
            variants.append({**modeled, **patch})
        duplicate = copy.deepcopy(modeled)
        duplicate["witness"].append(duplicate["witness"][0])
        variants.append(duplicate)
        bad_bool = copy.deepcopy(modeled)
        bad_bool["lookups"][0]["dereference"] = 1
        variants.append(bad_bool)
        root_bytes = dict((tuple(key), value) for key, value in modeled["witness"])[tuple(modeled["root"])]
        trailing = root_bytes + [0]
        trailing_hash = list(hashlib.sha256(bytes(trailing)).digest())
        variants.append({**modeled, "root": trailing_hash, "witness": [[trailing_hash, trailing]]})
        bad_padding = root_bytes.copy()
        bad_padding[5] = 0x21
        bad_padding_hash = list(hashlib.sha256(bytes(bad_padding)).digest())
        variants.append({**modeled, "root": bad_padding_hash, "witness": [[bad_padding_hash, bad_padding]]})
        bad_length = root_bytes.copy()
        bad_length[7] += 1
        bad_length_hash = list(hashlib.sha256(bytes(bad_length)).digest())
        variants.append({**modeled, "root": bad_length_hash,
                         "witness": [[bad_length_hash, bad_length]] +
                             [row for row in modeled["witness"] if row[0] != modeled["root"]]})
        missing_value = copy.deepcopy(modeled)
        missing_value["witness"] = [row for row in missing_value["witness"] if row[0] == modeled["root"]]
        variants.append(missing_value)
        cyclic_hash = [1] * 32
        extension = [3, 1, 0, 0, 0, 0x10] + cyclic_hash + [0] * 8
        variants.append({**modeled, "root": cyclic_hash, "witness": [[cyclic_hash, extension]],
                         "lookups": [query(b"\0")]})
        for payload in [[9], [0], [0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0x40],
                        [3, 1, 0, 0, 0, 0] + [1] * 32 + [0] * 8]:
            identifier = list(hashlib.sha256(bytes(payload)).digest())
            variants.append({**modeled, "root": identifier, "witness": [[identifier, payload]]})
        for value in variants:
            with self.subTest(request=value):
                result = subprocess.run([str(self.model)], input=json.dumps(value), text=True, capture_output=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertTrue(result.stderr)
        for patch in [dict(formatVersion=2), dict(entries=[[[1], [2]], [[1], [3]]]), dict(extra=True)]:
            with self.assertRaises(subprocess.CalledProcessError):
                native_call(self.native, "--trie-lookups", {**source, **patch})


if __name__ == "__main__":
    unittest.main()
