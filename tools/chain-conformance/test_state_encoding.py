#!/usr/bin/env python3
"""Typed Lean state -> independent native Borsh bytes and complete trie objects.

Both executors receive projections of the original typed records. Native encoded
state/root/witness never enter the Lean request. The Python public-key transport
is independently base58 encoded; code names use Python hashlib, checked by Lean.
"""
import hashlib
import json
from pathlib import Path
import random
import subprocess
import unittest

from import_snapshot import execute, native_call
from near_rpc import b58encode
from prepare import HERE, ROOT, atomic_write
from probe import frozen_reference
from test_replay import empty_state, action_receipt
from trie_probe import REFERENCE, frozen_model

MODEL = ROOT / "near-lean/chain/.lake/build/bin/state-encode"


def source():
    return dict(formatVersion=1, codes=[], initialState=empty_state())


def native_source(request):
    """Transport only: no Borsh encoding, hashes, roots or native output used."""
    state = request["initialState"]
    codes = {row["hash"]: list(Path(row["codePath"]).read_bytes()) for row in request["codes"]}
    rows = []
    for name, account in state["accounts"]:
        keys = []
        for (owner, pk), key in state["accessKeys"]:
            if owner != name: continue
            permission = key["permission"]
            native = "FullAccess" if permission["kind"] == "fullAccess" else dict(FunctionCall=dict(
                allowance=permission["allowance"], receiver_id=permission["receiverId"],
                method_names=permission["methodNames"]))
            text = ["ed25519:", "secp256k1:"][pk[0]] + b58encode(bytes(pk[1:]))
            keys.append(dict(publicKey=text, accessKey=dict(nonce=key["nonce"], permission=native)))
        rows.append(dict(accountId=name, amount=account["amount"], locked=account["locked"],
            storageUsage=account["storageUsage"], code=codes.get(account["codeHash"]), keys=keys,
            storage=dict(state["storage"]).get(name, [])))
    return dict(accounts=rows)


def catalogue(request):
    blob = (HERE / "fixtures/replay.wasm").read_bytes()
    name = b58encode(hashlib.sha256(blob).digest())
    request["codes"] = [dict(hash=name, codePath=str(HERE / "fixtures/replay.wasm"),
        watPath=str(HERE / "fixtures/replay.wat"))]
    request["initialState"]["accounts"][0][1]["codeHash"] = name


def cases():
    yield "empty", dict(formatVersion=1, codes=[], initialState={**empty_state(), "accounts": [], "accessKeys": []})
    yield "ordinary", source()
    request = source()
    catalogue(request)
    request["initialState"]["accounts"][1][1].update(amount=str(2**128 - 1), locked=str(2**128 - 1), storageUsage=2**64 - 1)
    request["initialState"]["storage"] = [["alice.near", [[[], []], [[0, 44, 255], [1, 0, 255]]]]]
    for tag, width in [(0, 32), (1, 64)]:
        for index, allowance in enumerate([None, "0", str(2**128 - 1)]):
            request["initialState"]["accessKeys"].append([["bob.near", [tag] + [index + 3] * width],
                dict(nonce=2**64 - 1, permission=dict(kind="functionCall", allowance=allowance,
                    receiverId="not an account 🦀\0", methodNames=["", "méthode", "漢字", "dup", "dup", "\0"]))])
    yield "borsh-boundaries-code-unicode", request
    rng = random.Random(583721)
    for index in range(40):
        request = source()
        state = request["initialState"]
        state["accounts"] = []
        state["accessKeys"] = []
        for position in range(rng.randrange(1, 7)):
            name = "a" * 64 if position == 0 else f"account-{position}.near"
            state["accounts"].append([name, dict(amount=str(rng.getrandbits(128)), locked=str(rng.getrandbits(128)),
                codeHash=None, storageUsage=rng.getrandbits(64))])
            keys = []
            for _ in range(rng.randrange(5)):
                key = list(rng.randbytes(rng.randrange(10)))
                if key not in [row[0] for row in keys]: keys.append([key, list(rng.randbytes(rng.randrange(32)))])
            state["storage"].append([name, keys])
            for tag, width in [(0, 32), (1, 64)]:
                permission = dict(kind="fullAccess") if rng.randrange(2) else dict(kind="functionCall",
                    allowance=None if rng.randrange(2) else str(rng.getrandbits(128)), receiverId="",
                    methodNames=["alpha", "β", "\0"][:rng.randrange(4)])
                state["accessKeys"].append([[name, [tag] + list(rng.randbytes(width))],
                    dict(nonce=rng.getrandbits(64), permission=permission)])
        if index % 2 == 0: catalogue(request)
        if index % 3 == 0:
            state["accounts"].reverse()
            state["accessKeys"].reverse()
            state["storage"].reverse()
        yield f"random-{index}", request


def entries(rows):
    result = {bytes(key).hex(): value for key, value in rows}
    if len(rows) != len(result): raise ValueError("duplicate raw entry")
    return result


class StateEncodingTests(unittest.TestCase):
    def test_typed_records_and_canonical_roots_match_native(self):
        evidence = []
        with frozen_reference(REFERENCE) as (native, build), frozen_model(MODEL) as (model, checksum):
            for name, request in cases():
                with self.subTest(scenario=name):
                    native_request = native_source(request)
                    expected = native_call(native, "--encode-state", native_request)
                    actual = execute(model, request, ROOT)
                    self.assertEqual(set(actual), {"initialEntries", "root", "witness"})
                    self.assertEqual(entries(actual["initialEntries"]), entries(expected["initialEntries"]))
                    trie = native_call(native, "--trie-lookups", dict(formatVersion=1,
                        entries=expected["initialEntries"], lookups=[]))
                    self.assertTrue(trie["witnessComplete"])
                    self.assertEqual(actual["root"], trie["root"])
                    self.assertEqual(entries(actual["witness"]), entries(trie["witness"]))
                    evidence.append(dict(scenario=name, request=request, nativeRequest=native_request,
                        native=expected, nativeTrie=trie, model=actual))
        atomic_write(ROOT / "audit/state-encoding-regressions.json", (json.dumps(dict(referenceBuild=build,
            modelBinarySha256=checksum, runtimeIntegrated=False, historicalState=False, cases=evidence), indent=2) + "\n").encode())

    def test_unrepresented_ids_bad_keys_duplicates_and_unbound_code_fail_closed(self):
        variants = []
        for field, value in [("postponed", [[20, action_receipt([])]]), ("pendingDataCount", [[20, 1]]),
                ("postponedByData", [[40, 20]]), ("receivedData", [[40, []]]), ("delayed", [action_receipt([])])]:
            request = source()
            request["initialState"][field] = value
            variants.append(request)
        for pk in [[], [0] * 32, [1] * 64, [2] * 33, [3] * 33, [256] * 33]:
            request = source()
            request["initialState"]["accessKeys"][0][0][1] = pk
            variants.append(request)
        for field in ["accounts", "accessKeys"]:
            request = source()
            request["initialState"][field] *= 2
            variants.append(request)
        for field, value in [("accounts", [["Bad.near", empty_state()["accounts"][0][1]]]),
                ("storage", [["missing.near", []]]), ("storage", [["alice.near", [[[0], []], [[0], [1]]]]])]:
            request = source()
            request["initialState"][field] = value
            variants.append(request)
        request = source()
        request["initialState"]["accessKeys"][0][0][0] = "missing.near"
        variants.append(request)
        for name in ["replay", "1" * 32, "2" * 44]:
            request = source()
            catalogue(request)
            request["codes"][0]["hash"] = name
            request["initialState"]["accounts"][0][1]["codeHash"] = name
            variants.append(request)
        for value in [str(2**128), "-1"]:
            request = source()
            request["initialState"]["accounts"][0][1]["amount"] = value
            variants.append(request)
        request = source()
        request["initialState"]["accounts"][0][1]["storageUsage"] = 2**64
        variants.append(request)
        request = source()
        request["initialState"]["accessKeys"][0][1]["nonce"] = 2**64
        variants.append(request)
        request = source()
        request["initialState"]["accessKeys"][0][1]["permission"] = dict(kind="functionCall",
            allowance=str(2**128), receiverId="alice.near", methodNames=[])
        variants.append(request)
        request = source()
        request["initialState"]["accounts"][0][1]["codeHash"] = "missing"
        variants.append(request)
        request = source()
        request["initialState"]["storage"] = [["alice.near", []], ["alice.near", []]]
        variants.append(request)
        with frozen_model(MODEL) as (model, _):
            for request in variants:
                with self.subTest(request=request):
                    process = subprocess.run([str(model)], input=json.dumps(request), text=True, capture_output=True)
                    self.assertNotEqual(process.returncode, 0)
                    self.assertTrue(process.stderr)


if __name__ == "__main__":
    unittest.main()
