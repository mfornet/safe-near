#!/usr/bin/env python3
"""Prepare a queue-free trusted-chain genesis from complete captured accounts.

Native protocol types encode the trie and sign synthetic transactions. Both
executors validate the initial represented state. This is not historical replay.
"""
from __future__ import annotations

import argparse
import base64
import copy
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from prepare import HERE, ROOT, digest
from probe import file_digest, frozen_reference
from gas_probe import canonical_state

sys.path.insert(0, str(HERE.parent))
from near_snapshot import EMPTY_CODE_HASH, code_hash, decode
from snapshot_vm import account_id, amount, byte_list, storage_pairs, uint



REGISTERED_MODEL = ROOT / "near-lean/chain/.lake/build/bin/registered-replay"
REPRESENTED_COLUMNS = frozenset([0, 1, 2, 3, 4, 5, 6, 7, 9])


def represented_entries(rows):
    return [row for row in rows if row[0] and row[0][0] in REPRESENTED_COLUMNS]


def canonical_entries(rows, *, complete=False):
    """Compare every represented raw key/value; never hide duplicate/extra keys."""
    result, seen = [], set()
    if not isinstance(rows, list): raise ValueError("expected represented trie entry list")
    for row in rows:
        if not isinstance(row, list) or len(row) != 2: raise ValueError("invalid represented trie entry")
        key, value = row
        for raw in [key, value]:
            if not isinstance(raw, list) or any(type(byte) is not int or not 0 <= byte < 256 for byte in raw):
                raise ValueError("invalid represented trie bytes")
        if not key or (not complete and key[0] not in REPRESENTED_COLUMNS): raise ValueError("unrepresented model trie column")
        identity = bytes(key)
        if identity in seen: raise ValueError("duplicate represented trie key")
        seen.add(identity); result.append([key, value])
    return sorted(result, key=lambda row: bytes(row[0]))


def fields(value, required, optional=()):
    if not isinstance(value, dict) or set(value) - set(required) - set(optional) or set(required) - set(value):
        raise ValueError(f"expected fields {list(required)}, optional {list(optional)}")


def permission(raw):
    if raw == "FullAccess":
        return {"kind": "fullAccess"}
    fields(raw, ["FunctionCall"])
    value = raw["FunctionCall"]
    fields(value, ["allowance", "receiver_id", "method_names"])
    allowance = None if value["allowance"] is None else amount(value["allowance"], "allowance")
    if not isinstance(value["method_names"], list) or any(not isinstance(x, str) for x in value["method_names"]):
        raise ValueError("invalid function-call method names")
    if not isinstance(value["receiver_id"], str):
        raise ValueError("invalid function-call key receiver")
    return dict(kind="functionCall", allowance=allowance,
                receiverId=value["receiver_id"], methodNames=value["method_names"])


def access_key(raw):
    fields(raw, ["nonce", "permission"])
    return {"nonce": uint(raw["nonce"], 64, "key nonce"), "permission": permission(raw["permission"])}


def key_bytes(text, keys):
    if not isinstance(text, str) or not text.startswith(("ed25519:", "secp256k1:")):
        raise ValueError("chain import currently supports ordinary Ed25519 and secp256k1 keys")
    return byte_list(keys[text], "native public key bytes")


def validate_snapshot(snapshot):
    if snapshot.get("format") != "safe-near-snapshot-v1":
        raise ValueError("unsupported snapshot format")
    header = snapshot["block"]["header"]
    uint(header["height"], 64, "captured block height")
    if not isinstance(header["hash"], str) or not header["hash"]:
        raise ValueError("missing captured block hash")
    version = uint(snapshot["protocol_config"]["protocol_version"], 32, "protocol version")
    if not 83 <= version <= 86:
        raise ValueError("reference supports protocol versions 83–86")
    rows, codes, ids = [], {}, set()
    if not isinstance(snapshot["accounts"], list) or not snapshot["accounts"]:
        raise ValueError("snapshot must contain at least one account")
    for entry in snapshot["accounts"]:
        identifier = account_id(entry["account_id"], "captured account")
        if identifier in ids:
            raise ValueError("duplicate captured account")
        ids.add(identifier)
        account, storage = entry["account"], entry["storage"]
        if storage.get("complete") is not True or storage.get("prefixes_base64") != [""]:
            raise ValueError("chain import requires complete account storage; filtered keys are unknown")
        if account.get("global_contract_hash") or account.get("global_contract_account_id"):
            raise ValueError("global contract references are not supported")
        unknown = set(account) - {"amount", "locked", "storage_usage", "code_hash", "storage_paid_at",
                                  "global_contract_hash", "global_contract_account_id"}
        if unknown or account.get("storage_paid_at", 0) != 0:
            raise ValueError("unsupported account fields")
        code = entry["code"]
        blob = None
        if account["code_hash"] == EMPTY_CODE_HASH:
            if code is not None:
                raise ValueError("unexpected code for a code-free account")
        else:
            if not code:
                raise ValueError("captured contract code is missing")
            blob = decode(code["code_base64"])
            if code_hash(blob) != code["hash"] or code["hash"] != account["code_hash"]:
                raise ValueError("captured code hash mismatch")
            if not blob.startswith(b"\0asm\1\0\0\0"):
                raise ValueError("expected Wasm version 1 code")
            codes[code["hash"]] = blob
        if entry.get("gas_key_nonces"):
            raise ValueError("gas keys are not represented by the runtime model")
        keys, seen = [], set()
        for key in entry["access_keys"]:
            fields(key, ["public_key", "access_key"])
            text = key["public_key"]
            if not isinstance(text, str) or not text.startswith(("ed25519:", "secp256k1:")):
                raise ValueError("unsupported captured public key kind")
            if text in seen:
                raise ValueError("duplicate captured access key")
            seen.add(text)
            access_key(key["access_key"])
            keys.append(dict(publicKey=text, accessKey=key["access_key"]))
        pairs = storage_pairs([[list(decode(item["key"])), list(decode(item["value"]))]
                               for item in storage["values"]])
        rows.append(dict(accountId=identifier, amount=amount(account["amount"], "account balance"),
            locked=amount(account["locked"], "locked balance"), storageUsage=uint(account["storage_usage"], 64, "storage usage"),
            code=None if blob is None else list(blob), keys=keys, storage=pairs))
    return sorted(rows, key=lambda row: row["accountId"]), codes, version


def native_call(binary, mode, request):
    result = subprocess.run([str(binary), mode], input=json.dumps(request), text=True,
                            capture_output=True, check=True)
    return json.loads(result.stdout)


def execute(binary, request, cwd):
    result = subprocess.run([str(binary)], input=json.dumps(request), text=True,
                            capture_output=True, check=True, cwd=cwd)
    return json.loads(result.stdout)


def action(value, keys, codes):
    if value == "CreateAccount" or value == {"CreateAccount": {}}:
        return {"kind": "createAccount"}
    if not isinstance(value, dict) or len(value) != 1:
        raise ValueError("unsupported native action view")
    name, data = next(iter(value.items()))
    if name == "Transfer":
        return dict(kind="transfer", deposit=amount(data["deposit"], "deposit"))
    if name == "FunctionCall":
        return dict(kind="functionCall", methodName=data["method_name"], args=list(decode(data["args"])),
                    gas=uint(data["gas"], 64, "call gas"), deposit=amount(data["deposit"], "deposit"))
    if name == "DeployContract":
        blob = decode(data["code"])
        code = code_hash(blob)
        codes[code] = blob
        return dict(kind="deployContract", codeHash=code)
    if name == "Stake":
        return dict(kind="stake", stake=amount(data["stake"], "stake"), publicKey=key_bytes(data["public_key"], keys))
    if name == "AddKey":
        return dict(kind="addKey", publicKey=key_bytes(data["public_key"], keys), accessKey=access_key(data["access_key"]))
    if name == "DeleteKey":
        return dict(kind="deleteKey", publicKey=key_bytes(data["public_key"], keys))
    if name == "DeleteAccount":
        return dict(kind="deleteAccount", beneficiaryId=account_id(data["beneficiary_id"], "beneficiary"))
    raise ValueError(f"action not represented by model: {name}")


def initial_state(trace, keys, codes):
    result = dict(accounts=[], accessKeys=[], storage=[], postponed=[], pendingDataCount=[],
                  postponedByData=[], receivedData=[], delayed=[], nextId=1)
    storage, contracts = {}, {}
    for row in trace["initialState"]["decodedRecords"]:
        if set(row) != {"key", "record"} or len(row["record"]) != 1:
            raise ValueError("unexpected opaque or undecodable imported genesis column")
        kind, value = next(iter(row["record"].items()))
        identifier = value["account_id"]
        if kind == "Account":
            a = value["account"]
            label = None if a["code_hash"] == EMPTY_CODE_HASH else a["code_hash"]
            if label is not None and label not in codes:
                raise ValueError("native account code hash is absent from frozen catalogue")
            result["accounts"].append([identifier, dict(amount=a["amount"], locked=a["locked"],
                storageUsage=a["storage_usage"], codeHash=label)])
        elif kind == "AccessKey":
            result["accessKeys"].append([[identifier, key_bytes(value["public_key"], keys)], access_key(value["access_key"])])
        elif kind == "Data":
            storage.setdefault(identifier, []).append([list(decode(value["data_key"])), list(decode(value["value"]))])
        elif kind == "Contract":
            blob = decode(value["code"])
            label = code_hash(blob)
            if codes.get(label) != blob:
                raise ValueError("native contract bytes disagree with frozen catalogue")
            contracts[identifier] = label
        else:
            raise ValueError(f"unsupported imported genesis record: {kind}")
    for identifier, a in result["accounts"]:
        if contracts.get(identifier) != a["codeHash"]:
            raise ValueError("native account and contract records disagree")
    result["storage"] = [[identifier, storage_pairs(entries)] for identifier, entries in sorted(storage.items())]
    return canonical_state(result)


def write_json(path, value, *, compact=False):
    options = dict(separators=(",", ":")) if compact else dict(indent=2)
    path.write_text(json.dumps(value, sort_keys=True, **options) + "\n")


def publish(stage, destination):
    """Never overwrite; publish requests after assets and the manifest last.

    A directory without manifest.json is incomplete. Exclusive mkdir and hard
    links reject concurrent filenames rather than replacing somebody's files.
    """
    required = ["native.json", "model.json", "registered.json", "manifest.json"]
    if any(not (stage / name).is_file() for name in required):
        raise ValueError("incomplete fixture publication stage")
    destination.mkdir()
    for folder in sorted(path for path in stage.rglob("*") if path.is_dir()):
        (destination / folder.relative_to(stage)).mkdir()
    names = sorted(path.relative_to(stage) for path in stage.rglob("*") if path.is_file())
    ordered = [name for name in names if name.as_posix() not in {"native.json", "model.json", "registered.json", "manifest.json"}]
    ordered += [Path("native.json"), Path("model.json"), Path("registered.json"), Path("manifest.json")]
    for name in ordered:
        os.link(stage / name, destination / name)


def prepare(snapshot, destination, *, reference, model, scenario=None, registered_model=None):
    rows, codes, version = validate_snapshot(snapshot)
    registered_model = REGISTERED_MODEL if registered_model is None else Path(registered_model)
    destination = destination.resolve()
    if destination.exists():
        raise FileExistsError(f"destination already exists: {destination}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    scenario = copy.deepcopy(scenario) if scenario is not None else {"blocks": []}
    fields(scenario, ["blocks"], ["caller", "codeBlobs"])
    if not isinstance(scenario["blocks"], list):
        raise ValueError("scenario blocks must be an array")
    for text in scenario.get("codeBlobs", []):
        blob = decode(text)
        codes[code_hash(blob)] = blob
    with frozen_reference(reference) as (native, build), tempfile.TemporaryDirectory(prefix="safe-near-chain-import-") as temporary, tempfile.TemporaryDirectory(prefix=".chain-import-", dir=destination.parent) as staging:
        temporary = Path(temporary)
        stage = Path(staging) / "fixture"
        stage.mkdir()
        lean = temporary / "chain-replay"
        shutil.copy2(model, lean)
        registered = temporary / "registered-replay"
        shutil.copy2(registered_model, registered)
        prototype = json.loads(subprocess.check_output([str(native), "--example"], text=True))["blocks"][0]
        config_dir = stage / "configs"
        config_dir.mkdir()
        config_source = ROOT / f"near-lean/vm/configs/runtime_config_v{version}.json"
        shutil.copyfile(config_source, config_dir / config_source.name)
        config = json.loads(config_source.read_text())
        signed, counts, specifications = None, [], []
        for block in scenario["blocks"]:
            fields(block, ["blockHeight", "blockTimestamp", "epochHeight", "gasPrice", "gasLimit", "randomSeed",
                           "prevBlockHash", "incomingIndices", "transactions"], ["congestionInfo", "bandwidthRequests"])
            for name in ("blockHeight", "blockTimestamp", "epochHeight"):
                uint(block[name], 64, name)
            amount(block["gasPrice"], "block gas price")
            if block["gasLimit"] is not None:
                uint(block["gasLimit"], 64, "gas limit")
            byte_list(block["randomSeed"], "random seed", 32)
            byte_list(block["prevBlockHash"], "previous hash", 32)
            if block["incomingIndices"] is not None:
                if not isinstance(block["incomingIndices"], list):
                    raise ValueError("receipt schedule must be null or an array")
                for position in block["incomingIndices"]:
                    uint(position, 64, "receipt position")
            if not isinstance(block["transactions"], list):
                raise ValueError("transactions must be an array")
            counts.append(len(block["transactions"]))
            for tx in block["transactions"]:
                fields(tx, ["receiverId", "nonce", "actions"], ["blockHash", "version", "nonceMode"])
                version_tag = uint(tx.get("version", 0), 8, "transaction version")
                if version_tag > 1 or tx.get("nonceMode", "monotonic") not in {"monotonic", "strict"}:
                    raise ValueError("unsupported transaction envelope or nonce mode")
                specifications.append(dict(version=version_tag, nonceMode=tx.get("nonceMode", "monotonic"), receiverId=account_id(tx["receiverId"], "transaction receiver"),
                    nonce=uint(tx["nonce"], 64, "transaction nonce"), actions=tx["actions"],
                    blockHash=byte_list(tx.get("blockHash", block["prevBlockHash"]), "transaction block hash", 32)))
        if "caller" in scenario:
            caller = scenario["caller"]
            fields(caller, ["accountId", "seed", "amount"], ["accessKey", "keyType"])
            identifier = account_id(caller["accountId"], "synthetic caller")
            if identifier == "system":
                raise ValueError("system is reserved for protocol receipts, not a synthetic caller")
            if identifier in {row["accountId"] for row in rows}:
                raise ValueError("synthetic caller overlaps a captured account")
            if not isinstance(caller["seed"], str) or not caller["seed"]:
                raise ValueError("provide an explicit synthetic caller seed")
            signing = dict(signerId=identifier, seed=caller["seed"], transactions=specifications)
            if "keyType" in caller:
                if not isinstance(caller["keyType"], str) or caller["keyType"] not in {"ed25519", "secp256k1"}:
                    raise ValueError("unsupported synthetic key type")
                signing["keyType"] = caller["keyType"]
            signed = native_call(native, "--sign-transactions", signing)
            usage = config["transaction_costs"]["storage_usage_config"]
            caller_key = caller.get("accessKey", dict(nonce=0, permission="FullAccess"))
            if caller_key is not None:
                access_key(caller_key)
            caller_row = dict(accountId=identifier, amount=amount(caller["amount"], "synthetic balance"), locked="0",
                storageUsage=usage["num_bytes_account"], code=None, keys=[] if caller_key is None else [
                    dict(publicKey=signed["publicKey"], accessKey=caller_key)], storage=[])
            if caller_key is not None:
                # Measure the actual native AccessKey encoding, including variable permissions.
                sizing = native_call(native, "--encode-state", {"accounts": [caller_row]})["initialEntries"]
                if len(sizing) != 2 or sizing[0][0][0] != 0 or sizing[1][0][0] != 2:
                    raise ValueError("unexpected native account/access-key sizing records")
                caller_row["storageUsage"] += usage["num_extra_bytes_record"] + len(signed["publicKeyBorsh"]) + len(sizing[1][1])
            rows.append(caller_row)
        elif specifications:
            raise ValueError("transactions require an explicitly funded synthetic caller")
        encoded = native_call(native, "--encode-state", {"accounts": rows})
        keys = dict(encoded["publicKeys"])
        if signed:
            keys.update(signed["actionPublicKeys"])
            keys[signed["publicKey"]] = signed["publicKeyBorsh"]
        expected_hashes = {row["accountId"]: EMPTY_CODE_HASH if row["code"] is None else code_hash(bytes(row["code"])) for row in rows}
        if encoded["codeHashes"] != expected_hashes:
            raise ValueError("native code hashes disagree with captured bytes")
        model_blocks, native_blocks, offset = [], [], 0
        for block, count in zip(scenario["blocks"], counts):
            transactions = [] if signed is None else signed["transactions"][offset:offset + count]
            offset += count
            native_block = copy.deepcopy(prototype)
            native_block.update({k: v for k, v in block.items() if k != "transactions"})
            native_block["transactions"] = [row["borsh"] for row in transactions]
            native_blocks.append(native_block)
            model_block = {k: block[k] for k in ("blockHeight", "blockTimestamp", "epochHeight", "gasPrice", "gasLimit", "randomSeed", "incomingIndices")}
            model_block["transactions"] = []
            for row in transactions:
                tx = dict(signerId=row["view"]["signer_id"], receiverId=row["view"]["receiver_id"],
                    nonce=row["view"]["nonce"], publicKey=signed["publicKeyBorsh"],
                    actions=[action(a, keys, codes) for a in row["actions"]])
                if row["version"] == 1:
                    if row["view"].get("nonce_index") is not None:
                        raise ValueError("gas-key nonce lanes are not represented by this importer")
                    tx.update(version=1, nonceMode=row["view"].get("nonce_mode", "monotonic"))
                model_block["transactions"].append(tx)
            model_blocks.append(model_block)
        catalogue, wasm_tools = [], None
        (stage / "codes").mkdir()
        if codes:
            executable = shutil.which("wasm-tools")
            if executable is None:
                raise ValueError("wasm-tools 1.251.0 is required for captured contract code")
            frozen_tools = temporary / "wasm-tools"
            shutil.copy2(executable, frozen_tools)
            tool_version = subprocess.check_output([str(frozen_tools), "--version"], text=True).strip()
            if tool_version != "wasm-tools 1.251.0":
                raise ValueError("expected wasm-tools 1.251.0")
            wasm_tools = dict(version=tool_version, sha256=file_digest(frozen_tools))
            for label, blob in sorted(codes.items()):
                if not blob.startswith(b"\0asm\1\0\0\0"):
                    raise ValueError("catalogue code must be a Wasm v1 module")
                code_path, wat_path = Path(f"codes/{label}.wasm"), Path(f"codes/{label}.wat")
                (stage / code_path).write_bytes(blob)
                subprocess.run([str(frozen_tools), "validate", str(stage / code_path)], check=True, capture_output=True)
                wat = subprocess.check_output([str(frozen_tools), "print", str(stage / code_path)], text=True)
                (stage / wat_path).write_text(wat)
                catalogue.append(dict(hash=label, codePath=code_path.as_posix(), watPath=wat_path.as_posix()))
        native_request = dict(formatVersion=1, protocolVersion=version, initialEntries=encoded["initialEntries"], pendingReceipts=[], blocks=native_blocks)
        native_initial_request = {**native_request, "blocks": []}
        native_zero = execute(native, native_initial_request, stage)
        projected = initial_state(native_zero, encoded["publicKeys"], codes)
        expected = dict(accounts=[], accessKeys=[], storage=[], postponed=[], pendingDataCount=[], postponedByData=[], receivedData=[], delayed=[], nextId=1)
        for row in rows:
            expected["accounts"].append([row["accountId"], dict(amount=row["amount"], locked=row["locked"], storageUsage=row["storageUsage"],
                codeHash=None if row["code"] is None else expected_hashes[row["accountId"]])])
            expected["accessKeys"].extend([[[row["accountId"], key_bytes(k["publicKey"], keys)], access_key(k["accessKey"])] for k in row["keys"]])
            if row["storage"]:
                expected["storage"].append([row["accountId"], row["storage"]])
        expected = canonical_state(expected)
        if projected != expected:
            raise ValueError("native encoded state differs from captured account projection")
        model_request = dict(formatVersion=1, protocolVersion=version, configDir="configs", codes=catalogue,
            initialState=expected, pendingReceipts=[], blocks=model_blocks)
        model_zero = execute(lean, {**model_request, "blocks": []}, stage)
        if (canonical_state(model_zero["initialState"]) != expected or model_zero["initialPendingReceipts"]
                or model_zero["blocks"] or not model_zero["quiescent"]):
            raise ValueError("Lean initial state differs from the captured account projection")
        registered_request = {**model_request, "schedulerInputs": [
            {key: block[key] for key in ["congestionInfo", "bandwidthRequests"]} for block in native_blocks], "transactionBlockHashes": [
            [tx.get("blockHash", block["prevBlockHash"]) for tx in block["transactions"]] for block in scenario["blocks"]]}
        registered_zero = execute(registered, {**registered_request, "blocks": [], "transactionBlockHashes": [], "schedulerInputs": []}, stage)
        if (canonical_state(registered_zero["initialState"]) != expected or registered_zero["initialPendingReceipts"]
                or registered_zero["blocks"] or not registered_zero["quiescent"] or registered_zero.get("nativeActionRandomness") is not True):
            raise ValueError("registered initial state differs from the captured account projection")
        if canonical_entries(registered_zero["initialEntries"]) != canonical_entries(represented_entries(native_zero["initialState"]["entries"])):
            raise ValueError("registered initial trie bytes differ from native represented records")
        write_json(stage / "snapshot.json", snapshot)
        write_json(stage / "scenario.json", scenario)
        write_json(stage / "native.json", native_request, compact=True)
        write_json(stage / "model.json", model_request, compact=True)
        write_json(stage / "registered.json", registered_request, compact=True)
        write_json(stage / "native-initial.json", native_zero, compact=True)
        write_json(stage / "model-initial.json", model_zero, compact=True)
        write_json(stage / "registered-initial.json", registered_zero, compact=True)
        files = {str(path.relative_to(stage)): file_digest(path) for path in sorted(stage.rglob("*")) if path.is_file()}
        rpc_config = snapshot["protocol_config"].get("runtime_config")
        model_view = {k: v for k, v in config.items() if k not in {"runtime_finance", "runtime_admission"}}
        manifest = dict(format="safe-near-chain-fixture-v1", genesisProjectionMatches=True, representedGenesisBytesMatch=True,
            executionComparisonEstablished=False, historicalReplayEstablished=False,
            capturedBlock=dict(hash=snapshot["block"]["header"]["hash"], height=snapshot["block"]["header"]["height"]),
            capturedAccounts=sorted(entry["account_id"] for entry in snapshot["accounts"]), syntheticCaller=scenario.get("caller"),
            scope=dict(selectedAccountsOnly=True, missingAccountsAbsentInSyntheticGenesis=True,
                queuesExplicitlyEmpty=True, stateProofsVerified=False, originalRawTrieCaptured=False),
            capturedRpcConfigMatchesPinnedView=rpc_config == model_view,
            capturedRpcConfigSha256=digest(json.dumps(rpc_config, sort_keys=True).encode()),
            referenceBuild=build, modelBinarySha256=file_digest(lean), registeredModelBinarySha256=file_digest(registered),
            defaultExecutionMode="registered", wasmTools=wasm_tools, files=files)
        write_json(stage / "manifest.json", manifest)
        publish(stage, destination)
        return manifest


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--scenario", type=Path)
    parser.add_argument("--reference", type=Path, default=HERE / "target/near-apply-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/chain/.lake/build/bin/chain-replay", help="direct frontend for typed genesis validation")
    parser.add_argument("--registered-model", type=Path, default=REGISTERED_MODEL)
    args = parser.parse_args()
    snapshot = json.loads(args.snapshot.read_text())
    scenario = None if args.scenario is None else json.loads(args.scenario.read_text())
    result = prepare(snapshot, args.destination, reference=args.reference.resolve(), model=args.model.resolve(), scenario=scenario, registered_model=args.registered_model.resolve())
    print(f"Prepared {len(result['capturedAccounts'])} captured accounts; initial native/Lean projections match.")
    print(f"Fixture: {args.destination.resolve()}")
    print("Synthetic genesis; no historical replay or execution equivalence claimed.")


if __name__ == "__main__":
    main()
