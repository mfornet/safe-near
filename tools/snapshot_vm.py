#!/usr/bin/env python3
"""Compare VM executors on hypothetical calls seeded from a captured NEAR account.

This imports complete account storage, code and block context from near_snapshot.py.
It does not replay an on-chain transaction or execute outgoing receipts.
"""

import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile

from near_snapshot import code_hash, decode, write_snapshot


ROOT = Path(__file__).resolve().parents[1]


def uint(value, bits, label):
    if type(value) is not int or not 0 <= value < 2 ** bits:
        raise ValueError(f"{label} must be an unsigned {bits}-bit integer")
    return value


def amount(value, label):
    if not isinstance(value, str) or not re.fullmatch(r"0|[1-9][0-9]*", value):
        raise ValueError(f"{label} must be a decimal amount string")
    uint(int(value), 128, label)
    return value


def byte_list(value, label, length=None):
    if not isinstance(value, list) or any(type(b) is not int or not 0 <= b <= 255 for b in value):
        raise ValueError(f"{label} must be a list of bytes")
    if length is not None and len(value) != length:
        raise ValueError(f"{label} must contain {length} bytes")
    return value


def account_id(value, label):
    if not isinstance(value, str) or not 2 <= len(value) <= 64 or not re.fullmatch(
            r"[a-z0-9]+(?:[._-][a-z0-9]+)*", value):
        raise ValueError(f"{label} must be a NEAR account ID")
    return value


def storage_pairs(values):
    if not isinstance(values, list):
        raise ValueError("storage must be a list")
    seen = set()
    result = []
    for item in values:
        if not isinstance(item, (list, tuple)) or len(item) != 2:
            raise ValueError("storage entries must be key/value pairs")
        key, value = byte_list(item[0], "storage key"), byte_list(item[1], "storage value")
        if bytes(key) in seen:
            raise ValueError("duplicate storage key")
        seen.add(bytes(key))
        result.append([key, value])
    return sorted(result, key=lambda item: item[0])


def seed(snapshot, selected):
    if snapshot.get("format") != "safe-near-snapshot-v1":
        raise ValueError("unsupported snapshot format")
    selected = account_id(selected, "selected account")
    entries = [entry for entry in snapshot["accounts"] if entry["account_id"] == selected]
    if len(entries) != 1:
        raise ValueError("selected account must occur exactly once in the snapshot")
    entry = entries[0]
    storage = entry["storage"]
    if storage.get("complete") is not True or storage.get("prefixes_base64") != [""]:
        raise ValueError("VM replay requires complete account storage; filtered keys are unknown")
    account, code = entry["account"], entry["code"]
    if account.get("global_contract_hash") or account.get("global_contract_account_id"):
        raise ValueError("global contract code is not supported")
    if not code:
        raise ValueError("selected account has no deployed code")
    binary = decode(code["code_base64"])
    if code_hash(binary) != code["hash"] or code["hash"] != account["code_hash"]:
        raise ValueError("snapshot code hash mismatch")
    if not binary.startswith(b"\x00asm\x01\x00\x00\x00"):
        raise ValueError("expected a Wasm version 1 binary module")
    pairs = storage_pairs([[list(decode(item["key"])), list(decode(item["value"]))]
                           for item in storage["values"]])
    header = snapshot["block"]["header"]
    context = {
        "currentAccountId": selected,
        "accountLockedBalance": amount(account["locked"], "account locked balance"),
        "blockHeight": uint(header["height"], 64, "block height"),
        "blockTimestamp": uint(int(header["timestamp_nanosec"]), 64, "block timestamp"),
        "protocolVersion": uint(snapshot["protocol_config"]["protocol_version"], 32, "protocol version"),
    }
    state = {"balance": amount(account["amount"], "account balance"),
             "storageUsage": uint(account["storage_usage"], 64, "storage usage"), "storage": pairs}
    return binary, context, state


def validate_calls(scenario):
    # Receipt-specific seed and epoch height are explicit trusted inputs. Neither
    # is silently inferred from a block's random_value or its epoch ID.
    unknown = set(scenario) - {"epochHeight", "randomSeed", "calls"}
    if unknown:
        raise ValueError(f"unknown scenario fields: {sorted(unknown)}")
    epoch = uint(scenario["epochHeight"], 64, "scenario epochHeight")
    random_seed = byte_list(scenario["randomSeed"], "scenario randomSeed", 32)
    calls = scenario["calls"]
    if not isinstance(calls, list) or not calls:
        raise ValueError("scenario must contain at least one call")
    checked = []
    names = set()
    for call in calls:
        unknown = set(call) - {"name", "method", "input", "args", "signer", "predecessor",
                               "signerPublicKey", "view", "deposit", "gas", "promiseResults",
                               "outputDataReceivers"}
        if unknown:
            raise ValueError(f"unknown call fields: {sorted(unknown)}")
        name = call["name"]
        if not isinstance(name, str) or not name or name in names:
            raise ValueError("call names must be nonempty and unique")
        names.add(name)
        if not isinstance(call["method"], str):
            raise ValueError("method must be a string")
        if ("input" in call) == ("args" in call):
            raise ValueError("provide exactly one of input bytes or JSON args")
        raw = (byte_list(call["input"], "input") if "input" in call else
               list(json.dumps(call["args"], separators=(",", ":"), ensure_ascii=False,
                               allow_nan=False, sort_keys=True).encode()))
        pk = byte_list(call["signerPublicKey"], "signerPublicKey")
        if not ((len(pk) == 33 and pk[0] == 0) or (len(pk) == 65 and pk[0] == 1)):
            raise ValueError("signerPublicKey must be a serialized ed25519 or secp256k1 key")
        if type(call["view"]) is not bool:
            raise ValueError("view must be explicitly true or false")
        promises = call.get("promiseResults", [])
        if not isinstance(promises, list):
            raise ValueError("promiseResults must be a list")
        for value in promises:
            if value is not None:
                byte_list(value, "promise result")
        receivers = call.get("outputDataReceivers", [])
        if not isinstance(receivers, list):
            raise ValueError("outputDataReceivers must be a list")
        for receiver in receivers:
            account_id(receiver, "output data receiver")
        checked.append({"name": name, "request": {
            "method": call["method"], "signerAccountId": account_id(call["signer"], "signer"),
            "predecessorAccountId": account_id(call["predecessor"], "predecessor"),
            "signerAccountPk": pk, "input": raw, "view": call["view"],
            "attachedDeposit": amount(call.get("deposit", "0"), "attached deposit"),
            "prepaidGas": uint(call["gas"], 64, "gas"),
            "epochHeight": epoch, "randomSeed": random_seed,
            "promiseResults": promises, "outputDataReceivers": receivers,
        }})
    return checked


def differences(reference, model, path="$"):
    """Compare every field and preserve missing-vs-null and bool-vs-int differences."""
    if type(reference) is not type(model):
        return [{"path": path, "reference": reference, "model": model}]
    if isinstance(reference, dict):
        result = []
        for key in sorted(reference.keys() | model.keys()):
            if key not in reference or key not in model:
                result.append({"path": f"{path}.{key}", "referencePresent": key in reference,
                               "modelPresent": key in model, "reference": reference.get(key),
                               "model": model.get(key)})
            else:
                result.extend(differences(reference[key], model[key], f"{path}.{key}"))
        return result
    if isinstance(reference, list):
        if len(reference) != len(model):
            return [{"path": path, "reference": reference, "model": model}]
        return [diff for index, (left, right) in enumerate(zip(reference, model))
                for diff in differences(left, right, f"{path}[{index}]")]
    return [] if reference == model else [{"path": path, "reference": reference, "model": model}]


def compare(snapshot, selected, scenario, *, reference, model, code_path, wat_path, config_dir):
    binary, context, state = seed(snapshot, selected)
    calls = validate_calls(scenario)
    report = {"format": "safe-near-snapshot-vm-v1", "accountId": selected,
              "blockHash": snapshot["block"]["header"]["hash"],
              "codeSha256": hashlib.sha256(binary).hexdigest(),
              "scope": "hypothetical VM calls; receipts are not executed; RPC state is trusted",
              "cases": [], "notRun": []}
    for index, call in enumerate(calls):
        request = {**context, **call["request"], "codePath": str(code_path), "watPath": str(wat_path),
                   "configDir": str(config_dir), "accountBalance": state["balance"],
                   "storageUsage": state["storageUsage"], "storage": state["storage"]}
        record = {"name": call["name"], "request": request}
        try:
            expected = reference(request)
            record["reference"] = expected
            actual = model(request)
            record["model"] = actual
            # Validate the state before feeding it to the next call. A crashed
            # or malformed oracle must never make later cases appear successful.
            state = {"balance": amount(expected["balance"], "reference balance"),
                     "storageUsage": uint(expected["storageUsage"], 64, "reference storage usage"),
                     "storage": storage_pairs(expected["storage"])}
            record["differences"] = differences(expected, actual)
        except (RuntimeError, ValueError, KeyError, TypeError, OSError, subprocess.TimeoutExpired) as error:
            record["executionError"] = str(error)
            record["differences"] = [{"path": "$.execution", "error": str(error)}]
            report["cases"].append(record)
            report["notRun"] = [remaining["name"] for remaining in calls[index + 1:]]
            break
        report["cases"].append(record)
    report["passed"] = sum(not case["differences"] for case in report["cases"])
    report["failed"] = len(report["cases"]) - report["passed"] + len(report["notRun"])
    return report


def run_json(binary, request, timeout):
    process = subprocess.run([str(binary)], input=json.dumps(request) + "\n",
                             text=True, capture_output=True, timeout=timeout)
    if process.returncode:
        raise RuntimeError(f"{binary.name} exited {process.returncode}: {process.stderr.strip()}")
    result = json.loads(process.stdout)
    if not isinstance(result, dict):
        raise ValueError(f"{binary.name} did not return a JSON object")
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("snapshot", type=Path)
    parser.add_argument("account")
    parser.add_argument("scenario", type=Path)
    parser.add_argument("--reference", type=Path,
                        default=ROOT / "tools/runtime-conformance/target/debug/near-runtime-reference")
    parser.add_argument("--model", type=Path, default=ROOT / "near-lean/vm/.lake/build/bin/vm-replay")
    parser.add_argument("--config-dir", type=Path, default=ROOT / "near-lean/vm/configs")
    parser.add_argument("--reference-manifest", type=Path)
    parser.add_argument("--report", type=Path, required=True)
    parser.add_argument("--timeout", type=float, default=120)
    args = parser.parse_args()
    try:
        if args.timeout <= 0:
            raise ValueError("timeout must be positive")
        if args.report.exists():
            raise FileExistsError(f"refusing to overwrite {args.report}")
        snapshot_bytes, scenario_bytes = args.snapshot.read_bytes(), args.scenario.read_bytes()
        snapshot, scenario = json.loads(snapshot_bytes), json.loads(scenario_bytes)
        binary, _, _ = seed(snapshot, args.account)
        validate_calls(scenario)
        provenance, executables = {}, {}
        for label, executable in [("reference", args.reference), ("model", args.model)]:
            executables[label] = executable.read_bytes()
            provenance[label] = {"path": str(executable.resolve()),
                                 "sha256": hashlib.sha256(executables[label]).hexdigest()}
        if provenance["reference"]["sha256"] == provenance["model"]["sha256"]:
            raise ValueError("reference and model must be different executables")
        version = subprocess.check_output(["wasm-tools", "--version"], text=True).strip()
        if version != "wasm-tools 1.251.0":
            raise ValueError(f"expected wasm-tools 1.251.0, got {version}")
        with tempfile.TemporaryDirectory(prefix="safe-near-snapshot-vm-") as directory:
            code, wat = Path(directory) / "contract.wasm", Path(directory) / "contract.wat"
            code.write_bytes(binary)
            # Never run a binary that another agent can replace halfway through
            # a scenario. Freeze the exact bytes whose digests we recorded.
            frozen = {}
            for label, contents in executables.items():
                frozen[label] = Path(directory) / label
                frozen[label].write_bytes(contents)
                frozen[label].chmod(0o700)
            config_dir = Path(directory) / "configs"
            config_dir.mkdir()
            configurations = {}
            for source in sorted(args.config_dir.glob("*.json")):
                contents = source.read_bytes()
                (config_dir / source.name).write_bytes(contents)
                configurations[source.name] = {"sha256": hashlib.sha256(contents).hexdigest(),
                                                "text": contents.decode("utf-8")}
            if not configurations:
                raise ValueError("config directory contains no JSON parameter files")
            subprocess.run(["wasm-tools", "print", str(code), "-o", str(wat)], check=True)
            report = compare(snapshot, args.account, scenario,
                             reference=lambda request: run_json(frozen["reference"], request, args.timeout),
                             model=lambda request: run_json(frozen["model"], request, args.timeout),
                             code_path=code, wat_path=wat, config_dir=config_dir)
            report["wat"] = wat.read_text()
            report["configurationFiles"] = configurations
        report["provenance"] = {"executables": provenance, "wasmTools": version,
                                "snapshotSha256": hashlib.sha256(snapshot_bytes).hexdigest(),
                                "scenarioSha256": hashlib.sha256(scenario_bytes).hexdigest()}
        if args.reference_manifest:
            report["provenance"]["referenceManifest"] = json.loads(args.reference_manifest.read_text())
        write_snapshot(args.report, report)
    except (ValueError, KeyError, TypeError, OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(f"snapshot VM comparison failed: {error}", file=sys.stderr)
        return 2
    print(f"{report['passed']} passed, {report['failed']} differed or did not run; evidence: {args.report}")
    return int(report["failed"] != 0)


if __name__ == "__main__":
    raise SystemExit(main())
