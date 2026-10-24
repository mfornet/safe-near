"""Bundle -> Lean ``registered-replay`` request, and the field-by-field comparison of its answer.

The Lean runtime's input is a *represented* model: accounts, access keys, contract storage, callback
queues and a code catalogue, with model counters for receipt and data ids.  A bundle is the raw shard
state.  ``convert`` maps the second onto the first and is strict about it: whatever the model cannot
express is reported as a *blocker* (``Unsupported``) rather than approximated, and after converting,
Lean's own encoding of the converted state must reproduce the bundle's pre-state entries exactly.

Nothing here edits an expected value to agree with Lean; ``replay`` only reads ``bundle["expected"]``.
"""

from __future__ import annotations

import base64
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

import corpus

HERE = Path(__file__).resolve().parent
ROOT = corpus.ROOT
sys.path.insert(0, str(ROOT / "tools"))
import nearcodec as nc  # noqa: E402

CONFIG_DIR = ROOT / "near-lean/vm/configs"
EMPTY_CODE_HASH = "1" * 32

# columns of the raw trie the Lean state model has a place for
MODEL_COLUMNS = {0, 1, 2, 3, 4, 5, 6, 7, 9}
SCHEDULER_COLUMN = 15
UNREPRESENTED_ACTIONS = {
    "Delegate": "action Delegate (meta transaction)",
    "DelegateV2": "action DelegateV2 (meta transaction with gas keys)",
    "DeployGlobalContract": "action DeployGlobalContract",
    "UseGlobalContract": "action UseGlobalContract",
    "DeterministicStateInit": "action DeterministicStateInit",
    "TransferToGasKey": "action TransferToGasKey",
    "WithdrawFromGasKey": "action WithdrawFromGasKey",
}
HOSTS_NEEDING_EPOCH = {"validator_stake": "host function validator_stake (needs the epoch's validator set)",
                       "validator_total_stake": "host function validator_total_stake (needs the epoch's validator set)"}


class Unsupported(Exception):
    def __init__(self, reasons: list[str]):
        super().__init__("; ".join(reasons))
        self.reasons = reasons


class Mismatch(Exception):
    def __init__(self, field: str, blockers: list[str] | None = None):
        super().__init__(field)
        self.field, self.blockers = field, blockers or []


class Replayed:
    def __init__(self, blockers: list[str]):
        self.blockers = blockers


def column(key_hex: str) -> int:
    return int(key_hex[:2], 16)


def column_name(number: int) -> str:
    return corpus.COLUMN_NAMES.get(number, str(number))


def b58(text: str) -> bytes:
    return nc.b58decode(text)


def public_key(text: str) -> list[int]:
    kind, body = text.split(":", 1)
    prefix = {"ed25519": 0, "secp256k1": 1}.get(kind)
    if prefix is None:
        raise Unsupported([f"public key type {kind}"])
    return [prefix] + list(b58(body))


def view_action_kinds(actions) -> list[str]:
    return corpus.action_kinds(actions)


# --- static analysis -------------------------------------------------------------
def blockers(bundle: dict) -> list[str]:
    """Features of this chunk the Lean model cannot express, most fundamental first."""
    found: list[str] = []
    context, inputs, expected = bundle["context"], bundle["inputs"], bundle["expected"]
    if len(context["congestionInfo"]) > 1:
        found.append("multi-shard layout (the chunk model assumes the single-shard reference layout)")
    for number in sorted({column(key) for key, _ in bundle["preState"]["entries"]}):
        if number not in MODEL_COLUMNS and number != SCHEDULER_COLUMN:
            found.append(f"pre-state column {column_name(number)}")
    kinds: list[str] = []
    for row in inputs["transactions"]:
        view = row["view"]
        kinds += view_action_kinds(view.get("actions", []))
        if not row["valid"]:
            found.append("transaction rejected by chunk validity (no model of invalid-transaction outcomes)")
        if view.get("nonce_index") is not None:
            found.append("gas-key nonce index")
    for view in inputs["incomingReceiptViews"]:
        payload = view["receipt"]
        kind = next(iter(payload))
        if kind not in ("Action", "Data"):
            found.append(f"receipt kind {kind}")
        if kind == "ActionV2" or (kind == "Action" and False):
            found.append("receipt kind ActionV2 (refund_to)")
        if kind == "Action":
            kinds += view_action_kinds(payload["Action"].get("actions", []))
    for kind in dict.fromkeys(kinds):
        if kind in UNREPRESENTED_ACTIONS:
            found.append(UNREPRESENTED_ACTIONS[kind])
    if context["validatorAccountsUpdate"] is not None:
        found.append("epoch boundary: validator accounts update (rewards, stake return)")
    for outcome in expected["outcomes"]:
        for entry in (outcome["view"].get("metadata") or {}).get("gas_profile") or []:
            host = corpus.host_function(entry["cost"]) if entry.get("cost_category") == "WASM_HOST_COST" else None
            if host in HOSTS_NEEDING_EPOCH:
                found.append(HOSTS_NEEDING_EPOCH[host])
    return list(dict.fromkeys(found))


# --- decoding ----------------------------------------------------------------------
# --- conversion -----------------------------------------------------------------------
sys.path.insert(0, str(ROOT / "tools/chain-conformance"))
import import_snapshot as importer  # noqa: E402  (action and access-key views -> model JSON)
from compare_fixture import PublicKeys  # noqa: E402

MODEL_ACTIONS = {"CreateAccount", "DeployContract", "FunctionCall", "Transfer", "Stake", "AddKey", "DeleteKey",
                 "DeleteAccount"}


def model_action_blockers(kinds: list[str]) -> list[str]:
    found = []
    for kind in dict.fromkeys(kinds):
        if kind not in MODEL_ACTIONS:
            found.append(UNREPRESENTED_ACTIONS.get(kind, f"action {kind}"))
    return found


def read_string(raw: bytes, at: int) -> tuple[str, int]:
    length = int.from_bytes(raw[at:at + 4], "little")
    return raw[at + 4:at + 4 + length].decode(), at + 4 + length


def receipt_format(raw: bytes) -> tuple[str, bool]:
    """('legacy' | 'v2' | 'data' | other, has_refund_to) from the Borsh header of an incoming receipt."""
    _, at = read_string(raw, 0)
    _, at = read_string(raw, at)
    at += 32
    tag = raw[at]
    if tag == 0:
        return "legacy", False
    if tag == 1:
        return "data", False
    if tag == 5:
        _, after = read_string(raw, at + 1)
        return "v2", raw[after] == 1
    return f"tag {tag}", False


def transaction_block_hash(raw: bytes) -> list[int]:
    """The block hash inside a V0/V1 Borsh transaction: after signer, key, nonce and receiver."""
    v1 = raw[1] != 0            # nearcore: a zero second byte is the high byte of a V0 account id length
    at = 1 if v1 else 0
    _, at = read_string(raw, at)
    at += 33 if raw[at] == 0 else 65
    if v1:                      # TransactionNonce: Nonce{nonce} or GasKeyNonce{nonce, index}
        at += 9 if raw[at] == 0 else 11
    else:
        at += 8
    _, at = read_string(raw, at)
    return list(raw[at:at + 32])


class Converter:
    """One bundle -> one registered-replay request; fills ``codes`` on disk under ``workdir``."""

    def __init__(self, bundle: dict, decoded: dict, workdir: Path):
        self.bundle, self.decoded, self.workdir = bundle, decoded, workdir
        self.keys = PublicKeys()
        self.codes: dict[str, bytes] = {}
        self.next_id = 1
        self.receipt_ids: dict[str, int] = {}
        self.data_ids: dict[str, int] = {}
        self.data_receivers: dict[str, str] = {}
        self.reasons: list[str] = []

    def fresh(self, table: dict, name: str) -> int:
        if name not in table:
            table[name] = self.next_id
            self.next_id += 1
        return table[name]

    def action(self, view) -> dict:
        return importer.action(view, self.keys, self.codes)

    def model_receipt(self, view: dict, typed: dict, raw: bytes) -> tuple[dict, str]:
        kind, refund = receipt_format(raw)
        payload = view["receipt"]
        variant = next(iter(payload))
        if kind == "data":
            data = payload["Data"]
            if data.get("is_promise_resume"):
                raise Unsupported(["receipt kind PromiseResume"])
            identifier = self.fresh(self.data_ids, data["data_id"])
            self.data_receivers[data["data_id"]] = view["receiver_id"]
            body = {"kind": "data", "dataId": identifier,
                    "data": None if data["data"] is None else list(base64.b64decode(data["data"]))}
        elif kind in ("legacy", "v2") and variant == "Action":
            if refund:
                raise Unsupported(["receipt with an explicit refund_to"])
            action = payload["Action"]
            if action.get("is_promise_yield"):
                raise Unsupported(["receipt kind PromiseYield"])
            for output in action["output_data_receivers"]:
                self.data_receivers[output["data_id"]] = output["receiver_id"]
            for name in action["input_data_ids"]:
                self.data_receivers[name] = view["receiver_id"]
            body = {"kind": "action", "signerId": action["signer_id"],
                    "signerPublicKey": self.keys[action["signer_public_key"]], "gasPrice": action["gas_price"],
                    "inputDataIds": [self.fresh(self.data_ids, name) for name in action["input_data_ids"]],
                    "outputDataReceivers": [[self.fresh(self.data_ids, o["data_id"]), o["receiver_id"]]
                                            for o in action["output_data_receivers"]],
                    "actions": [self.action(a) for a in next(iter(typed["receipt"].values()))["actions"]]}
        else:
            raise Unsupported([f"receipt kind {variant} ({kind})"])
        identifier = self.fresh(self.receipt_ids, view["receipt_id"])
        return {"predecessorId": view["predecessor_id"], "receiverId": view["receiver_id"], "receiptId": identifier,
                "receipt": body}, kind

    def state(self) -> tuple[dict, dict | None, dict]:
        """Model state from the decoded pre-state records; also the delayed-queue header and the scheduler."""
        accounts, keys, storage, contracts = [], [], {}, {}
        for row in self.decoded["preState"]:
            if "decodeError" in row:
                raise Unsupported([f"pre-state record that upstream cannot decode ({row['decodeError']})"])
            if row.get("opaque"):
                continue
            kind, value = next(iter(row["record"].items()))
            if kind == "Account":
                account = value["account"]
                extra = set(account) - {"amount", "locked", "code_hash", "storage_usage", "version"}
                if extra or account.get("version") != "V1":
                    raise Unsupported([f"account with fields {sorted(extra) or account.get('version')} (global contract use)"])
                accounts.append([value["account_id"], {"amount": account["amount"], "locked": account["locked"],
                                                       "storageUsage": account["storage_usage"],
                                                       "codeHash": None if account["code_hash"] == EMPTY_CODE_HASH else account["code_hash"]}])
            elif kind == "AccessKey":
                keys.append([[value["account_id"], list(self.keys[value["public_key"]])], importer.access_key(value["access_key"])])
            elif kind == "Data":
                storage.setdefault(value["account_id"], []).append(
                    [list(base64.b64decode(value["data_key"])), list(base64.b64decode(value["value"]))])
            elif kind == "Contract":
                blob = base64.b64decode(value["code"])
                label = nc.b58encode(hashlib.sha256(blob).digest())
                self.codes[label] = blob
                contracts[value["account_id"]] = label
            elif kind in ("PostponedReceipt", "PostponedReceiptId", "PendingDataCount", "ReceivedData", "DelayedReceipt"):
                raise Unsupported([f"pre-state callback or delayed-queue record {kind}"])
            else:
                raise Unsupported([f"pre-state record {kind}"])
        for identifier, account in accounts:
            label = account["codeHash"]
            if (contracts.get(identifier) or None) != label:
                raise Unsupported(["account code hash without a matching contract record"])
        state = {"accounts": accounts, "accessKeys": keys,
                 "storage": [[name, sorted(rows)] for name, rows in sorted(storage.items())],
                 "postponed": [], "pendingDataCount": [], "postponedByData": [], "receivedData": [], "delayed": [],
                 "nextId": 1}
        entries = {key: value for key, value in self.bundle["preState"]["entries"]}
        header = entries.get("07")
        delayed = None
        if header is not None:
            raw = bytes.fromhex(header)
            first, last = int.from_bytes(raw[:8], "little"), int.from_bytes(raw[8:16], "little")
            if first != last or len(raw) != 16:
                raise Unsupported(["pre-state delayed receipt queue"])
            delayed = {"firstIndex": first, "forms": []}
        scheduler = None
        value = entries.get("0f")
        if value is not None:
            raw = bytes.fromhex(value)
            if len(raw) != 61 or raw[0] != 0 or int.from_bytes(raw[1:5], "little") != 1:
                raise Unsupported(["bandwidth scheduler state with more than one link"])
            scheduler = {"allowance": int.from_bytes(raw[21:29], "little"), "sanity": list(raw[29:61])}
        return state, delayed, scheduler

    def build(self) -> dict:
        bundle, context, inputs = self.bundle, self.bundle["context"], self.bundle["inputs"]
        state, delayed, scheduler = self.state()
        transactions, hashes = [], []
        for row in inputs["transactions"]:
            view = row["view"]
            raw = bytes.fromhex(row["borsh"])
            tx = {"signerId": view["signer_id"], "receiverId": view["receiver_id"], "nonce": view["nonce"],
                  "publicKey": list(self.keys[view["public_key"]]), "actions": [self.action(a) for a in row["actions"]]}
            if raw[0] == 1 and int.from_bytes(raw[:4], "little") != len(view["signer_id"]):
                tx.update(version=1, nonceMode=view.get("nonce_mode", "monotonic"))
            transactions.append(tx)
            hashes.append(transaction_block_hash(raw))
        pending, formats = [], []
        for view, typed, raw in zip(inputs["incomingReceiptViews"], inputs["incomingReceiptTyped"], inputs["incomingReceipts"]):
            receipt, kind = self.model_receipt(view, typed, bytes.fromhex(raw))
            pending.append(receipt)
            if kind in ("legacy", "v2"):
                formats.append([receipt["receiptId"], kind])
        state["nextId"] = self.next_id
        registry = {"receiptIds": [[identifier, list(b58(name))] for name, identifier in self.receipt_ids.items()],
                    "dataIds": [{"id": identifier, "hash": list(b58(name)), "receiverId": self.data_receivers[name]}
                                for name, identifier in self.data_ids.items()],
                    "actionFormats": formats, "delayed": delayed}
        catalogue = []
        (self.workdir / "codes").mkdir(parents=True, exist_ok=True)
        for label, blob in sorted(self.codes.items()):
            path = self.workdir / "codes" / f"{label}.wasm"
            path.write_bytes(blob)
            catalogue.append({"hash": label, "codePath": str(path), "watPath": str(path)})
        request = {
            "formatVersion": 1, "protocolVersion": context["currentProtocolVersion"], "configDir": str(CONFIG_DIR),
            "codes": catalogue, "initialState": state, "pendingReceipts": pending,
            "blocks": [{"blockHeight": context["blockHeight"], "blockTimestamp": context["blockTimestamp"],
                        "epochHeight": context["epochHeight"], "gasPrice": context["gasPrice"],
                        "gasLimit": context["gasLimit"], "randomSeed": list(bytes.fromhex(context["randomSeed"])),
                        "transactions": transactions, "incomingIndices": None}],
            "transactionBlockHashes": [hashes], "queueContext": registry,
            "schedulerInputs": [{"congestionInfo": [[shard, list(bytes.fromhex(info)), missed]
                                                    for shard, info, missed in context["congestionInfo"]],
                                 "bandwidthRequests": list(bytes.fromhex(context["bandwidthRequests"]))}],
        }
        if scheduler is not None:
            request["initialScheduler"] = scheduler
        return request


def run_lean(binary: Path, request: dict, workdir: Path) -> dict:
    result = subprocess.run([str(binary)], input=json.dumps(request), text=True, capture_output=True, cwd=workdir)
    if result.returncode != 0:
        raise Unsupported([f"Lean rejected the converted request: {result.stderr.strip()[:160]}"])
    return json.loads(result.stdout)


def entry_map(rows) -> dict[bytes, bytes]:
    return {bytes(key): bytes(value) for key, value in rows}


def expected_post_state(bundle: dict) -> dict[bytes, bytes]:
    state = {bytes.fromhex(key): bytes.fromhex(value) for key, value in bundle["preState"]["entries"]}
    for key, value in bundle["expected"]["stateDiff"]:
        if value is None:
            state.pop(bytes.fromhex(key), None)
        else:
            state[bytes.fromhex(key)] = bytes.fromhex(value)
    return state


def describe_key(key: bytes) -> str:
    return column_name(key[0]) if key else "empty key"


def first_state_difference(expected: dict[bytes, bytes], actual: dict[bytes, bytes], where: str) -> str | None:
    for key in sorted(set(expected) | set(actual)):
        if key not in actual:
            return f"{where}: {describe_key(key)} entry missing in Lean ({key.hex()[:48]})"
        if key not in expected:
            return f"{where}: {describe_key(key)} entry unexpected in Lean ({key.hex()[:48]})"
        if expected[key] != actual[key]:
            return f"{where}: {describe_key(key)} value differs ({key.hex()[:48]})"
    return None


def expected_outcomes(bundle: dict) -> list[dict]:
    rows = []
    transactions = bundle["inputs"]["transactions"]
    for index, outcome in enumerate(bundle["expected"]["outcomes"]):
        view = outcome["view"]
        status = view["status"]
        if isinstance(status, dict) and "SuccessValue" in status:
            shown = ["value", list(base64.b64decode(status["SuccessValue"]))]
        elif isinstance(status, dict) and "SuccessReceiptId" in status:
            shown = ["receipt", b58(status["SuccessReceiptId"]).hex()]
        elif isinstance(status, dict) and "Failure" in status:
            shown = ["failure"]
        else:
            shown = [str(status)]
        rows.append({"id": outcome["id"], "executor": view["executor_id"], "status": shown, "logs": view["logs"],
                     "receiptIds": [b58(r).hex() for r in view["receipt_ids"]], "gasBurnt": view["gas_burnt"],
                     "tokensBurnt": int(view["tokens_burnt"])})
    return rows


def lean_outcomes(trace: dict, request: dict) -> list[dict]:
    native = {identifier: bytes(raw).hex() for identifier, raw in trace["registry"]["receiptIds"]}
    transaction_hashes = [bytes(row["hash"]).hex() for row in trace["transactionIdentities"]]
    rows = []
    for index, row in enumerate(trace["execution"]["outcomes"]):
        outcome = row["outcome"]
        status = outcome["status"]
        if status["kind"] == "successValue":
            shown = ["value", status["value"]]
        elif status["kind"] == "successReceiptId":
            shown = ["receipt", native.get(status["receiptId"], f"model {status['receiptId']}")]
        else:
            shown = ["failure"]
        identifier = transaction_hashes[index] if index < len(transaction_hashes) else native.get(row["id"], f"model {row['id']}")
        rows.append({"id": identifier, "executor": outcome["executorId"], "status": shown, "logs": outcome["logs"],
                     "receiptIds": [native.get(r, f"model {r}") for r in outcome["receiptIds"]],
                     "gasBurnt": outcome["gasBurnt"], "tokensBurnt": int(outcome["tokensBurnt"])})
    return rows


def compare(bundle: dict, request: dict, answer: dict, extra: list[str]) -> None:
    """Raise Mismatch with the first differing field; the bundle's expected values are never altered."""
    trace = answer["blocks"][0] if answer["blocks"] else None
    if answer["stop"] == "executionIssue" and trace is not None:
        issue = trace["execution"].get("issue") or {}
        raise Mismatch("model execution issue: " + str(issue.get("message", issue)), extra)
    if answer["stop"] != "blocksExhausted" or trace is None:
        raise Mismatch(f"stop: {answer['stop']}", extra)
    expected = bundle["expected"]
    if not trace.get("admissionCommitted", False):
        raise Mismatch("execution: model execution issue " + json.dumps(trace["execution"].get("issue"))[:120], extra)
    for index, row in enumerate(trace["transactionIdentities"]):
        if bytes(row["hash"]).hex() != bundle["inputs"]["transactions"][index]["hash"]:
            raise Unsupported(["transaction body re-encoded by Lean hashes differently"])
    want, got = expected_outcomes(bundle), lean_outcomes(trace, request)
    if len(want) != len(got):
        raise Mismatch(f"outcomes (count {len(want)} != {len(got)})", extra)
    for index, (left, right) in enumerate(zip(want, got)):
        for field in ("id", "executor", "status", "logs", "receiptIds", "gasBurnt", "tokensBurnt"):
            if left[field] != right[field]:
                raise Mismatch(f"outcomes[{index}].{field}", extra)
    outgoing = [bytes(row["bytes"]).hex() for row in trace["outgoingBytes"]]
    if len(outgoing) != len(expected["outgoingReceipts"]):
        raise Mismatch(f"outgoingReceipts (count {len(expected['outgoingReceipts'])} != {len(outgoing)})", extra)
    for index, (left, right) in enumerate(zip(expected["outgoingReceipts"], outgoing)):
        if left != right:
            raise Mismatch(f"outgoingReceipts[{index}]", extra)
    stats = expected["balanceStats"]
    burnt = int(stats["txBurnt"]) + int(stats["otherBurnt"]) + int(stats["slashedBurnt"])
    if int(trace["execution"]["tokensBurnt"]) != burnt:
        raise Mismatch("balanceStats.burnt", extra)
    if int(trace["execution"]["subsidizedAmount"]) != int(stats["subsidized"]):
        raise Mismatch("balanceStats.subsidized", extra)
    difference = first_state_difference(expected_post_state(bundle), entry_map(trace["chunkEntries"]), "postState")
    if difference:
        raise Mismatch(difference, extra)


def replay(bundle: dict, binary: Path) -> Replayed:
    found = blockers(bundle)
    kinds = [kind for row in bundle["inputs"]["transactions"] for kind in view_action_kinds(row["view"].get("actions", []))]
    kinds += [kind for view in bundle["inputs"]["incomingReceiptViews"]
              for kind in view_action_kinds(view["receipt"].get("Action", {}).get("actions", []))]
    found = list(dict.fromkeys(found + model_action_blockers(kinds)))
    if found:
        raise Unsupported(found)
    decoded = bundle.get("decoded") or corpus.checker_decode(bundle)
    with tempfile.TemporaryDirectory(prefix="safe-near-lean-") as temporary:
        workdir = Path(temporary)
        converter = Converter(bundle, decoded, workdir)
        request = converter.build()
        # Lean must rebuild the chunk's complete pre-state, byte for byte, from the converted model.
        initial = run_lean(binary, dict(request, blocks=[], transactionBlockHashes=[], schedulerInputs=[]), workdir)
        rebuilt = entry_map(initial["initialEntries"] + initial["initialSchedulerEntries"])
        original = {bytes.fromhex(k): bytes.fromhex(v) for k, v in bundle["preState"]["entries"]}
        difference = first_state_difference(original, rebuilt, "pre-state")
        if difference:
            raise Unsupported([f"pre-state not reproduced by the Lean encoding: {difference}"])
        answer = run_lean(binary, request, workdir)
        compare(bundle, request, answer, found)
    return Replayed(found)
