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
MODEL_COLUMNS = {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 18, 19, 20}
SCHEDULER_COLUMN = 15
# the outgoing buffers: indices, receipts, and the receipt group metadata (13, 14, 16, 17) are decoded by Lean itself
BUFFER_COLUMNS = {13, 14, 16, 17}
UNREPRESENTED_ACTIONS = {
    "DeterministicStateInit": "action DeterministicStateInit",
}
# the action views that are spelled differently in the RPC view and in the typed receipt
ACTION_ALIASES = {"DeployGlobalContractByAccountId": "DeployGlobalContract",
                  "UseGlobalContractByAccountId": "UseGlobalContract"}


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


def layout_shard_ids(layout_hex: str) -> list[int]:
    """Shard ids of a Borsh ``ShardLayout::V2`` in layout order (Lean parses and checks the rest)."""
    raw = bytes.fromhex(layout_hex)
    if raw[0] != 2:
        raise Unsupported([f"shard layout version {raw[0]}"])
    at = 5
    for _ in range(int.from_bytes(raw[1:5], "little")):
        at += 4 + int.from_bytes(raw[at:at + 4], "little")
    count = int.from_bytes(raw[at:at + 4], "little")
    return [int.from_bytes(raw[at + 4 + 8 * i:at + 12 + 8 * i], "little") for i in range(count)]


def view_action_kinds(actions) -> list[str]:
    return corpus.action_kinds(actions)


# --- static analysis -------------------------------------------------------------
def blockers(bundle: dict) -> list[str]:
    """Features of this chunk the Lean model cannot express, most fundamental first."""
    found: list[str] = []
    context, inputs, expected = bundle["context"], bundle["inputs"], bundle["expected"]
    for number in sorted({column(key) for key, _ in bundle["preState"]["entries"]}):
        if number not in MODEL_COLUMNS and number != SCHEDULER_COLUMN and number not in BUFFER_COLUMNS:
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
        if kind not in ("Action", "Data", "GlobalContractDistribution"):
            found.append(f"receipt kind {kind}")
        if kind == "ActionV2" or (kind == "Action" and False):
            found.append("receipt kind ActionV2 (refund_to)")
        if kind == "Action":
            kinds += view_action_kinds(payload["Action"].get("actions", []))
    for kind in dict.fromkeys(kinds):
        if kind in UNREPRESENTED_ACTIONS:
            found.append(UNREPRESENTED_ACTIONS[kind])
    return list(dict.fromkeys(found))


# --- decoding ----------------------------------------------------------------------
# --- conversion -----------------------------------------------------------------------
sys.path.insert(0, str(ROOT / "tools/chain-conformance"))
import import_snapshot as importer  # noqa: E402  (action and access-key views -> model JSON)
from compare_fixture import PublicKeys  # noqa: E402

MODEL_ACTIONS = {"CreateAccount", "DeployContract", "FunctionCall", "Transfer", "Stake", "AddKey", "DeleteKey",
                 "DeleteAccount", "Delegate", "DelegateV2", "DeployGlobalContract", "DeployGlobalContractByAccountId",
                 "UseGlobalContract", "UseGlobalContractByAccountId", "TransferToGasKey", "WithdrawFromGasKey"}


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
    if tag == 3:
        return "resume", False
    if tag == 4:
        return "distribution", False
    if tag == 5:
        _, after = read_string(raw, at + 1)
        return "v2", raw[after] == 1
    if tag == 6:
        return "yield", False
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



def delayed_form(raw: bytes) -> tuple[bytes, dict]:
    """The receipt bytes of a delayed queue entry and how it was stored (``StateStoredReceipt`` or plain)."""
    if raw[:2] == b"\xff\xff":
        version = raw[2]
        if version not in (0, 1):
            raise Unsupported([f"state-stored receipt version {version}"])
        return raw[3:-16], {"kind": f"storedV{version}", "gas": int.from_bytes(raw[-16:-8], "little"),
                            "size": int.from_bytes(raw[-8:], "little")}
    return raw, {"kind": "receipt"}


def received_payload(data) -> list[int] | None:
    """``ReceivedData.data`` of a decoded record: absent, or the bytes."""
    if data is None:
        return None
    return list(base64.b64decode(data)) if isinstance(data, str) else list(data)


class Reader:
    """A cursor over Borsh bytes."""

    def __init__(self, raw: bytes):
        self.raw, self.at = raw, 0

    def take(self, n: int) -> bytes:
        if self.at + n > len(self.raw):
            raise Unsupported(["truncated Borsh record"])
        chunk = self.raw[self.at:self.at + n]
        self.at += n
        return chunk

    def uint(self, width: int) -> int:
        return int.from_bytes(self.take(width), "little")

    def string(self) -> str:
        return self.take(self.uint(4)).decode()

    def vector(self) -> bytes:
        return self.take(self.uint(4))

    def public_key(self) -> list[int]:
        tag = self.take(1)[0]
        if tag not in (0, 1):
            raise Unsupported([f"public key type {tag}"])
        return [tag] + list(self.take(32 if tag == 0 else 64))

    def done(self) -> bool:
        return self.at == len(self.raw)


def global_identifier_json(identifier: dict) -> dict:
    """The model's global contract identifier from the typed form ``{"hash": ...}`` / ``{"account_id": ...}``."""
    if "hash" in identifier:
        return {"codeHash": list(b58(identifier["hash"]))}
    name = identifier.get("account_id", identifier.get("accountId"))
    if name is None:
        raise Unsupported([f"global contract identifier {identifier}"])
    return {"accountId": list(name.encode())}


def signature_bytes(text: str) -> list[int]:
    kind, body = text.split(":", 1)
    prefix = {"ed25519": 0, "secp256k1": 1}.get(kind)
    if prefix is None:
        raise Unsupported([f"signature type {kind}"])
    return [prefix] + list(b58(body))


def nested(*items):
    """A tuple as Lean's JSON codec reads it: a pair whose second component is the rest, nested."""
    return list(items) if len(items) <= 2 else [items[0], nested(*items[1:])]


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
        self.yield_formats: list = []

    def fresh(self, table: dict, name: str) -> int:
        if name not in table:
            table[name] = self.next_id
            self.next_id += 1
        return table[name]

    def code_label(self, blob: bytes) -> str:
        label = nc.b58encode(hashlib.sha256(blob).digest())
        self.codes[label] = blob
        return label

    def access_key(self, raw: dict) -> dict:
        permission = raw["permission"]
        if isinstance(permission, dict):
            name, body = next(iter(permission.items()))
            if name == "GasKeyFullAccess":
                return {"nonce": raw["nonce"], "permission": {"kind": "gasKeyFullAccess", "balance": body["balance"],
                                                              "numNonces": body["num_nonces"]}}
            if name == "GasKeyFunctionCall":
                info, call = (body["gas_key_info"], body["function_call"]) if isinstance(body, dict) else body
                return {"nonce": raw["nonce"], "permission": {
                    "kind": "gasKeyFunctionCall", "balance": info["balance"], "numNonces": info["num_nonces"],
                    "allowance": call["allowance"], "receiverId": call["receiver_id"],
                    "methodNames": call["method_names"]}}
        return importer.access_key(raw)

    def action(self, view) -> dict:
        if isinstance(view, dict) and len(view) == 1:
            name, data = next(iter(view.items()))
            name = ACTION_ALIASES.get(name, name)
            if name == "DeployGlobalContract":
                label = self.code_label(base64.b64decode(data["code"]))
                mode = data.get("deploy_mode") or ("AccountId" if next(iter(view)) == "DeployGlobalContractByAccountId" else "CodeHash")
                return {"kind": "deployGlobalContract", "codeHash": label,
                        "mode": {"CodeHash": "codeHash", "AccountId": "accountId"}[mode]}
            if name == "UseGlobalContract":
                if "contract_identifier" in data:
                    identifier = data["contract_identifier"]
                elif "code_hash" in data:
                    identifier = {"hash": data["code_hash"]}
                else:
                    identifier = {"account_id": data["account_id"]}
                return {"kind": "useGlobalContract", **global_identifier_json(identifier)}
            if name == "TransferToGasKey":
                return {"kind": "transferToGasKey", "publicKey": list(self.keys[data["public_key"]]),
                        "deposit": data["deposit"]}
            if name == "WithdrawFromGasKey":
                return {"kind": "withdrawFromGasKey", "publicKey": list(self.keys[data["public_key"]]),
                        "amount": data["amount"]}
            if name in ("Delegate", "DelegateV2"):
                return self.delegate(name, data)
            if name == "AddKey":
                return {"kind": "addKey", "publicKey": list(self.keys[data["public_key"]]),
                        "accessKey": self.access_key(data["access_key"])}
        return importer.action(view, self.keys, self.codes)

    def delegate(self, name: str, data: dict) -> dict:
        body = data["delegate_action"]
        v2 = name == "DelegateV2"
        if v2:
            body = body["V2"]
        nonce, index = body["nonce"], None
        if isinstance(nonce, dict):
            if "GasKeyNonce" in nonce:
                nonce, index = nonce["GasKeyNonce"]["nonce"], nonce["GasKeyNonce"]["nonce_index"]
            else:
                nonce = nonce["Nonce"]["nonce"]
        return {"kind": "delegate", "v2": v2, "senderId": body["sender_id"], "receiverId": body["receiver_id"],
                "actions": [self.action(a) for a in body["actions"]], "nonce": nonce, "nonceIndex": index,
                "maxBlockHeight": body["max_block_height"], "publicKey": list(self.keys[body["public_key"]]),
                "signature": signature_bytes(data["signature"])}

    def model_receipt(self, view: dict, typed: dict, raw: bytes) -> tuple[dict, str]:
        kind, refund = receipt_format(raw)
        payload = view["receipt"]
        variant = next(iter(payload))
        if kind == "resume":
            data = payload["Data"]
            body = {"kind": "data", "dataId": 0, "resumeDataId": list(b58(data["data_id"])),
                    "data": None if data["data"] is None else list(base64.b64decode(data["data"]))}
        elif kind == "data":
            data = payload["Data"]
            identifier = self.fresh(self.data_ids, data["data_id"])
            self.data_receivers[data["data_id"]] = view["receiver_id"]
            body = {"kind": "data", "dataId": identifier,
                    "data": None if data["data"] is None else list(base64.b64decode(data["data"]))}
        elif kind == "distribution":
            distribution = next(iter(typed["receipt"]["GlobalContractDistribution"].values()))
            if "code" not in distribution:       # the versioned wrapper: {"V2": {...}}
                distribution = next(iter(distribution.values()))
            body = {"kind": "globalDistribution", "id": global_identifier_json(distribution["id"]),
                    "targetShard": distribution["target_shard"],
                    "alreadyDelivered": distribution["already_delivered_shards"],
                    "codeHash": self.code_label(base64.b64decode(distribution["code"])),
                    "nonce": distribution.get("nonce", 0)}
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

    # --- columns the state view leaves undecoded: read straight from the raw trie entries -----------------------
    def state_receipt(self, record: dict, raw: bytes) -> dict:
        """A receipt stored in the shard (postponed or delayed) as the model's receipt JSON."""
        name, payload = next(iter(record["receipt"].items()))
        if name in ("Action", "ActionV2"):
            variant = "Action"
        elif name == "Data":
            variant = name
            if isinstance(payload.get("data"), list):                    # the typed form lists the bytes
                payload = dict(payload, data=base64.b64encode(bytes(payload["data"])).decode())
        else:
            variant = name
        view = {"predecessor_id": record["predecessor_id"], "receiver_id": record["receiver_id"],
                "receipt_id": record["receipt_id"], "receipt": {variant: payload}}
        receipt, kind = self.model_receipt(view, {"receipt": record["receipt"]}, raw)
        self.yield_formats.append([receipt["receiptId"], kind if kind in ("legacy", "v2") else "legacy"])
        return receipt

    def raw_action(self, reader: Reader) -> dict:
        tag = reader.take(1)[0]
        if tag == 0:
            return {"kind": "createAccount"}
        if tag == 1:
            return {"kind": "deployContract", "codeHash": self.code_label(reader.vector())}
        if tag == 2:
            return {"kind": "functionCall", "methodName": reader.string(), "args": list(reader.vector()),
                    "gas": reader.uint(8), "deposit": str(reader.uint(16))}
        if tag == 3:
            return {"kind": "transfer", "deposit": str(reader.uint(16))}
        if tag == 4:
            return {"kind": "stake", "stake": str(reader.uint(16)), "publicKey": reader.public_key()}
        if tag == 5:
            key = reader.public_key()
            return {"kind": "addKey", "publicKey": key, "accessKey": self.raw_access_key(reader)}
        if tag == 6:
            return {"kind": "deleteKey", "publicKey": reader.public_key()}
        if tag == 7:
            return {"kind": "deleteAccount", "beneficiaryId": reader.string()}
        raise Unsupported([f"stored receipt action tag {tag}"])

    def raw_access_key(self, reader: Reader) -> dict:
        nonce, tag = reader.uint(8), reader.take(1)[0]

        def call() -> dict:
            allowance = None if reader.take(1)[0] == 0 else str(reader.uint(16))
            receiver = reader.string()
            methods = [reader.string() for _ in range(reader.uint(4))]
            return {"allowance": allowance, "receiverId": receiver, "methodNames": methods}

        if tag == 1:
            return {"nonce": nonce, "permission": {"kind": "fullAccess"}}
        if tag == 0:
            return {"nonce": nonce, "permission": {"kind": "functionCall", **call()}}
        balance, nonces = str(reader.uint(16)), reader.uint(2)
        if tag == 3:
            return {"nonce": nonce, "permission": {"kind": "gasKeyFullAccess", "balance": balance, "numNonces": nonces}}
        return {"nonce": nonce, "permission": {"kind": "gasKeyFunctionCall", "balance": balance, "numNonces": nonces,
                                               **call()}}

    def raw_receipt(self, raw: bytes) -> dict:
        """A stored ``PromiseYield`` receipt, as the model's receipt JSON."""
        reader = Reader(raw)
        predecessor, receiver = reader.string(), reader.string()
        receipt_id = reader.take(32)
        tag = reader.take(1)[0]
        if tag not in (2, 6):
            raise Unsupported([f"stored receipt kind {tag}"])
        signer = reader.string()
        if tag == 6 and reader.take(1)[0] == 1:
            raise Unsupported(["stored receipt with an explicit refund_to"])
        signer_key, price = reader.public_key(), reader.uint(16)
        outputs = []
        for _ in range(reader.uint(4)):
            data_id, to = nc.b58encode(reader.take(32)), reader.string()
            self.data_receivers[data_id] = to
            outputs.append([self.fresh(self.data_ids, data_id), to])
        inputs = [reader.take(32) for _ in range(reader.uint(4))]
        actions = [self.raw_action(reader) for _ in range(reader.uint(4))]
        if len(inputs) != 1 or not reader.done():
            raise Unsupported(["stored yield receipt with an unexpected shape"])
        identifier = self.fresh(self.receipt_ids, nc.b58encode(receipt_id))
        self.yield_formats.append([identifier, "v2" if tag == 6 else "legacy"])
        return {"predecessorId": predecessor, "receiverId": receiver, "receiptId": identifier,
                "receipt": {"kind": "action", "signerId": signer, "signerPublicKey": signer_key,
                            "gasPrice": str(price), "inputDataIds": [], "outputDataReceivers": outputs,
                            "yieldDataId": list(inputs[0]), "actions": actions}}

    def raw_columns(self) -> dict:
        """The yield queue and the global contract tables, decoded from their raw trie entries."""
        found = {"globalCode": [], "globalNonces": [], "yieldIndices": None, "yieldTimeouts": [],
                 "yieldReceipts": [], "yieldStatus": []}

        def identifier(reader: Reader) -> dict:
            tag = reader.take(1)[0]
            if tag == 0:
                return {"codeHash": list(reader.take(32))}
            return {"accountId": list(reader.vector())}

        def owned(key: bytes) -> tuple[str, list[int]]:
            name, _, data_id = key[1:].partition(b",")
            return name.decode(), list(data_id)

        for key_hex, value_hex in self.bundle["preState"]["entries"]:
            key, value = bytes.fromhex(key_hex), bytes.fromhex(value_hex)
            number = key[0]
            if number == 10:
                found["yieldIndices"] = [int.from_bytes(value[:8], "little"), int.from_bytes(value[8:16], "little")]
            elif number == 11:
                reader = Reader(value)
                found["yieldTimeouts"].append(nested(int.from_bytes(key[1:9], "little"), reader.string(),
                                                     list(reader.take(32)), reader.uint(8)))
            elif number == 12:
                account, data_id = owned(key)
                found["yieldReceipts"].append(nested(account, data_id, self.raw_receipt(value)))
            elif number == 18:
                reader = Reader(key[1:])
                ident = identifier(reader)
                found["globalCode"].append([ident, self.code_label(value)])
            elif number == 19:
                found["globalNonces"].append([identifier(Reader(key[1:])), int.from_bytes(value, "little")])
            elif number == 20:
                account, data_id = owned(key)
                found["yieldStatus"].append(nested(account, data_id, ["yielded", "resumeInitiated"][value[0]]))
        return found

    def state(self) -> tuple[dict, dict | None, dict]:
        """Model state from the decoded pre-state records; also the delayed-queue header and the scheduler."""
        accounts, keys, storage, contracts, gas_nonces = [], [], {}, {}, []
        postponed, counts, by_data, received, delayed_rows = [], [], [], [], []
        raw_entries = {key: value for key, value in self.bundle["preState"]["entries"]}
        for row in self.decoded["preState"]:
            if "decodeError" in row:
                raise Unsupported([f"pre-state record that upstream cannot decode ({row['decodeError']})"])
            if row.get("opaque"):
                continue
            kind, value = next(iter(row["record"].items()))
            if kind == "Account":
                account = value["account"]
                extra = set(account) - {"amount", "locked", "code_hash", "storage_usage", "version",
                                        "global_contract_hash", "global_contract_account_id"}
                if extra:
                    raise Unsupported([f"account with fields {sorted(extra)}"])
                global_contract = None
                if account.get("global_contract_hash"):
                    global_contract = {"codeHash": list(b58(account["global_contract_hash"]))}
                elif account.get("global_contract_account_id"):
                    global_contract = {"accountId": list(account["global_contract_account_id"].encode())}
                accounts.append([value["account_id"], {"amount": account["amount"], "locked": account["locked"],
                                                       "storageUsage": account["storage_usage"],
                                                       "codeHash": None if account["code_hash"] == EMPTY_CODE_HASH else account["code_hash"],
                                                       "global": global_contract,
                                                       "versionTwo": account.get("version") == "V2"}])
            elif kind == "AccessKey":
                keys.append([[value["account_id"], list(self.keys[value["public_key"]])], self.access_key(value["access_key"])])
            elif kind == "GasKeyNonce":
                gas_nonces.append(nested(value["account_id"], list(self.keys[value["public_key"]]), value["index"],
                                         value["nonce"]))
            elif kind == "Data":
                storage.setdefault(value["account_id"], []).append(
                    [list(base64.b64decode(value["data_key"])), list(base64.b64decode(value["value"]))])
            elif kind == "Contract":
                blob = base64.b64decode(value["code"])
                label = nc.b58encode(hashlib.sha256(blob).digest())
                self.codes[label] = blob
                contracts[value["account_id"]] = label
            elif kind == "PostponedReceipt":
                receipt = self.state_receipt(value, bytes.fromhex(raw_entries[row["key"]]))
                postponed.append([receipt["receiptId"], receipt])
            elif kind == "PostponedReceiptId":
                self.data_receivers[value["data_id"]] = value["account_id"]
                by_data.append([self.fresh(self.data_ids, value["data_id"]),
                                self.fresh(self.receipt_ids, value["receipt_id"])])
            elif kind == "PendingDataCount":
                counts.append([self.fresh(self.receipt_ids, value["receipt_id"]), value["count"]])
            elif kind == "ReceivedData":
                self.data_receivers[value["data_id"]] = value["account_id"]
                received.append([self.fresh(self.data_ids, value["data_id"]), received_payload(value["data"])])
            elif kind == "DelayedReceipt":
                delayed_rows.append((row["queueIndex"], row["key"], value))
            else:
                raise Unsupported([f"pre-state record {kind}"])
        for identifier, account in accounts:
            label = account["codeHash"]
            if (contracts.get(identifier) or None) != label:
                raise Unsupported(["account code hash without a matching contract record"])
        state = {"accounts": accounts, "accessKeys": keys,
                 "storage": [[name, sorted(rows)] for name, rows in sorted(storage.items())],
                 "postponed": postponed, "pendingDataCount": counts, "postponedByData": by_data,
                 "receivedData": received, "delayed": [],
                 "nextId": 1, "gasKeyNonces": gas_nonces, **self.raw_columns()}
        entries = raw_entries
        header = entries.get("07")
        delayed = None
        if header is not None:
            raw = bytes.fromhex(header)
            first, last = int.from_bytes(raw[:8], "little"), int.from_bytes(raw[8:16], "little")
            if len(raw) != 16 or [index for index, _, _ in sorted(delayed_rows)] != list(range(first, last)):
                raise Unsupported(["pre-state delayed receipt queue header disagrees with its entries"])
            forms = []
            for index, key, record in sorted(delayed_rows):
                body, form = delayed_form(bytes.fromhex(entries[key]))
                receipt = self.state_receipt(record, body)
                state["delayed"].append(receipt)
                forms.append(form)
            delayed = {"firstIndex": first, "forms": forms}
        elif delayed_rows:
            raise Unsupported(["delayed receipts without a queue header"])
        scheduler = None
        value = entries.get("0f")
        if value is not None:
            scheduler = {"raw": list(bytes.fromhex(value))}
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
            formats.append([receipt["receiptId"], kind if kind in ("legacy", "v2") else "legacy"])
        state["nextId"] = self.next_id
        registry = {"receiptIds": [[identifier, list(b58(name))] for name, identifier in self.receipt_ids.items()],
                    "dataIds": [{"id": identifier, "hash": list(b58(name)), "receiverId": self.data_receivers[name]}
                                for name, identifier in self.data_ids.items()],
                    "actionFormats": formats + self.yield_formats, "delayed": delayed}
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
                        "transactions": transactions, "incomingIndices": None,
                        "chainId": bundle["meta"]["chainId"], "shardId": bundle["meta"]["shardId"],
                        "shardIds": layout_shard_ids(context["shardLayout"]),
                        "epochInfo": epoch_info(context["epochInfo"]),
                        "validatorAccountsUpdate": validator_update(context["validatorAccountsUpdate"])}],
            "transactionBlockHashes": [hashes], "queueContext": registry,
            "schedulerInputs": [{"congestionInfo": [[shard, list(bytes.fromhex(info)), missed]
                                                    for shard, info, missed in context["congestionInfo"]],
                                 "bandwidthRequests": list(bytes.fromhex(context["bandwidthRequests"])),
                                 "shardLayout": list(bytes.fromhex(context["shardLayout"])),
                                 "prevBlockHash": list(bytes.fromhex(context["prevBlockHash"]))}],
        }
        if scheduler is not None:
            request["initialScheduler"] = scheduler
        buffers = [[list(bytes.fromhex(key)), list(bytes.fromhex(value))]
                   for key, value in bundle["preState"]["entries"] if column(key) in BUFFER_COLUMNS]
        if buffers:
            request["initialBuffers"] = buffers
        return request


def epoch_info(info: dict) -> dict:
    """What `EpochInfoProvider` answers: minimum stake, total stake and each validator's stake."""
    return {"minimumStake": info["minimumStake"], "totalStake": info["totalStake"],
            "validators": {name: stake for name, stake in info["validators"]}}


def validator_update(update: dict | None) -> dict | None:
    """The epoch-start `ValidatorAccountsUpdate` of the shard (None outside an epoch's first chunk)."""
    if update is None:
        return None
    return {"stakeInfo": update["stakeInfo"], "validatorRewards": update["validatorRewards"],
            "lastProposals": update["lastProposals"],
            "protocolTreasuryAccountId": update["protocolTreasuryAccountId"]}


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
    published = {"validatorProposals": bytes(trace["validatorProposals"]).hex(),
                 "congestionInfo": bytes(trace["congestionInfo"]).hex(),
                 "bandwidthRequests": bytes(trace["bandwidthRequests"]).hex(),
                 "bandwidthSchedulerStateHash": bytes(trace["schedulerStateHash"]).hex(),
                 "delayedReceiptsCount": trace["delayedReceiptsCount"]}
    for name, value in published.items():
        if expected[name] != value:
            raise Mismatch(name, extra)
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
