"""Writes the generated scenario files (python3 generate.py). Hand-written
scenarios are the other *.json files; these need inputs too large or too
regular to write by hand."""
import json
import random
from pathlib import Path

HERE = Path(__file__).parent
FEE = 125 * 10**19  # storage_balance_bounds().min under mainnet accounting
TGAS = 10**12


def call(frm, method, args=None, deposit=0, gas=None, **extra):
    c = {"from": frm, "method": method}
    if args is not None:
        c["args"] = args
    if deposit:
        c["deposit"] = str(deposit)
    if gas is not None:
        c["gas"] = gas
    c.update(extra)
    return c


def rx(label, c, expect=None, probe=False):
    r = {"label": label, "call": c}
    if expect:
        r["expect"] = expect
    if probe:
        r["probe"] = True
    return r


def neighbours(account):
    """Valid ids that differ from `account` in one character: their keys
    share every prefix of the account's key."""
    out = []
    for i, ch in enumerate(account):
        if ch in ".-_":
            continue
        for c in "0qz":
            if c != ch:
                out.append(account[:i] + c + account[i + 1:])
    return out


def gas_bound_scenarios():
    crowd = sorted(set(neighbours("alice.near") + neighbours("bob.near")))
    accounts = {"alice.near": str(10**24), "bob.near": str(10**24)}
    accounts.update({a: "0" for a in crowd})
    # Other contracts' records whose trie keys share wrap.near's prefix.
    trie = [{"account": a, "key": "STATE", "value": "x" * 40}
            for a in neighbours("wrap.near") + ["wrap.near0", "wrap.nea", "wrap.near.a"]]
    trie += [{"account": "wrap.neas", "key": "a" + chr(10) + "\u0000\u0000\u0000alice.near", "value": "v"}]
    methods = [
        ("near_deposit", "alice.near", None, 10**24),
        ("near_deposit-new", "carl.near", None, 10**24),
        ("ft_transfer", "alice.near", {"receiver_id": "bob.near", "amount": "1", "memo": "m"}, 1),
        ("ft_transfer_call", "alice.near", {"receiver_id": "bob.near", "amount": "1", "msg": ""}, 1),
        ("near_withdraw", "alice.near", {"amount": "1"}, 1),
        ("storage_deposit", "alice.near", {"account_id": crowd[0] + "x"}, FEE + 5),
        ("storage_deposit-registered", "alice.near", {"account_id": crowd[1]}, 7),
        ("storage_unregister", crowd[2], {}, 1),
        ("storage_withdraw", "alice.near", {"amount": "0"}, 1),
        ("ft_balance_of", "alice.near", {"account_id": "bob.near"}, 0),
        ("storage_balance_of", "alice.near", {"account_id": crowd[3]}, 0),
        ("ft_total_supply", "alice.near", None, 0),
        ("ft_metadata", "alice.near", None, 0),
        ("new", "wrap.near", None, 0),
    ]
    out = []
    for gas in ["bound", "bound-1"]:
        receipts = []
        for name, frm, args, deposit in methods:
            method = name.split("-")[0] if name != "near_deposit-new" else "near_deposit"
            if name == "storage_deposit-registered":
                method = "storage_deposit"
            receipts.append(rx(f"{name}@{gas}", call(frm, method, args, deposit, gas=gas), probe=True))
        resolve = {"sender_id": "alice.near", "receiver_id": "bob.near", "amount": "10"}
        for res_name, res in [("failed", ["failed"]), ("value", [{"ok": "\"3\""}])]:
            receipts.append(rx(f"ft_resolve_transfer-{res_name}@{gas}",
                               call("wrap.near", "ft_resolve_transfer", resolve, gas=gas, results=res), probe=True))
        for name, blocks in [("cold", [{"receipts": receipts}])]:
            out.append({"name": f"gas: every method at {gas} on an adversarial trie ({len(crowd)} neighbours)",
                        "state": {"accounts": accounts}, "trie": trie, "blocks": blocks})
    # Warm cache: the same transfers repeated within one chunk, then in a new one.
    t = call("alice.near", "ft_transfer", {"receiver_id": "bob.near", "amount": "1"}, 1, gas="bound")
    out.append({"name": "gas: repeated transfers at the bound, warm and cold cache",
                "state": {"accounts": accounts}, "trie": trie,
                "blocks": [{"receipts": [rx(f"warm-{i}", t, "ok") for i in range(5)]},
                           {"receipts": [rx("cold", t, "ok")]}]})
    return out


def long_input_scenarios(arg_sizes, msg_sizes, result_sizes, suffix=""):
    acc = {"alice.near": str(10**24), "bob.near": "0"}
    out = []
    receipts = []
    for size in msg_sizes:
        msg = [{"repeat": "m", "times": size}]
        args = ["{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"msg\":\""] + msg + ["\"}"]
        # Beyond about 30 KB no prepaid gas fits the bound: the call keeps 25 Tgas.
        for gas in (["bound"] if size <= 30000 else []) + ["300000000000000", "1000000000000000"]:
            receipts.append(rx(f"tc-msg-{size}@{gas}", call("alice.near", "ft_transfer_call", None, 1, gas=gas, argsText=args), probe=True))
    for size in arg_sizes:
        pad = ["{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"x\":\""] + [{"repeat": "p", "times": size}] + ["\"}"]
        receipts.append(rx(f"transfer-ignored-string-{size}@bound", call("alice.near", "ft_transfer", None, 1, gas="bound", argsText=pad), probe=True))
        arr = ["{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"x\":["] + [{"repeat": "1,", "times": size // 2}] + ["1]}"]
        receipts.append(rx(f"transfer-ignored-array-{size}@bound", call("alice.near", "ft_transfer", None, 1, gas="bound", argsText=arr), probe=True))
        esc = ["{\"receiver_id\":\"bob.near\",\"amount\":\"1\",\"x\":\""] + [{"repeat": "\\u00e9", "times": size // 6}] + ["\"}"]
        receipts.append(rx(f"transfer-ignored-escapes-{size}@bound", call("alice.near", "ft_transfer", None, 1, gas="bound", argsText=esc), probe=True))
        zeros = ["{\"receiver_id\":\"bob.near\",\"amount\":\""] + [{"repeat": "0", "times": size}] + ["1\"}"]
        receipts.append(rx(f"transfer-amount-zeros-{size}@bound", call("alice.near", "ft_transfer", None, 1, gas="bound", argsText=zeros), probe=True))
        ws = [{"repeat": " ", "times": size}, "{\"receiver_id\":\"bob.near\",\"amount\":\"1\"}"]
        receipts.append(rx(f"transfer-whitespace-{size}@bound", call("alice.near", "ft_transfer", None, 1, gas="bound", argsText=ws), probe=True))
        receipts.append(rx(f"deposit-unread-args-{size}@bound", call("alice.near", "near_deposit", None, 10**24, gas="bound", argsText=[{"repeat": "z", "times": size}]), probe=True))
    out.append({"name": "gas: long arguments at and around the bound" + suffix, "state": {"accounts": acc},
                "blocks": [{"receipts": receipts}]})
    resolve = {"sender_id": "alice.near", "receiver_id": "bob.near", "amount": "10"}
    receipts = []
    for size in result_sizes:
        for shape, res in [("digits", {"ok": ["\""] + [{"repeat": "1", "times": size}] + ["\""]}),
                           ("garbage", {"ok": [{"repeat": "x", "times": size}]}),
                           ("zeros", {"ok": ["\""] + [{"repeat": "0", "times": size}] + ["7\""]}),
                           ("plus-zeros", {"ok": ["\"+"] + [{"repeat": "0", "times": size}] + ["7\""]}),
                           ("escaped-zeros", {"ok": ["\""] + [{"repeat": "\\u0030", "times": size // 6}] + ["7\""]}),
                           ("whitespace", {"ok": [{"repeat": " ", "times": size}, "\"7\""]})]:
            for gas in ["bound", "5000000000000"]:
                receipts.append(rx(f"resolve-{shape}-{size}@{gas}",
                                   call("wrap.near", "ft_resolve_transfer", resolve, gas=gas, results=[res]), probe=True))
    out.append({"name": "gas: large promise results in ft_resolve_transfer" + suffix,
                "state": {"accounts": {"alice.near": "100", "bob.near": "100"}},
                "blocks": [{"receipts": receipts}]})
    return out


MAX_RECEIPT_SIZE = 4194304  # limit_config.max_receipt_size, protocol 86


def receipt_size(predecessor, receiver, signer, pk_len, outputs, dependencies, actions_size):
    """Borsh size of an action receipt (nearcore's `Receipt` with `ActionReceipt`)."""
    return (4 + len(predecessor) + 4 + len(receiver) + 32 + 1 + 4 + len(signer) + 1 + pk_len + 16
            + 4 + sum(32 + 4 + len(o) for o in outputs) + 4 + 32 * dependencies + 4 + actions_size)


def function_call_size(method, args):
    return 1 + 4 + len(method) + 4 + len(json.dumps(args, separators=(",", ":"))) + 8 + 16


def signer_key_scenarios():
    """`Context.WF` does not bound the signer's public key, and every receipt a
    call creates carries it. Keys that put each receipt one byte under, at and
    over `max_receipt_size`."""
    contract, alice, bob = "wrap.near", "alice.near", "bob.near"
    long_signer = "s" * 64
    state = {"accounts": {alice: "1000", bob: "0"}}

    def key(n):
        return [{"repeat": "00", "times": n}]

    def edges(base):
        return [(MAX_RECEIPT_SIZE - base + d, "ok" if d <= 0 else "other:size of the receipt exceeded")
                for d in (-1, 0, 1)]

    out = []
    for signer in (alice, long_signer):
        payout = receipt_size(contract, alice, signer, 0, [], 0, 1 + 16)
        receipts = []
        for n, expect in edges(payout):
            for method, args, deposit in (("near_withdraw", {"amount": "5"}, 1),
                                          ("storage_deposit", {}, FEE + 7),
                                          ("storage_unregister", {"force": True}, 1)):
                receipts.append(rx(f"{method} {n - (MAX_RECEIPT_SIZE - payout)}",
                                   call(alice, method, args, deposit=deposit, signer=signer, signerPk=key(n)),
                                   expect=expect, probe=True))
        out.append({"name": f"signer key at the receipt size limit: payouts, signer {len(signer)} bytes",
                    "description": "Generated by generate.py. The payout receipt of near_withdraw, the refund "
                                   "of storage_deposit and storage_unregister, with a signer key that puts it "
                                   "one byte under, at and over max_receipt_size.",
                    "state": state, "blocks": [{"receipts": receipts}]})

    on_transfer = {"sender_id": alice, "amount": "5", "msg": ""}
    resolve = {"sender_id": alice, "receiver_id": bob, "amount": "5"}
    first = receipt_size(contract, bob, alice, 0, [contract], 0, function_call_size("ft_on_transfer", on_transfer))
    second = receipt_size(contract, contract, alice, 0, [], 1, function_call_size("ft_resolve_transfer", resolve))
    receipts = []
    for base, which in ((first, "ft_on_transfer"), (second, "ft_resolve_transfer")):
        for n, expect in edges(base):
            if which == "ft_on_transfer" and expect == "ok" and n > MAX_RECEIPT_SIZE - second:
                expect = "other:size of the receipt exceeded"  # the callback is the larger receipt
            receipts.append(rx(f"{which} {n - (MAX_RECEIPT_SIZE - base)}",
                               call(alice, "ft_transfer_call", {"receiver_id": bob, "amount": "5", "msg": ""},
                                    deposit=1, signerPk=key(n)), expect=expect, probe=True))
    out.append({"name": "signer key at the receipt size limit: transfer-call",
                "description": "Generated by generate.py. ft_on_transfer carries one output data receiver, "
                               "ft_resolve_transfer one dependency: keys that put either receipt one byte "
                               "under, at and over max_receipt_size.",
                "state": state, "blocks": [{"receipts": receipts}]})
    return out


class JsonFuzz:
    """Random argument bytes for one method, near the shapes serde_json and
    the derived `Deserialize` accept: every field's value in and out of its
    type, escaped and duplicate keys, unknown fields with nested values, the
    array form, odd whitespace, and single-byte corruption."""

    VALID_ACCOUNTS = ["bob.near", "alice.near", "wrap.near", "ab", "a" * 64, "0" * 64, "0x" + "ab" * 20,
                      "a-b_c.d", "near"]
    INVALID_ACCOUNTS = ["Bob.near", "a", "a" * 65, "bob..near", "-bob", "bob.near.", "", "bob near", "bób.near",
                        "bob\u0000", "bob_.near", ".bob"]
    VALID_U128 = ["0", "1", "5", "1000", str(2**128 - 1), "+5", "0005", "+0", "000", "0" * 40 + "7"]
    INVALID_U128 = ["", "+", "-1", "-0", " 5", "5 ", "5.0", "1e3", str(2**128), "٥", "0x5", "++5", "5\u0000",
                    "+-5", "５"]
    STRINGS = ["", "m", "hello world", "é中\U0001F600", "\"quoted\\\"", "tab\there", "nul\u0000",
               "\u007f\u0080߿ࠀ￿", "\U0010FFFF"]

    def __init__(self, rnd):
        self.rnd = rnd
        # Clean inputs only vary what serde_json accepts; noisy ones also
        # inject malformed bytes.
        self.noisy = False

    def noise(self, p):
        return self.noisy and self.rnd.random() < p

    def ws(self):
        r = self.rnd.random()
        if r < 0.75:
            return b""
        if not self.noise(0.1):
            return bytes(self.rnd.choice(b" \t\n\r") for _ in range(self.rnd.randint(1, 3)))
        return self.rnd.choice([b"\x0b", b"\x0c", b"\xc2\xa0", b"\x00", b"\xef\xbb\xbf"])

    def string(self, s):
        """A JSON string for `s`, with random escapes, sometimes malformed."""
        rnd, out = self.rnd, bytearray(b'"')
        for ch in s:
            cp = ord(ch)
            short = {'"': b'\\"', "\\": b"\\\\", "\n": b"\\n", "\r": b"\\r", "\t": b"\\t", "\b": b"\\b",
                     "\f": b"\\f", "/": b"\\/"}
            if ch in short and (ch in '"\\' or rnd.random() < 0.5) and rnd.random() < 0.9:
                out += short[ch]
            elif cp < 0x20 or ch in '"\\' or rnd.random() < 0.15:
                if cp >= 0x10000:
                    v = cp - 0x10000
                    units = [0xD800 + (v >> 10), 0xDC00 + (v & 0x3FF)]
                else:
                    units = [cp]
                for u in units:
                    h = "%04x" % u
                    out += b"\\u" + (h.upper() if rnd.random() < 0.3 else h).encode()
            else:
                out += ch.encode("utf-8", "surrogatepass")
        if self.noise(0.08):
            pos = rnd.randint(1, len(out))
            out[pos:pos] = rnd.choice([b"\\ud800", b"\\udc00", b"\\ud800\\u0041", b"\\x", b"\\u12", b"\x01",
                                      b"\xff", b"\xc0\xaf", b"\xed\xa0\x80", b"\\U0041", b"\x7f", b"\\'"])
        return bytes(out) + b'"'

    def ignored(self, depth=0):
        """Any JSON value, for an unknown field."""
        rnd = self.rnd
        r = rnd.random()
        if depth > 3 or r < 0.5:
            if self.noise(0.2):
                return rnd.choice([b"01", b"1.", b".5", b"nul", b"-", b"1e", b"+1", b"NaN"])
            return rnd.choice([b"null", b"true", b"false", b"0", b"-0", b"1.5e+3", b"-12", b"1E9", b"[]", b"{}",
                               self.string(rnd.choice(self.STRINGS)), b'"\xff"', b'"\xc0\xaf"'])
        if r < 0.75:
            items = [self.ignored(depth + 1) for _ in range(rnd.randint(0, 3))]
            return (b"[" + b",".join(self.ws() + i + self.ws() for i in items) + (b"," if self.noise(0.05) else b"")
                    + b"]")
        members = [self.string(rnd.choice(["k", "amount", "", "é"])) + b":" + self.ignored(depth + 1)
                   for _ in range(rnd.randint(0, 3))]
        if self.noise(0.1):
            members.append(b'"\xff":1')
        return b"{" + b",".join(members) + b"}"

    def typed(self, kind):
        rnd = self.rnd
        if self.noise(0.2):
            return rnd.choice([b"null", b"5", b"true", b"[]", b"{}", b'"x"', b"1.0", b'["5"]'])
        good = not self.noise(0.4)
        if kind == "account":
            return self.string(rnd.choice(self.VALID_ACCOUNTS if good else self.INVALID_ACCOUNTS))
        if kind == "u128":
            return self.string(rnd.choice(self.VALID_U128 if good else self.INVALID_U128))
        if kind == "string":
            return self.string(rnd.choice(self.STRINGS) * rnd.choice([1, 1, 1, 3]))
        if kind == "bool":
            return rnd.choice([b"true", b"false"]) if good else rnd.choice([b'"true"', b"1", b"True", b"tru"])
        raise ValueError(kind)

    def key(self, name):
        return self.string(name)

    def args(self, fields):
        """`fields`: (name, kind, optional) in declaration order."""
        rnd = self.rnd
        self.noisy = rnd.random() < 0.4
        if rnd.random() < 0.12:
            n = len(fields) + rnd.choice([-1, 0, 0, 0, 1])
            vals = [self.typed(fields[i][1]) if i < len(fields) else self.ignored() for i in range(max(n, 0))]
            body = b"[" + b",".join(self.ws() + v + self.ws() for v in vals) + b"]"
        else:
            members = []
            for name, kind, optional in fields:
                r = rnd.random()
                if optional and r < 0.3:
                    continue
                if not optional and self.noise(0.05):
                    continue
                members.append((self.key(name), self.typed(kind)))
                if self.noise(0.05):
                    members.append((self.key(name), self.typed(kind)))
            for _ in range(rnd.choice([0, 0, 0, 1, 2])):
                members.append((self.key(rnd.choice(["x", "memo_", "Amount", "amount ", "", "é"])),
                                self.ignored()))
            if self.noise(0.05):
                members.append((b'"\xff"', b"1"))
            rnd.shuffle(members)
            body = b"{" + b",".join(self.ws() + k + self.ws() + b":" + self.ws() + v + self.ws()
                                    for k, v in members) + (b"," if self.noise(0.03) else b"") + b"}"
        body = self.ws() + body + self.ws()
        if self.noise(0.1):
            body = bytearray(body)
            pos = rnd.randrange(len(body) + 1)
            op = rnd.random()
            if op < 0.33 and pos < len(body):
                del body[pos]
            elif op < 0.66:
                body[pos:pos] = bytes([rnd.randrange(256)])
            elif pos < len(body):
                body[pos] = rnd.randrange(256)
            body = bytes(body)
        if self.noise(0.05):
            body += rnd.choice([b"x", b"{}", b"\x00", b","])
        return body


FUZZ_METHODS = {
    "near_withdraw": ([("amount", "u128", False)], 1),
    "ft_transfer": ([("receiver_id", "account", False), ("amount", "u128", False), ("memo", "string", True)], 1),
    "ft_transfer_call": ([("receiver_id", "account", False), ("amount", "u128", False), ("memo", "string", True),
                          ("msg", "string", False)], 1),
    "ft_resolve_transfer": ([("sender_id", "account", False), ("receiver_id", "account", False),
                             ("amount", "u128", False)], 0),
    "ft_balance_of": ([("account_id", "account", False)], 0),
    "storage_deposit": ([("account_id", "account", True), ("registration_only", "bool", True)], FEE + 3),
    "storage_withdraw": ([("amount", "u128", True)], 1),
    "storage_unregister": ([("force", "bool", True)], 1),
    "storage_balance_of": ([("account_id", "account", False)], 0),
}


def fuzz_result(f):
    """A random promise result for `ft_resolve_transfer`: mostly near a `U128`."""
    rnd = f.rnd
    r = rnd.random()
    if r < 0.05:
        return "failed"
    if r < 0.08:
        return "notReady"
    f.noisy = rnd.random() < 0.4
    if r < 0.75:
        body = f.ws() + f.typed("u128") + f.ws()
    else:
        body = f.ignored()
    if f.noise(0.2):
        body = bytes(rnd.randrange(256) for _ in range(rnd.randint(0, 4))) + body
    return {"okHex": body.hex()}


def fuzz_scenario(seed, probes=150):
    """Seeded random argument bytes for every method that has parameters (and
    random promise results for the callback), as probes on one state with
    every party registered; half of them at the model's gas bound or one below
    it (300 Tgas when the input is no call)."""
    rnd = random.Random(seed)
    f = JsonFuzz(rnd)
    contract = "wrap.near"
    accounts = {"alice.near": "1000", "bob.near": "7", contract: "3", "a" * 64: "0", "0" * 64: str(2**128 - 1100)}
    receipts = []
    for i in range(probes):
        method = rnd.choice(sorted(FUZZ_METHODS))
        fields, deposit = FUZZ_METHODS[method]
        if rnd.random() < 0.05:
            deposit = rnd.choice([0, 1, 2])
        frm = contract if method == "ft_resolve_transfer" else rnd.choice(["alice.near", "alice.near", "bob.near"])
        extra = {}
        if method == "ft_resolve_transfer":
            extra["results"] = [fuzz_result(f) for _ in range(rnd.choice([1, 1, 1, 2]))]
        gas = rnd.choice([None, None, "bound?", "bound-1?"]
                         + (["30000000000001"] if method == "ft_transfer_call" else []))
        c = call(frm, method, deposit=deposit, gas=gas, argsHex=f.args(fields).hex(), **extra)
        receipts.append(rx(f"{method} {i}", c, probe=True))
    return {"name": f"argument fuzz, seed {seed}",
            "description": "Generated by generate.py: random argument bytes near the accepted JSON shapes, "
                           "as probes on one state.",
            "state": {"accounts": accounts}, "blocks": [{"receipts": receipts}]}


# Seeds of `fuzz_scenario` kept as regressions and for breadth.
FUZZ_SEEDS = [1, 2]

ETH_IMPLICIT = "0x" + "ab" * 20
DETERMINISTIC = "0s" + "cd" * 20


def random_scenario(seed, steps=120, wide=False):
    """A random interleaving: calls from a small set of accounts, transfer-calls
    whose callbacks are delivered later in random order with random results.

    `wide` adds ETH-implicit and deterministic callers, a 64-character contract
    account, receivers of the call's result (`outputDataReceivers`), forged
    resolutions with deposits and transfer-calls at the 30 Tgas edge. Without
    it, a seed generates what it always did."""
    rnd = random.Random(seed)
    contract = "w" * 64 if wide and seed % 2 == 0 else "wrap.near"
    people = ["alice.near", "bob.near", "carol.near", "dave.near", contract,
              "a" * 64, "x.near"] + ([ETH_IMPLICIT, DETERMINISTIC] if wide else [])
    amounts = lambda: rnd.choice(["0", "1", "7", "100", str(10**21), str(10**24), "340282366920938463463374607431768211455"])
    blocks, pending, height = [], [], 0
    receipts = [rx("init", call(contract, "new"))]
    n = 0

    def outputs():
        """Receivers of the result: usually none, sometimes many."""
        if not wide or rnd.random() < 0.6:
            return {}
        n = rnd.choice([1, 2, 30, 1024])
        return {"outputDataReceivers": [{"repeat": rnd.choice([contract, "bob.near", ETH_IMPLICIT]), "times": n}]}

    while n < steps:
        n += 1
        kind = rnd.random()
        p = rnd.choice(people)
        q = rnd.choice(people)
        label = f"s{n}"
        if pending and kind < 0.2:
            ref = pending.pop(rnd.randrange(len(pending)))
            res = rnd.choice([["failed"], [{"ok": f"\"{rnd.choice(['0', '1', '5', '1000000'])}\""}],
                              [{"ok": "garbage"}], ["notReady"], [{"ok": "\"3\""}, "failed"]])
            receipts.append({"label": label, "deliver": ref, "results": res, "optional": True, **outputs()})
        elif wide and kind < 0.25:
            receipts.append(rx(label, call(p, "ft_resolve_transfer", {"sender_id": q, "receiver_id": rnd.choice(people), "amount": amounts()},
                                           deposit=rnd.choice([0, 0, 1]), results=rnd.choice([["failed"], [{"ok": "\"2\""}], []]), **outputs())))
        elif kind < 0.35:
            receipts.append(rx(label, call(p, "near_deposit", deposit=rnd.choice([1, FEE - 1, FEE, FEE + 1, 10**24]), **outputs())))
        elif kind < 0.45:
            receipts.append(rx(label, call(p, "storage_deposit", {"account_id": q} if rnd.random() < 0.5 else {},
                                           deposit=rnd.choice([0, 1, FEE, 3 * FEE]), **outputs())))
        elif kind < 0.6:
            receipts.append(rx(label, call(p, "ft_transfer", {"receiver_id": q, "amount": amounts()}, deposit=rnd.choice([1, 1, 1, 0, 2]))))
        elif kind < 0.75:
            receipts.append(rx(label, call(p, "ft_transfer_call", {"receiver_id": q, "amount": amounts(), "msg": "m"},
                                           deposit=1, gas=rnd.choice(["300000000000000", "30000000000000", "bound", "bound-1"]
                                                                    + (["30000000000001", "1000000000000000"] if wide else [])), **outputs())))
            pending.append(f"{label}#1")
        elif kind < 0.85:
            receipts.append(rx(label, call(p, "near_withdraw", {"amount": amounts()}, deposit=1, **outputs())))
        elif kind < 0.93:
            receipts.append(rx(label, call(p, "storage_unregister", {"force": rnd.random() < 0.5}, deposit=1, **outputs())))
        else:
            receipts.append(rx(label, call(p, rnd.choice(["ft_total_supply", "ft_balance_of", "storage_balance_of"]),
                                           {"account_id": q}, **outputs())))
        if rnd.random() < 0.25:
            height += rnd.choice([1, 1, 2, 10, 100])
            blocks.append({"height": height + 1, "receipts": receipts})
            height += 1
            receipts = []
    if receipts:
        blocks.append({"height": height + 1, "receipts": receipts})
    return {"name": f"random interleaving{', wide' if wide else ''}, seed {seed}",
            **({"contract": contract} if wide else {}),
            "description": "Generated by generate.py. A delivery is optional: the transfer-call it resolves may have failed.",
            "state": None, "account": {"balance": str(10**25)}, "blocks": blocks}


# Seeds of `random_scenario(wide=True)` kept as regressions and for breadth.
WIDE_SEEDS = [1, 2, 3, 4]

if __name__ == "__main__":
    import sys
    if sys.argv[1:2] == ["fuzz"]:
        # Fresh seeds for a scratch run: generate.py fuzz FIRST LAST DIR
        first, last, out = int(sys.argv[2]), int(sys.argv[3]), Path(sys.argv[4])
        out.mkdir(parents=True, exist_ok=True)
        for s in range(first, last + 1):
            (out / f"fuzz_{s}.json").write_text(json.dumps(fuzz_scenario(s), indent=1) + "\n")
        sys.exit()
    (HERE / "40_gas.json").write_text(json.dumps(
        gas_bound_scenarios() + long_input_scenarios([10000], [1000, 30000, 60000], [1000, 20000]), indent=1) + "\n")
    # Inputs of megabytes take minutes in the interpreter: run on request.
    (HERE / "slow").mkdir(exist_ok=True)
    (HERE / "slow" / "40_gas_large.json").write_text(json.dumps(
        long_input_scenarios([1000000, 4000000], [200000], [100000, 1000000, 4194304], " (large)"), indent=1) + "\n")
    (HERE / "26_arguments_fuzz.json").write_text(json.dumps([fuzz_scenario(s) for s in FUZZ_SEEDS], indent=1) + "\n")
    (HERE / "37_signer_key.json").write_text(json.dumps(signer_key_scenarios(), indent=1) + "\n")
    (HERE / "60_random.json").write_text(json.dumps([random_scenario(s) for s in range(1, 9)], indent=1) + "\n")
    (HERE / "61_random_wide.json").write_text(json.dumps([random_scenario(s, wide=True) for s in WIDE_SEEDS], indent=1) + "\n")
