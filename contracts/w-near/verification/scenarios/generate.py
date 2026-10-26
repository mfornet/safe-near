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
    (HERE / "40_gas.json").write_text(json.dumps(
        gas_bound_scenarios() + long_input_scenarios([10000], [1000, 30000, 60000], [1000, 20000]), indent=1) + "\n")
    # Inputs of megabytes take minutes in the interpreter: run on request.
    (HERE / "slow").mkdir(exist_ok=True)
    (HERE / "slow" / "40_gas_large.json").write_text(json.dumps(
        long_input_scenarios([1000000, 4000000], [200000], [100000, 1000000, 4194304], " (large)"), indent=1) + "\n")
    (HERE / "60_random.json").write_text(json.dumps([random_scenario(s) for s in range(1, 9)], indent=1) + "\n")
    (HERE / "61_random_wide.json").write_text(json.dumps([random_scenario(s, wide=True) for s in WIDE_SEEDS], indent=1) + "\n")
