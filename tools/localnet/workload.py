#!/usr/bin/env python3
"""Deterministic workload for the pinned neard localnet (stdlib only).

Every transaction is built from a fixed seed (account names, keys, contract arguments, the
order of rounds).  Transactions inside one round are submitted back to back so that they
share blocks and chunks; the next round starts when the previous one is final.  Only the
chain's own clock (block timestamps, hashes) differs between runs.

``python3 workload.py TOPOLOGY [--seed N]`` runs against a started localnet and writes
``data/TOPOLOGY/workload.json``, a log of every transaction, its label and its final status.
"""

from __future__ import annotations

import argparse
import base64
import hashlib
import json
from pathlib import Path
import sys
import time
import urllib.error

import nearcodec as nc
import wasmgen
import localnet

NEAR = 10**24
TGAS = 10**12
HERE = Path(__file__).resolve().parent


class Net:
    def __init__(self, topology: str):
        self.topology = topology

    def call(self, method, params, timeout=30):
        reply = localnet.rpc(self.topology, method, params, timeout=timeout)
        if "error" in reply:
            raise RuntimeError(json.dumps(reply["error"])[:300])
        return reply["result"]

    def height(self) -> int:
        return self.call("status", [])["sync_info"]["latest_block_height"]

    def final_hash(self) -> bytes:
        return nc.b58decode(self.call("block", {"finality": "final"})["header"]["hash"])

    def nonce(self, account: str, key: nc.Key) -> int:
        reply = self.call("query", {"request_type": "view_access_key", "finality": "optimistic",
                                    "account_id": account, "public_key": key.text})
        return reply["nonce"]

    def submit(self, signed: bytes) -> None:
        self.call("send_tx", {"signed_tx_base64": base64.b64encode(signed).decode(), "wait_until": "NONE"})

    def wait(self, signed: bytes, signer: str, deadline: float = 120, until: str = "FINAL"):
        tx_hash = nc.b58encode(nc.transaction_hash(signed))
        end = time.time() + deadline
        while time.time() < end:
            try:
                return self.call("tx", {"tx_hash": tx_hash, "sender_account_id": signer,
                                        "wait_until": until}, timeout=40)
            except RuntimeError as error:
                if "UNKNOWN_TRANSACTION" in str(error) or "TIMEOUT" in str(error):
                    time.sleep(0.5)
                    continue
                raise
            except (urllib.error.URLError, TimeoutError):
                time.sleep(0.5)
        return {"status": "LOST"}

    def view_state_prefix(self, account: str, prefix: bytes):
        reply = self.call("query", {"request_type": "view_state", "finality": "final", "account_id": account,
                                    "prefix_base64": base64.b64encode(prefix).decode()})
        return [(base64.b64decode(v["key"]), base64.b64decode(v["value"])) for v in reply["values"]]


def options_of(item: tuple) -> dict:
    return item[3] if len(item) > 3 else {}


class Actor:
    def __init__(self, account: str, key: nc.Key):
        self.account, self.key, self.nonce = account, key, None


class Workload:
    def __init__(self, net: Net, seed: int):
        self.net, self.seed = net, seed
        self.actors: dict[str, Actor] = {}
        self.log: list[dict] = []
        self.contracts: dict[str, bytes] = {}

    # --- plumbing -----------------------------------------------------------
    def key(self, label: str) -> nc.Key:
        return nc.Key.derive(f"{self.seed}/{label}")

    def actor(self, account: str, key: nc.Key | None = None) -> Actor:
        if account not in self.actors:
            self.actors[account] = Actor(account, key or self.key(account))
        return self.actors[account]

    def tx(self, actor: Actor, receiver: str, actions: list[bytes], block_hash: bytes, strict=False,
           key: nc.Key | None = None) -> bytes:
        key = key or actor.key
        if actor.nonce is None:
            actor.nonce = self.net.nonce(actor.account, actor.key)
        actor.nonce += 1
        make = nc.transaction_v1_strict if strict else nc.transaction
        return make(actor.account, key, actor.nonce, receiver, block_hash, actions)

    def round(self, label: str, items: list[tuple], settle: float = 0.0) -> list[dict]:
        """items: (actor, receiver, actions[, options]) submitted together, then awaited."""
        block_hash = self.net.final_hash()
        signed = []
        for item in items:
            actor, receiver, actions = item[:3]
            options = item[3] if len(item) > 3 else {}
            options = {k: v for k, v in options.items() if k in ("strict", "key")}
            signed.append((actor, receiver, self.tx(actor, receiver, actions, block_hash, **options)))
        rejected = {}
        for index, (actor, receiver, raw) in enumerate(signed):
            try:
                self.net.submit(raw)
            except RuntimeError as error:
                rejected[index] = str(error)[:200]
        results = []
        for index, ((actor, receiver, raw), item) in enumerate(zip(signed, items)):
            if index in rejected:
                outcome = {"status": "REJECTED", "rejection": rejected[index]}
                actor.nonce -= 1
            elif self.net.wait(raw, actor.account, deadline=20, until="INCLUDED").get("status") == "LOST":
                outcome = {"status": "LOST"}      # dropped by the pool: never reaches a chunk
            elif options_of(item).get("nowait"):
                outcome = self.net.wait(raw, actor.account, deadline=60, until="INCLUDED")
            else:
                outcome = self.net.wait(raw, actor.account, deadline=120)
            status = outcome.get("status")
            record = {"round": label, "signer": actor.account, "receiver": receiver,
                      "hash": nc.b58encode(nc.transaction_hash(raw)),
                      "actions": [a[0] for a in item[2]],
                      "status": list(status) if isinstance(status, dict) else status,
                      "final": outcome.get("final_execution_status")}
            if isinstance(status, dict):
                record["status"] = {k: (v if not isinstance(v, str) else v[:80]) for k, v in status.items()}
                record["failure"] = json.dumps(status.get("Failure"))[:200] if "Failure" in status else None
            record["receiptStatuses"] = [
                next(iter(r["outcome"]["status"])) if isinstance(r["outcome"]["status"], dict) else r["outcome"]["status"]
                for r in outcome.get("receipts_outcome", [])]
            self.log.append(record)
            results.append(outcome)
        print(f"[{self.net.height()}] {label}: " + ", ".join(
            f"{r['signer']}->{r['receiver']}:{r['status'] if isinstance(r['status'], str) else next(iter(r['status'] or {}), 'pending')}"
            for r in self.log[-len(items):]), flush=True)
        if settle:
            time.sleep(settle)
        return results

    def fc(self, method: str, args: bytes = b"", gas: int = 100 * TGAS, deposit: int = 0) -> bytes:
        return nc.function_call(method, args, gas, deposit)

    # --- scenarios ----------------------------------------------------------
    def setup(self):
        root = self.actor("node0", nc.Key.from_secret(
            json.loads((localnet.home(self.net.topology) / "node0/validator_key.json").read_text())["secret_key"]))
        self.root = root
        names = ["a.node0", "test1.node0", "test2.node0", "test3.node0", "est.node0", "ft.node0",
                 "u1.node0", "relay.node0"]
        for name in names:
            self.actor(name)
        def create(name, amount):
            return (root, name, [nc.create_account(), nc.transfer(amount), nc.add_key(self.actors[name].key.pk, nc.access_key_full())])
        self.round("create-accounts", [create(n, (20_000_000 if n == "a.node0" else 2000) * NEAR) for n in names])

    def run_all(self):
        """Features whose state never goes away (yield queues, global contracts, ETH-implicit accounts, gas keys)
        come last, so that the early chunks stay free of them."""
        self.setup()
        self.transfers()
        self.implicit_accounts()
        self.deploy_and_call()
        self.promises()
        self.keys()
        self.staking()
        self.delete_accounts()
        self.hostcalls()
        self.burst()
        self.delegate()
        self.eth_implicit()
        self.yields()
        self.global_contracts()
        self.gas_keys()
        self.wait_blocks(215)       # long enough for the unresumed yield to time out (200 blocks)

    def wait_blocks(self, count: int):
        start = self.net.height()
        while self.net.height() < start + count:
            time.sleep(0.5)

    def transfers(self):
        a, t1, t2, t3 = (self.actors[n] for n in ["a.node0", "test1.node0", "test2.node0", "test3.node0"])
        self.round("transfers", [
            (a, "test1.node0", [nc.transfer(5 * NEAR)]),
            (t1, "test2.node0", [nc.transfer(3 * NEAR)]),
            (t2, "test3.node0", [nc.transfer(2 * NEAR)]),
            (t3, "a.node0", [nc.transfer(1 * NEAR)]),
            (a, "a.node0", [nc.transfer(1)]),
            (a, "ghost.node0", [nc.transfer(7 * NEAR)]),          # no such account: refunded
            (a, "test2.node0", [nc.transfer(1 * NEAR), nc.transfer(2 * NEAR)]),
        ])

    def implicit_accounts(self):
        a = self.actors["a.node0"]
        implicit = self.key("implicit-1")
        near_implicit = implicit.public.hex()
        self.implicit = Actor(near_implicit, implicit)
        self.actors[near_implicit] = self.implicit
        self.round("implicit-create", [
            (a, near_implicit, [nc.transfer(10 * NEAR)]),
        ])
        # the NEAR-implicit account can sign; its key was added on creation
        self.round("implicit-spend", [(self.implicit, "test1.node0", [nc.transfer(1 * NEAR)])])
        # an implicit account that is created by a function call receipt is covered in `promises`

    def eth_implicit(self):
        """An ETH-implicit account is created with the global wallet contract, state the model does not have."""
        a = self.actors["a.node0"]
        eth_implicit = "0x" + hashlib.sha256(b"eth-implicit").digest()[:20].hex()
        self.round("eth-implicit-create", [(a, eth_implicit, [nc.transfer(10 * NEAR)])])

    def deploy_and_call(self):
        rs = (self.contract("test_contract_rs"))
        estimator = self.contract("estimator_contract")
        ft = self.contract("fungible_token")
        hostcalls = wasmgen.hostcalls()
        self.contracts_by_name = {"rs": rs, "estimator": estimator, "ft": ft, "host": hostcalls}
        t = self.actors
        self.round("deploy", [
            (t["a.node0"], "a.node0", [nc.deploy_contract(rs)]),
            (t["test1.node0"], "test1.node0", [nc.deploy_contract(rs)]),
            (t["test2.node0"], "test2.node0", [nc.deploy_contract(rs)]),
            (t["test3.node0"], "test3.node0", [nc.deploy_contract(rs)]),
            (t["est.node0"], "est.node0", [nc.deploy_contract(estimator)]),
            (t["ft.node0"], "ft.node0", [nc.deploy_contract(ft)]),
            (t["u1.node0"], "u1.node0", [nc.deploy_contract(hostcalls)]),
        ])
        u64 = lambda *values: b"".join(v.to_bytes(8, "little") for v in values)
        a, t1, t2, t3, u1 = (t[n] for n in ["a.node0", "test1.node0", "test2.node0", "test3.node0", "u1.node0"])
        self.round("calls-state", [
            (a, "a.node0", [self.fc("write_key_value", b"key-one" + u64(11))]),
            (t1, "test1.node0", [self.fc("write_key_value", b"key-two" + u64(22))]),
            (t2, "test2.node0", [self.fc("insert_strings", u64(0, 40))]),
            (t3, "test3.node0", [self.fc("write_block_height")]),
            (a, "test1.node0", [self.fc("log_something")]),
            (t1, "a.node0", [self.fc("write_random_value")]),
        ])
        self.round("calls-state-2", [
            (a, "a.node0", [self.fc("write_key_value", b"key-one" + u64(33))]),       # overwrite
            (a, "a.node0", [self.fc("read_value", u64(0))]),
            (t2, "test2.node0", [self.fc("delete_strings", u64(0, 20))]),
            (t3, "test3.node0", [self.fc("sum_with_input", u64(3, 4))]),
            (t1, "test1.node0", [self.fc("sum_n", u64(2000))]),
            (a, "test3.node0", [self.fc("fibonacci", bytes([15]))]),
        ])
        self.round("calls-context", [
            (a, "a.node0", [self.fc("ext_account_id")]),
            (a, "test1.node0", [self.fc("ext_predecessor_account_id")]),
            (a, "test2.node0", [self.fc("ext_signer_pk")]),
            (a, "a.node0", [self.fc("ext_account_balance")]),
            (a, "a.node0", [self.fc("ext_attached_deposit", deposit=1234)]),
            (a, "test1.node0", [self.fc("ext_sha256", b"safe-near")]),
            (a, "test2.node0", [self.fc("ext_validator_stake", b"node0")]),
            (a, "test3.node0", [self.fc("ext_validator_total_stake")]),
            (a, "a.node0", [self.fc("ext_used_gas")]),
            (a, "test1.node0", [self.fc("ext_random_seed"), self.fc("ext_block_timestamp"), self.fc("ext_storage_usage")]),
            (a, "test3.node0", [self.fc("do_ripemd")]),
            (a, "a.node0", [self.fc("ext_chain_id")]),
        ])
        self.round("calls-failing", [
            (a, "a.node0", [self.fc("panic_with_message")]),
            (a, "test1.node0", [self.fc("abort_with_zero")]),
            (a, "test2.node0", [self.fc("sanity_check_panic")]),
            (a, "test3.node0", [self.fc("loop_forever", gas=30 * TGAS)]),
            (a, "a.node0", [self.fc("no_such_method")]),
            (a, "test1.node0", [self.fc("sum_with_input", b"short")]),
            (a, "ft.node0", [self.fc("no_such_method", deposit=3 * NEAR)]),     # failing call with a deposit: refund
            (a, "est.node0", [self.fc("panic_after_logging")]),
        ])
        self.round("calls-ft", [
            (t["ft.node0"], "ft.node0", [self.fc("new_default_meta", json.dumps({
                "owner_id": "ft.node0", "total_supply": "1000000000"}).encode())]),
        ])
        self.round("calls-ft-2", [
            (a, "ft.node0", [self.fc("storage_deposit", json.dumps({"account_id": "a.node0"}).encode(), deposit=NEAR // 10)]),
            (t1, "ft.node0", [self.fc("storage_deposit", json.dumps({"account_id": "test1.node0"}).encode(), deposit=NEAR // 10)]),
        ])
        self.round("calls-ft-3", [
            (t["ft.node0"], "ft.node0", [self.fc("ft_transfer", json.dumps({
                "receiver_id": "a.node0", "amount": "1000"}).encode(), deposit=1)]),
        ])
        self.round("calls-ft-4", [
            (a, "ft.node0", [self.fc("ft_transfer_call", json.dumps({
                "receiver_id": "test1.node0", "amount": "10", "msg": "hello"}).encode(), gas=200 * TGAS, deposit=1)]),
            (a, "ft.node0", [self.fc("ft_balance_of", json.dumps({"account_id": "a.node0"}).encode())]),
        ])

    def contract(self, name: str) -> bytes:
        path = HERE / "target/bin/contracts" / f"{name}.wasm"
        return path.read_bytes()

    def promises(self):
        t = self.actors
        a, t1, t2, t3 = (t[n] for n in ["a.node0", "test1.node0", "test2.node0", "test3.node0"])
        def create(account, method, arguments, gas=20 * TGAS, amount="0"):
            return {"create": {"account_id": account, "method_name": method, "arguments": arguments,
                               "amount": amount, "gas": gas}}
        def then(index, account, method, arguments, gas=20 * TGAS, amount="0"):
            return {"then": {"promise_index": index, "account_id": account, "method_name": method,
                             "arguments": arguments, "amount": amount, "gas": gas}}
        def call(steps):
            return self.fc("call_promise", json.dumps(steps).encode(), gas=250 * TGAS)
        # cross-shard call chain with a callback reading the result, a failing callee, a deposit refund
        chain = [dict(create("test1.node0", "log_something", {}), id=0),
                 dict(then(0, "a.node0", "sanity_check_promise_results", {}), id=1),
                 dict(then(1, "test2.node0", "noop", {}), id=2, ret=True)]
        for step in chain:
            if step.pop("ret", False):
                step["return"] = True
        failing = [dict(create("test3.node0", "panic_with_message", {}, amount="1000000"), id=0),
                   dict(then(0, "test1.node0", "sanity_check_promise_results", {}), id=1)]
        fanout = [dict(create("test1.node0", "noop", {}), id=0), dict(create("test2.node0", "noop", {}), id=1),
                  dict(create("test3.node0", "log_something", {}), id=2),
                  dict(then(0, "a.node0", "noop", {}), id=3), dict(then(2, "a.node0", "sanity_check_promise_results", {}), id=4, **{"return": True})]
        nested = [dict(create("test2.node0", "call_promise", [
            dict(create("test3.node0", "log_something", {}), id=0, **{"return": True})], gas=120 * TGAS), id=0, **{"return": True})]
        batch = [{"batch_create": {"account_id": "dyn1.test1.node0"}, "id": 0},
                 {"action_create_account": {"promise_index": 0}, "id": 0},
                 {"action_transfer": {"promise_index": 0, "amount": str(3 * NEAR)}, "id": 0},
                 {"action_add_key_with_full_access": {"promise_index": 0, "public_key": base64.b64encode(
                     self.key("dyn1").pk).decode(), "nonce": 0}, "id": 0}]
        implicit = [{"batch_create": {"account_id": self.key("dyn-implicit").public.hex()}, "id": 0},
                    {"action_transfer": {"promise_index": 0, "amount": str(2 * NEAR)}, "id": 0}]
        self.round("promises", [
            (a, "a.node0", [call(chain)]),
            (t1, "test1.node0", [call(failing)]),
            (t2, "test2.node0", [call(fanout)]),
            (t3, "test3.node0", [call(nested)]),
        ])
        self.round("promises-actions", [
            (t1, "test1.node0", [nc.function_call("call_promise", json.dumps(batch).encode(), 150 * TGAS, 5 * NEAR)]),
            (t2, "test2.node0", [nc.function_call("call_promise", json.dumps(implicit).encode(), 100 * TGAS, 3 * NEAR)]),
        ])
        # gas attachment, unspent gas
        self.round("gas-weights", [
            (a, "test1.node0", [self.fc("attach_unspent_gas_but_use_all_gas", gas=100 * TGAS)]),
            (a, "test2.node0", [self.fc("attach_unspent_gas_but_burn_all_gas", gas=100 * TGAS)]),
        ])

    def yields(self):
        t = self.actors
        a = t["a.node0"]
        t2 = t["test2.node0"]
        # yield / resume: one in a single call, one resumed by a later transaction
        self.round("yield", [
            (a, "a.node0", [self.fc("call_yield_create_and_resume", b"payload-1", gas=200 * TGAS)]),
            (t2, "test2.node0", [self.fc("call_yield_create_return_promise", b"payload-2", gas=200 * TGAS)], {"nowait": True}),
        ])
        stored = self.net.view_state_prefix("test2.node0", (42).to_bytes(8, "little"))
        if stored:
            data_id = stored[0][1]
            self.round("yield-resume", [(a, "test2.node0", [self.fc("call_yield_resume", b"payload-2" + data_id, gas=100 * TGAS)])])
        # a yield that is never resumed: its callback runs with a timeout error 200 blocks later
        self.round("yield-timeout", [(t["test3.node0"], "test3.node0", [self.fc("call_yield_create_return_promise", b"never", gas=200 * TGAS)], {"nowait": True})])

    def keys(self):
        t = self.actors
        a = t["a.node0"]
        fc_key, full_key = self.key("a-fc"), self.key("a-full2")
        fc_actor = Actor("a.node0", fc_key)
        self.round("keys-add", [
            (a, "a.node0", [nc.add_key(fc_key.pk, nc.access_key_function_call("test1.node0", ["log_something", "write_key_value"], 5 * NEAR))]),
            (a, "a.node0", [nc.add_key(full_key.pk, nc.access_key_full())]),
        ])
        fc_actor.nonce = self.net.nonce("a.node0", fc_key)
        self.round("keys-use", [
            (fc_actor, "test1.node0", [self.fc("log_something")]),
            (fc_actor, "test1.node0", [self.fc("write_key_value", b"fc-key" + (5).to_bytes(8, "little"))]),
        ])
        self.round("keys-delete", [
            (a, "a.node0", [nc.delete_key(full_key.pk)]),
            (a, "a.node0", [nc.delete_key(fc_key.pk), nc.delete_key(self.key("never-added").pk)]),
        ])

    def staking(self):
        t = self.actors
        a, root = t["a.node0"], t["node0"]
        self.round("stake", [
            (a, "a.node0", [nc.stake(1000 * NEAR, a.key.pk)]),          # below the minimum stake: rejected
            (root, "node0", [nc.stake(50_000_000 * NEAR, root.key.pk)]),   # validator re-stakes its own amount
        ])
        self.round("stake-accepted", [(a, "a.node0", [nc.stake(2_000_000 * NEAR, a.key.pk)])])
        self.wait_blocks(30)
        self.round("unstake", [(a, "a.node0", [nc.stake(0, a.key.pk)])])

    def delegate(self):
        t = self.actors
        relay, user = t["relay.node0"], t["u1.node0"]
        height = self.net.height()
        def action(receiver, actions, nonce_offset):
            return nc.signed_delegate(user.key, nc.delegate_action(
                "u1.node0", receiver, actions, self.net.nonce("u1.node0", user.key) + nonce_offset, height + 200, user.key.pk))
        self.round("delegate", [
            (relay, "u1.node0", [nc.delegate(action("test1.node0", [self.fc("log_something")], 1))]),
        ])
        self.round("delegate-2", [
            (relay, "u1.node0", [nc.delegate(action("test2.node0", [nc.transfer(NEAR)], 1))]),
            (t["test1.node0"], "u1.node0", [nc.delegate(action("test3.node0", [nc.transfer(NEAR)], 2))]),
        ])
        self.round("delegate-3", [
            (relay, "u1.node0", [nc.delegate(action("test1.node0", [nc.transfer(NEAR)], 99))]),     # nonce far ahead of the key
            (t["test2.node0"], "u1.node0", [nc.delegate(nc.signed_delegate(user.key, nc.delegate_action(
                "u1.node0", "test1.node0", [nc.transfer(1)], 1, 1, user.key.pk)))]),                  # expired
        ])

    def global_contracts(self):
        t = self.actors
        a, t1 = t["a.node0"], t["test1.node0"]
        rs = self.contracts_by_name["rs"]
        code_hash = hashlib.sha256(rs).digest()
        for name in ["g1.node0", "g2.node0"]:
            self.actor(name)
        root = self.root
        def create(name, use):
            return (root, name, [nc.create_account(), nc.transfer(100 * NEAR),
                                 nc.add_key(self.actors[name].key.pk, nc.access_key_full()), use])
        self.round("global-deploy", [
            (a, "a.node0", [nc.deploy_global_contract(rs, by_account=False)]),
            (t1, "test1.node0", [nc.deploy_global_contract(rs, by_account=True)]),
        ])
        self.round("global-use", [
            create("g1.node0", nc.use_global_contract_by_hash(code_hash)),
            create("g2.node0", nc.use_global_contract_by_account("test1.node0")),
        ])
        self.round("global-call", [
            (self.actors["g1.node0"], "g1.node0", [self.fc("log_something")]),
            (self.actors["g2.node0"], "g2.node0", [self.fc("write_key_value", b"global" + (1).to_bytes(8, "little"))]),
            (a, "g1.node0", [self.fc("ext_account_id")]),
        ])

    def gas_keys(self):
        a = self.actors["a.node0"]
        gas_key = self.key("a-gas")
        try:
            self.round("gaskey-add", [(a, "a.node0", [nc.add_key(gas_key.pk, nc.access_key_gas_full(2))])])
            self.round("gaskey-fund", [(a, "a.node0", [nc.transfer_to_gas_key(gas_key.pk, 5 * NEAR)])])
            # strict-nonce transaction envelope signed by the account key
            self.round("strict-nonce", [(a, "test2.node0", [nc.transfer(NEAR)], {"strict": True})])
            self.round("gaskey-withdraw", [(a, "a.node0", [nc.withdraw_from_gas_key(gas_key.pk, NEAR)])])
        except Exception as error:   # keep the run going; the log records what happened
            self.log.append({"round": "gas-keys", "error": str(error)[:300]})

    def hostcalls(self):
        t = self.actors
        a = t["a.node0"]
        u1 = t["u1.node0"]
        self.round("hostcalls", [
            (a, "u1.node0", [self.fc("ecrecover_once")]),
            (a, "u1.node0", [self.fc("ed25519_once")]),
            (a, "u1.node0", [self.fc("p256_once")]),
            (a, "est.node0", [self.fc("keccak256_10b_10k", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("sha256_10b_10k", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("ed25519_verify_32b_500", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("alt_bn128_g1_sum_1_1k", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("alt_bn128_pairing_check_1_10", gas=300 * TGAS)]),
        ])
        self.round("hostcalls-bls", [
            (a, "est.node0", [self.fc("bls12381_p1_sum_0_100", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("bls12381_p2_sum_0_100", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("bls12381_g1_multiexp_0_100", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("bls12381_map_fp_to_g1_0_100", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("bls12381_pairing_0_100", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("bls12381_p1_decompress_0_100", gas=300 * TGAS)]),
            (a, "est.node0", [self.fc("ecrecover_10k", gas=300 * TGAS)]),      # exhausts its gas
        ])
        # every host function in one call, with a deployed contract that is later deleted
        sanity = json.dumps({"contract_code": base64.b64encode(wasmgen.noop_contract()).decode(),
                             "method_name": "noop", "method_args": "", "validator_id": "node0"}).encode()
        self.round("sanity-check", [(a, "test1.node0", [self.fc("sanity_check", sanity, gas=300 * TGAS, deposit=100 * NEAR)])])

    def delete_accounts(self):
        t = self.actors
        root = self.root
        for name in ["del1.node0", "del2.node0"]:
            self.actor(name)
        rs = self.contracts_by_name["rs"]
        def create(name):
            return (root, name, [nc.create_account(), nc.transfer(50 * NEAR),
                                 nc.add_key(self.actors[name].key.pk, nc.access_key_full())])
        self.round("delete-setup", [create("del1.node0"), create("del2.node0")])
        d2 = self.actors["del2.node0"]
        self.round("delete-fill", [(d2, "del2.node0", [nc.deploy_contract(rs)]),
                                   (self.actors["del1.node0"], "del1.node0", [nc.transfer(1)])])
        self.round("delete-fill-2", [(d2, "del2.node0", [self.fc("insert_strings", (0).to_bytes(8, "little") + (30).to_bytes(8, "little"))])])
        self.round("delete", [
            (self.actors["del1.node0"], "del1.node0", [nc.delete_account("test3.node0")]),
            (d2, "del2.node0", [nc.delete_account("a.node0")]),
        ])
        # the receiver of a transfer no longer exists
        self.round("delete-after", [(t["a.node0"], "del1.node0", [nc.transfer(NEAR)]),
                                    (t["a.node0"], "del2.node0", [self.fc("log_something")])])

    def burst(self):
        t = self.actors
        a = t["a.node0"]
        # many heavy calls in one block: pushes the shard past its gas limit, so receipts are delayed
        heavy = [(a, "test1.node0" if i % 2 else "test2.node0", [self.fc("sum_n", (30_000_000).to_bytes(8, "little"), gas=300 * TGAS)])
                 for i in range(14)]
        self.round("burst", heavy)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("topology", choices=sorted(localnet.TOPOLOGIES))
    parser.add_argument("--seed", type=int, default=1)
    parser.add_argument("--only", help="run only the named scenario after setup")
    arguments = parser.parse_args()
    workload = Workload(Net(arguments.topology), arguments.seed)
    first = workload.net.height()
    try:
        if arguments.only:
            workload.setup()
            getattr(workload, arguments.only)()
        else:
            workload.run_all()
    finally:
        last = workload.net.height()
        out = localnet.home(arguments.topology) / "workload.json"
        out.write_text(json.dumps({"topology": arguments.topology, "seed": arguments.seed,
                                   "firstHeight": first, "lastHeight": last, "transactions": workload.log}, indent=1))
        print(f"workload log: {out} ({len(workload.log)} transactions, heights {first}..{last})")


if __name__ == "__main__":
    main()
